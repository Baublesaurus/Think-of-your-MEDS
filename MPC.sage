#!/usr/bin/env sage

# Imports
import secrets # python module, for secure random number generation. https://docs.python.org/3/library/secrets.html
import time # python module, for timing execution 

import os.path as path # to import custom modules
#custom modules
import params # my own script, to define parameter sets
import util # usefull functions like H(),XOF() and SF()
import merkleTree # implements the logic of Merkle Trees. 

class MPCwithMCE:
    def __init__(self, params, rng=secrets.token_bytes):
        self.params = params
        self.randombytes = rng

    def key_generation(self):
        #parameters
        param = self.params 
        k = param.k
        m = param.m
        n = param.n
        q = param.q
        M = param.M

        #field
        GFq = GF(q)

        #secret keys
        A = [None] * M 
        B = [None] * M

        #public keys
        Gprime = [None] * M 

        #Bytes of randomness needed for the security goal
        #? delta is some form of master seed. other seeds are generated from delta in a fixed way. 
        delta = self.randombytes(param.sec_seed_bytes)
        secret_key = delta

        #Bytes of randomness for the public key, random bytes for the secret key 
        sigma_G0, sigma = util.XOF(delta, [param.pub_seed_bytes, param.sec_seed_bytes])

        #Initial generator matrix
        G = util.SF(util.expand_systematic_matrix(sigma_G0, GFq, k, m, n))
        sigma, sigma_T = util.XOF(sigma, [param.sec_seed_bytes]*2)
        # matrix T in GL(q) with dimension k is used in Lemma 1 from MEDS
        T = util.expand_invertible_matrix(sigma_T, GFq, k)
        for j in range(M): 
            while True: #repeat until G' has systematic form 
                # sigma_alpha: to generate Amm
                # sigma_T: to generate T 
                sigma_alpha, sigma = util.XOF(sigma, [param.sec_seed_bytes]*2)

                #generate an element in the field. Used to fix an element in the A matrix. 
                Amm = util.expand_field_elements(sigma_alpha, 1, GFq)[0]

                Gprime[j] = T * G

                #Try to generate an A and B from these 
                #Gprime.rows() generates a list of Tuples of all the rows. 
                # [matrix(GFq, m, n, Gprime.rows()[i]) for i in range(2)] constructs a matrix out of the first to rows of Gprime 
                # note that these "rows" are the first two m x n matrices in Gprime, as Gprime is a k x m x n matrix 
                A[j], B[j] = util.solve_symb([matrix(GFq, m, n, Gprime[j].rows()[i]) for i in range(2)], Amm)

                if A[j] == None and B[j] == None:
                    #if no unique solution exists, try again
                    continue
                elif not A[j].is_invertible():
                    continue
                elif not B[j].is_invertible():
                    continue
            
                B[j] = B[j].inverse()
                Gprime[j] = util.SF( util.pi(A[j], B[j], G) )
                if Gprime[j] != None: break

        public_key = sigma_G0
        secret_key += sigma_G0

        for j in range(M):
            public_key += util.CompressG(Gprime[j], k, m, n)
            secret_key += util.Compress(A[j].inverse())

        for j in range(M):
            secret_key += util.Compress(B[j].inverse())

        return public_key, secret_key

    def sign(self, secret_key, msg):
        #parameters
        param = self.params 
        k = param.k
        m = param.m
        n = param.n
        q = param.q
        N = param.N
        t = param.t

        #field
        GFq = GF(q)

        # reconstruct the secret key  
        G_0, A_inv, B_inv = util.reconstruct_sk(GFq, param, secret_key)
                
        #ephemeral keys 
        #note that Ai[0] and Bi[0] stay None, as Gi[0] = G_0
        #they are initialized to help prevent off by one errors in coding
        Atilde = [[None for _ in range(N+1)] for _ in range(t)] 
        Btilde = [[None for _ in range(N+1)] for _ in range(t)] 
        Gtilde = [[None for _ in range(N+1)] for _ in range(t)]

        delta = self.randombytes(param.sec_seed_bytes)
        sigma, salt = util.XOF(delta, [param.st_seed_bytes, param.st_salt_bytes])

        for u in range(0,t):
            #set Gi[0] = G_0 
            Gtilde[u][0] = G_0

            for i in range(1,N+1): # so including both 1 and N
                # generate an Ai and Bi s.t. SF(pi(A, B, Gi-1)) results in a systematic form
                Gi = None
                Ai = None
                Bi = None 

                while Gi == None: 
                    sigma_prime = salt + sigma + i.to_bytes(4, "little")
                    sigmaA, sigmaB, sigma = util.XOF(sigma_prime, [param.pub_seed_bytes, param.pub_seed_bytes, param.st_seed_bytes])
                    Ai = util.expand_matrix(sigmaA, GFq, m)
                    Bi = util.expand_matrix(sigmaB, GFq, n)

                    Gi = util.pi(Ai, Bi, Gtilde[u][i-1])
                    Gi = util.SF(Gi)

                Atilde[u][i] = Ai
                Btilde[u][i] = Bi
                Gtilde[u][i] = Gi

        commitment, round_merkle_trees = util.commit_prover(param, salt, Gtilde, msg)

        #interruption from commitment
        interruption, key_position = util.challenge(param, commitment)

        #build response 
        A_response = bytes()
        B_response = bytes()
        merkle_proofs = bytes()

        for u in range(0,t):
            # for all uninterrupted rounds, the product of all ephemeral keys is sent.
            if interruption[u] == N: 
                A_round_response = Atilde[u][-1]
                B_round_response = Btilde[u][1]
                for i in reversed(range(1, N)):
                    A_round_response = A_round_response * Atilde[u][i]
                for i in range(2,N+1):
                    B_round_response = B_round_response * Btilde[u][i]

                A_response += util.Compress(A_round_response)
                B_response += util.Compress(B_round_response)
                # add the root of the merkle tree as root 
                merkle_proofs += round_merkle_trees[u].root 

            # for all interrupted rounds
            else: 
                i = interruption[u]

                # The combined group action to get to the node of the interruption: 
                A_round_response = Atilde[u][i]
                B_round_response = Btilde[u][1]

                for j in reversed(range(1, i)):
                    A_round_response = A_round_response * Atilde[u][j]
                for j in range(2,i+1):
                    B_round_response = B_round_response * Btilde[u][j]

                A_response += util.Compress(A_round_response)
                B_response += util.Compress(B_round_response)

                # The combined group action to get to the node after the interruption
                A_proof = Atilde[u][i+1]
                for j in reversed(range(1, i+1)):
                    A_proof = A_proof * Atilde[u][j]
                A_proof = A_proof * A_inv[key_position[u]]

                B_proof = B_inv[key_position[u]]
                for j in range(1,i+2):
                    B_proof = B_proof * Btilde[u][j]

                A_response += util.Compress(A_proof)
                B_response += util.Compress(B_proof)

                # All later nodes
                for x in range(i+2, N+1):
                    A_response += util.Compress(Atilde[u][x])
                    B_response += util.Compress(Btilde[u][x]) 

                # For each round, compute the merkle proof
                    # The minus 1 is needed, because the MerkleTree class starts counting at 0, instead of 1
                merkle_proofs += round_merkle_trees[u].proof(interruption[u] - 1) 

        return salt + commitment + A_response + B_response + merkle_proofs
    
    def verify(self, public_key, response, msg):
        #params
        param = self.params
        N = param.N
        t = param.t
        q = param.q 

        GFq = GF(q)

        # reconstruct the response 
        # response pointer
        f_rp = 0

        salt = response[f_rp : f_rp + param.st_salt_bytes]
        f_rp += param.st_salt_bytes
        commitment = response[f_rp : f_rp + param.digest_bytes]
        f_rp += param.digest_bytes 

        # generate challenge from commitment
        interruption, key_position = util.challenge(param, commitment)
        # reconstruct the keys from the response
        A, B, f_rp = util.reconstruct_rsp(GFq, param, response, interruption, f_rp)

        # reconstruct the public key     
        G_0, Gprime = util.reconstruct_pk(GFq, param, public_key)

        recomputed_nodes = []
        for u in range(0,t):
            Gi_u = [G_0]

            if interruption[u] < N: 
                # the node of the interruption 
                Gi_u.append(util.SF(util.pi(A[u][0], B[u][0], Gi_u[-1])))                
                # the node after the interruption 
                Gi_u.append(util.SF(util.pi(A[u][1], B[u][1], Gprime[key_position[u]])))
                
                # all other nodes
                for i in range(2, len(A[u])):
                    Gi_u.append(util.SF(util.pi(A[u][i], B[u][i], Gi_u[-1])))
            else: 
                # only compute the last node 
                Gi_u.append(util.SF(util.pi(A[u][-1], B[u][-1], Gi_u[0])))
                
            recomputed_nodes.append(Gi_u[1:])
        
        c = util.commit_verifier(param, salt, response[f_rp:], recomputed_nodes, msg, interruption)

        #Verify
        return commitment ==  c

if __name__ == "__main__":    
    # Toy example 
    toy_example = MPCwithMCE(params.unseeded_options[0])

    msg = b"A wonderfull test message"

    #GFq = GF(toy_example.params.q)

    print("parameter set: " + toy_example.params.name)
    print(f"Fiat-Shamir: {toy_example.params.fiat_shamir} (log 2)")
    print(f"Secret key: {toy_example.params.sk_size} bytes")
    print(f"Public key: {toy_example.params.pk_size} bytes")
    print(f"Average Signature size: {toy_example.params.avg_signature} bytes")

    #print("=================Key generation==========")
    start_time = time.time()
    public_key, secret_key  = toy_example.key_generation()
    key_gen_time = time.time() - start_time
    print("Key Generation: {0:1.4f}".format(key_gen_time))
    
    #print("=================Signing=================")
    start_time = time.time()
    response = toy_example.sign(secret_key, msg)
    sign_time = time.time() - start_time
    print("Signing:   {0:1.4f}".format(sign_time))
    
    #print("=================Verifying===============")
    start_time = time.time()
    verify = toy_example.verify(public_key, response, msg)
    verify_time = time.time() - start_time
    print("Verification: {0:1.4f}".format(verify_time))

    print(f"Signature size: {len(response)} bytes")
    
    if verify :
        print(f'test: Accepted')
    else: 
        print(f'test: Rejected')
