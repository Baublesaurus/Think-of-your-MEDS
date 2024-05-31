#!/usr/bin/env sage

# Imports
import secrets # python module, for secure random number generation. https://docs.python.org/3/library/secrets.html
import time # python module, for timing execution 

import os.path as path # to import custom modules
#custom modules
import params # my own script, to define parameter sets
import util_seeded as util # usefull functions like H(),XOF() and SF(). Partially by me, partially from MEDS
import merkleTree # implements the logic of Merkle Trees. Made by me 
import seedtree # implements the logic of Seed Trees. from the MEDS sage reference implementation

class MPCwithMCE_seeded:
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

                # matrix T in GL(q) with dimension k is used in Lemma 1 from MEDS
                T = util.expand_invertible_matrix(sigma_T, GFq, k)

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
        rho, salt = util.XOF(delta, [param.st_seed_bytes, param.st_salt_bytes])

        master_seed_tree = seedtree.SeedTree(t, rho, util.G(self.params, salt))
        
        for u in range(0,t):
            #set Gi[0] = G_0 
            Gtilde[u][0] = G_0
            sigma = master_seed_tree[u]
            round_seed_tree = seedtree.SeedTree(N, sigma, util.G(self.params, salt))
            
            for i in range(1,N+1): # so including both 1 and N
                # generate an Ai and Bi s.t. SF(pi(A, B, Gi-1)) results in a systematic form
                Gi = None
                Ai = None
                Bi = None
                seed = round_seed_tree[i-1]
                while Gi == None: 
                    sigma_prime = salt + seed + i.to_bytes(4, "little")
                    sigmaA, sigmaB, seed = util.XOF(sigma_prime, [param.pub_seed_bytes, param.pub_seed_bytes, param.st_seed_bytes])
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
        round_seed_paths = bytes()

        for u in range(0,t):
            # for all uninterrupted rounds, the merkle root is sent. 
            # in MPC-in-the-head these are combined into a master_merkle_tree
            if interruption[u] == N: 
                # add the root of the merkle tree
                merkle_proofs += round_merkle_trees[u].root 

            # for all interrupted rounds
            else: 
                i = interruption[u]

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

                single_interruption = [0 if j == i else N for j in range(N)]
                round_seed_paths += util.SeedTreeToPath(single_interruption, N, master_seed_tree[u], salt, param)

                # The minus 1 is needed, because the MerkleTree class starts counting at 0, instead of 1
                merkle_proofs += round_merkle_trees[u].proof(interruption[u] - 1) 

        #The interrupted seed_tree
        master_seed_path = util.SeedTreeToPath(interruption, t, rho, salt, param)

        return salt + commitment + A_response + B_response + master_seed_path + round_seed_paths + merkle_proofs 
    
    def verify(self, public_key, response, msg):
        #params
        param = self.params
        m = param.m
        n = param.n
        k = param.k
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
        A, B, master_seed_tree, round_seed_trees, f_rp = util.reconstruct_rsp(GFq, param, response, interruption, f_rp, salt)

        # reconstruct the public key     
        G_0, Gprime = util.reconstruct_pk(GFq, param, public_key)

        Gtilde = [[None for _ in range(N+1)] for _ in range(t)]
        recomputed_nodes = []
        for u in range(0,t):
            Gtilde[u][0] = G_0
            if interruption[u] < N: 
                # recompute everything, except the node after the interruption. 
                for i in range(1, N+1):
                    if i == interruption[u]+1:
                        Gtilde[u][i] = util.SF(util.pi(A[u], B[u], Gprime[key_position[u]]))
                    else:
                        Gi = None
                        Ai = None
                        Bi = None
                        seed = round_seed_trees[u][i-1]
                        while Gi == None: 
                            sigma_prime = salt + seed + i.to_bytes(4, "little")
                            sigmaA, sigmaB, seed = util.XOF(sigma_prime, [param.pub_seed_bytes, param.pub_seed_bytes, param.st_seed_bytes])
                            Ai = util.expand_matrix(sigmaA, GFq, m)
                            Bi = util.expand_matrix(sigmaB, GFq, n)

                            Gi = util.pi(Ai, Bi, Gtilde[u][i-1])
                            Gi = util.SF(Gi)
                        Gtilde[u][i] = Gi
                recomputed_nodes.append(Gtilde[u][interruption[u]:])            
            else: 
                # recompute everything
                sigma = master_seed_tree[u]
                round_seed_tree = seedtree.SeedTree(N, sigma, util.G(self.params, salt))
                
                for i in range(1,N+1): # so including both 1 and N
                    # generate an Ai and Bi s.t. SF(pi(A, B, Gi-1)) results in a systematic form
                    Gi = None
                    Ai = None
                    Bi = None
                    seed = round_seed_tree[i-1]
                    while Gi == None: 
                        sigma_prime = salt + seed + i.to_bytes(4, "little")
                        sigmaA, sigmaB, seed = util.XOF(sigma_prime, [param.pub_seed_bytes, param.pub_seed_bytes, param.st_seed_bytes])
                        Ai = util.expand_matrix(sigmaA, GFq, m)
                        Bi = util.expand_matrix(sigmaB, GFq, n)

                        Gi = util.pi(Ai, Bi, Gtilde[u][i-1])
                        Gi = util.SF(Gi)
                    Gtilde[u][i] = Gi
                recomputed_nodes.append([Gtilde[u][-1]])
                
        c = util.commit_verifier(param, salt, response[f_rp:], recomputed_nodes, msg, interruption)

        #Verify
        return commitment ==  c

if __name__ == "__main__":    
    # Toy example 
    toy_example = MPCwithMCE_seeded(params.seeded_options[0])

    msg = b"A wonderfull test message"

    #GFq = GF(toy_example.params.q)

    print("parameter set: " + toy_example.params.name)
    print(f"Fiat-Shamir: {toy_example.params.fiat_shamir} (log 2)")
    print(f"Secret key: {toy_example.params.sk_size} bytes")
    print(f"Public key: {toy_example.params.pk_size} bytes")
    print(f"Average Signature size: {toy_example.params.avg_seeded_signature} bytes")

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
