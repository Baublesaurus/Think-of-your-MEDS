from dataclasses import dataclass
from math import log
from math import log2
from math import ceil
from math import comb

@dataclass
class param:
    digest_bytes: int # length of the Hash digests 
    pub_seed_bytes: int #length of the public key
    sec_seed_bytes: int #length of the secret key
    st_seed_bytes: int #length of the tree seed
    st_salt_bytes: int #length of the salt
    m: int # size of the first matrix
    n: int # size of the second matrix
    k: int # dimension of the subspace 
    q: int # the prime order of the field
    N: int # number of ephemeral keys in a round
    M: int # the number of keys
    t: int # the number of rounds
    w: int # the number of interrupted rounds

    name: str

    @property
    def pk_size(self):
        pub_seed_bytes = self.pub_seed_bytes
        M = self.M
        k = self.k 
        m = self.m
        n = self.n
        q = self.q

        q_bits = ceil(log2(q))

        return M * ceil(((k * (m*n - k) - (m*n - k + (m-1)*n-k)) * q_bits) / 8) + pub_seed_bytes
    
    @property
    def sk_size(self):
        sec_seed_bytes = self.sec_seed_bytes
        pub_seed_bytes = self.pub_seed_bytes
        M = self.M
        m = self.m
        n = self.n
        q = self.q

        q_bits = ceil(log2(q))

        def mat_bytes(i, j):
            return ceil(i*j*q_bits/8)

        return M*(mat_bytes(m,m) + mat_bytes(n,n)) + sec_seed_bytes + pub_seed_bytes

    @property
    def fiat_shamir(self):
        return log2(comb(self.t, self.w) * (self.M * self.N)**self.w)

    @property
    def master_seed_tree_cost(self):
        t = self.t
        w = self.w

        return (2**ceil(log2(w)) + w * (ceil(log2(t)) - ceil(log2(w)) - 1)) * self.st_seed_bytes

    @property 
    def round_seed_tree_cost(self):
        t = self.N # there are N nodes in the tree
        w = 1 # only one seed is removed, as there is a single interruption per round 
        return (2**ceil(log2(w)) + w * (ceil(log2(t)) - ceil(log2(w)) - 1)) * self.st_seed_bytes

    @property
    def avg_signature(self):
        N = self.N
        m = self.m
        n = self.n
        q = self.q

        q_bits = ceil(log2(q))

        def mat_bytes(i, j):
            return ceil(i*j*q_bits/8)
        
        hash_digest = self.digest_bytes
        salt = self.st_salt_bytes

        #                   Bottom page (13) of MPC-in-the-head
        avg_merkle_proof = ceil(hash_digest * log2(N-1) / 8)
        #                   One combined action            + one hash digest
        ephemeral_case = (mat_bytes(m,m) + mat_bytes(n,n)) + hash_digest
        #                   the action to before the interruption + one for every transition after + the average merkle proof
        interrupted_case = (1 + self.N/2) * (mat_bytes(m,m) + mat_bytes(n,n)) + avg_merkle_proof

        return hash_digest + salt + (self.t - self.w) * ephemeral_case + self.w *interrupted_case  

    @property
    def avg_seeded_signature(self):
        N = self.N
        m = self.m
        n = self.n
        q = self.q

        q_bits = ceil(log2(q))

        def mat_bytes(i, j):
            return ceil(i*j*q_bits/8)
        
        hash_digest = self.digest_bytes
        salt = self.st_salt_bytes

        #                   Bottom page (13) of MPC-in-the-head
        avg_merkle_proof = ceil(hash_digest * log2(N-1) / 8)
        #                   one hash digest = merkle root 
        ephemeral_case = hash_digest
        #                   The seed tree for every action except of the interruption + the interruption action + the average merkle proof
        interrupted_case = self.round_seed_tree_cost + (mat_bytes(m,m) + mat_bytes(n,n)) + avg_merkle_proof 

        return hash_digest + salt + (self.t - self.w) * ephemeral_case + self.w * interrupted_case  + self.master_seed_tree_cost
         
toy = param(
          digest_bytes = 256 >> 3,
          pub_seed_bytes = 256 >> 3,
          sec_seed_bytes = 256 >> 3,
          st_seed_bytes = 128 >> 3,
          st_salt_bytes = 256 >> 3,
          m = 10,
          n = 10,
          k = 10,
          q = 8191,
          N = 8,
          M = 1,
          t = 1,
          w = 1,
          name = "toy") 

example = param(
          digest_bytes = 256 >> 3,
          pub_seed_bytes = 256 >> 3,
          sec_seed_bytes = 256 >> 3,
          st_seed_bytes = 128 >> 3,
          st_salt_bytes = 256 >> 3,
          m = 13,
          n = 13,
          k = 13,
          q = 8191,
          N = 17,
          M = 8,
          t = 16,
          w = 11,
          name = "A little bigger toy")

hardexample = param(
          digest_bytes = 256 >> 3,
          pub_seed_bytes = 256 >> 3,
          sec_seed_bytes = 256 >> 3,
          st_seed_bytes = 128 >> 3,
          st_salt_bytes = 256 >> 3,
          m = 14,
          n = 14,
          k = 14,
          q = 4093,
          N = 3,
          M = 4,
          t = 39,
          w = 27,
          name = "one of mine")

seededexample = param(
          digest_bytes = 256 >> 3,
          pub_seed_bytes = 256 >> 3,
          sec_seed_bytes = 256 >> 3,
          st_seed_bytes = 128 >> 3,
          st_salt_bytes = 256 >> 3,
          m = 14,
          n = 14,
          k = 14,
          q = 4093,
          N = 513,
          M = 1,
          t = 36,
          w = 11,
          name = "one of mine") 

def lvl1(N, M, t, w):
    return param(
          digest_bytes = 256 >> 3,
          pub_seed_bytes = 256 >> 3,
          sec_seed_bytes = 256 >> 3,
          st_seed_bytes = 128 >> 3,
          st_salt_bytes = 256 >> 3,
          m = 14,
          n = 14,
          k = 14,
          q = 4093,
          N = N,
          M = M,
          t = t,
          w = w,
          name = "one of mine")
def lvl3(N, M, t, w):
    return param(
          digest_bytes = 256 >> 3,
          pub_seed_bytes = 256 >> 3,
          sec_seed_bytes = 256 >> 3,
          st_seed_bytes = 128 >> 3,
          st_salt_bytes = 256 >> 3,
          m = 22,
          n = 22,
          k = 22,
          q = 4093,
          N = N,
          M = M,
          t = t,
          w = w,
          name = "one of mine")
def lvl5(N, M, t, w):
    return param(
          digest_bytes = 256 >> 3,
          pub_seed_bytes = 256 >> 3,
          sec_seed_bytes = 256 >> 3,
          st_seed_bytes = 128 >> 3,
          st_salt_bytes = 256 >> 3,
          m = 30,
          n = 30,
          k = 30,
          q = 2039,
          N = N,
          M = M,
          t = t,
          w = w,
          name = "one of mine")

seeded_options = [
    lvl1(5, 1, 218, 18),
    lvl1(257, 3, 43, 11),
    lvl1(513, 1, 36, 11),
    lvl1(513, 4, 39, 10),
    lvl3(513, 1, 97, 15),
    lvl3(513, 35, 55, 11),
    lvl5(5, 3, 686, 29),
    lvl5(513, 1, 185, 19),
    lvl5(513, 14, 130, 15),
    lvl5(3, 1, 1283, 31)
    ]

unseeded_options = [
    lvl1(3, 4, 39, 27),
    lvl3(3, 4, 58, 40),
    lvl3(3, 34, 30, 27),
    lvl5(3, 12, 109, 35),
    lvl5(3, 4, 76, 54),
    lvl5(3, 14, 52, 41)
    ]
