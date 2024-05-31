# imports
from sage.all_cmdline import *   # import sage librarys
from Crypto.Hash import SHAKE256
from math import log
from math import ceil

import bitstream
import merkleTree
from seedtree import SeedTree 

# Directly taken from the MEDS reference sage implementation 
# https://www.meds-pqc.org/
GFq_cache = {}

def get_cached(GFq):
  global GFq_cache

  if GFq not in GFq_cache:
    numbytes = ceil(log(GFq.base().order(),2)/8)
    GF_BITS = ceil(log(GFq.base().order(),2))
    mask = (1 << ceil(log(GFq.base().order(),2))) - 1
    q = GFq.base().order()

    GFq_cache[GFq] = numbytes, mask, q, GF_BITS

  return GFq_cache[GFq]

def Compress(M):
  GFq = M[0,0].base_ring()
  _, _, _, GF_BITS = get_cached(GFq)

  bs = bitstream.BitStream()

  for v in [j for v in M.rows() for j in v]:
    bs.write(int(v), GF_BITS)

  return bs.data

def Decompress(b, GFq, r, c):
  _, _, _, GF_BITS = get_cached(GFq)

  bs = bitstream.BitStream(b)

  data = [GFq(bs.read(GF_BITS)) for _ in range(r*c)]
  
  return matrix(GFq, r, c, data)

def CompressG(M, k, m, n):
  GFq = M[0,0].base_ring()
  _, _, _, GF_BITS = get_cached(GFq)

  bs = bitstream.BitStream()

  for i in range(n):
    # of matrix 1 in M
    #writes the entire last row of the m*n matrix
    bs.write(int(M[1,m*n-n+i]), GF_BITS)

  for i in range(2, k):
    for j in range(k, m*n):
      bs.write(int(M[i, j]), GF_BITS)

  return bs.data

def DecompressG(b, GFq, k, m, n):
  _, _, _, GF_BITS = get_cached(GFq)

  bs = bitstream.BitStream(b)

  I_k = matrix.identity(ring=GFq, n=k)

  G = I_k.augment(matrix(GFq, k, m*n-k))

  for i in range(1, m):
    G[0, i*(n+1)] = 1

  for i in range(1, m-1):
    G[1, i*(n+1)+1] = 1

  for i in range(n):
    G[1,m*n-n+i] = GFq(bs.read(GF_BITS))
  
  for i in range(2,k):
    for j in range(k, m*n):
      G[i, j] = GFq(bs.read(GF_BITS))

  return G

def expand_field_elements(seed, num, GFq):
  numbytes, mask, q, _ = get_cached(GFq)

  if type(seed) == SHAKE256.SHAKE256_XOF:
    shake = seed
  else:
    shake = SHAKE256.new()
    shake.update(seed)

  ret = []

  for _ in range(num):
    while True:
      val = 0
  
      for i in range(numbytes):
        val += ord(shake.read(1)) << (i*8)
  
      val = val & mask
  
      if val < q:
        ret.append(GFq(val))
        break

  return ret

def expand_systematic_matrix(seed, GFq, k, m, n):
  I_k = matrix.identity(ring=GFq, n=k)

  return I_k.augment(matrix(GFq, k, m*n-k, expand_field_elements(seed, k*(m*n-k), GFq)))

def XOF(seed, length):
  shake = SHAKE256.new()
  shake.update(seed)

  if not isinstance(length, list):
    return shake.read(length)

  data = shake.read(sum(length))

  return tuple(data[sum(length[:i]):sum(length[:i+1])] for i in range(len(length)))

def expand_invertible_matrix(seed, GFq, n):
  shake = SHAKE256.new()
  shake.update(seed)

  while True:
    M = matrix(GFq, n, n, expand_field_elements(shake, n*n, GFq))

    if M.is_invertible():
      return M

def expand_matrix(seed, GFq, n):
  shake = SHAKE256.new()
  shake.update(seed)

  return matrix(GFq, n, n, expand_field_elements(shake, n*n, GFq))

def H(params):
  def hash(m):
    shake = SHAKE256.new()
    shake.update(m)
  
    return shake.read(params.digest_bytes)

  return hash

def ParseHash(digest, t, s, w):
  #logging.debug(f"digest:\n%s", [int(v) for v in digest])
  #logging.debug("digest_len:\n%i", len(digest))

  shake = SHAKE256.new()

  shake.update(digest)

  h = [0] * t

  num = 0

  while num < w:
    pos = 0

    for i in range(ceil(log(t,2)/8)):
      pos += ord(shake.read(1)) << (i*8)

    pos &= (1 << ceil(log(t,2))) - 1


    if pos >= t:
      continue

    if h[pos] > 0:
      continue  

    #logging.debug(f"pos: {pos}")

    val = 0

    while val < 1 or val > s-1:
      val = 0

      for i in range(ceil(log(s,2)/8)):
        val += ord(shake.read(1)) << (i*8)
    
      val &= (1 << ceil(log(s,2))) - 1

    h[pos] = val

    #logging.debug(f"p: {pos}  v: {val}")

    num += 1

  return h

def solve_symb(P0prime, Amm):
  m = P0prime[0].nrows()
  n = P0prime[0].ncols()

  GFq = Amm.base_ring()

  Pj = [None] * 2

  Pj[0] = matrix(GFq, m, n, [[GFq(1) if i==j else GFq(0) for i in range(n)] for j in range(m)])
  Pj[1] = matrix(GFq, m, n, [[GFq(1) if i==j else GFq(0) for i in range(n)] for j in range(1,m)] + [[GFq(0)]*n])

  R = PolynomialRing(GFq, m*m + n*n,
     names = ','.join([f"b{i}_{j}" for i in range(n) for j in range(n)]) + "," \
           + ','.join([f"a{i}_{j}" for i in range(m) for j in range(m)]))

  A     = matrix(R, m, var(','.join([f"a{i}_{j}" for i in range(m) for j in range(m)])))
  B_inv = matrix(R, n, var(','.join([f"b{i}_{j}" for i in range(n) for j in range(n)])))

  A[m-1,m-1] = Amm

  eqs1 = Pj[0] * B_inv - A*P0prime[0]
  eqs2 = Pj[1] * B_inv - A*P0prime[1]

  eqs = eqs1.coefficients() + eqs2.coefficients()[:-1]

  rsys = matrix(GFq, [[eq.coefficient(v) for v in R.gens()[:-1]] + [-eq.constant_coefficient()] for eq in eqs])

  rsys_rref = rsys.rref()

  if not all([rsys_rref[i][i] == 1 for i in range(rsys_rref.nrows())]):
    #logging.debug("no sol")
    return None, None

  sol = rsys_rref.columns()[-1].list()

  A = matrix(GFq, m, sol[n*n:] + [Amm])
  B_inv = matrix(GFq, m, sol[:n*n])

  #logging.debug(f"A:\n%s", A)
  #logging.debug(f"B_inv:\n%s", B_inv)

  return A, B_inv

def pi(A, B, G):
  m = A.nrows()
  n = B.nrows()
  k = G.nrows()

  GFq = A[0,0].base_ring()

  G = [matrix(GFq, m, n, row) for row in G.rows()]

  AGB = [A*v*B for v in G]

  return matrix(GFq, k, m*n, [AGB[i][j,g] for i in range(k) for j in range(m) for g in range(n)])

def SF(M):
  M = M.echelon_form()

  # check if we got systematic form
  if sum([M[j,j] for j in range(M.nrows())]) != M.nrows():
    return None

  return M

# Needed for the seed tree
def G(params, salt):
  def hash_pair(value, addr):
    shake = SHAKE256.new()
    shake.update(salt + value + addr.to_bytes(4, "little"))

    return shake.read(params.st_seed_bytes), shake.read(params.st_seed_bytes)

  return hash_pair

def SeedTreeToPath(h, t, root, salt, param):
  seeds = SeedTree(t, root, G(param, salt))

  for i, h_i in enumerate(h):
    if h_i < param.N:
      seeds.delete(i)

  ret = b"".join(seeds.path())

  if t == param.t: 
    cost = param.master_seed_tree_cost
  else:
     cost = param.round_seed_tree_cost

  return ret + bytes([0]) * (cost - len(ret))

def PathToSeedTree(h, t, path, salt, param):
  # prepare tree structure
  seeds = SeedTree(t)

  for i, v in enumerate(h):
    if v < param.N:
      seeds.delete(i)

  parsed = []

  for _ in range(len(seeds.path())):
    parsed.append(path[:param.st_seed_bytes])
    path = path[param.st_seed_bytes:]

  # apply patch once tree structure is set up
  seeds.patch(parsed, G(param, salt))

  return seeds

# My own code 
def commit_prover(param, salt, codes, msg):
        #params 
        k = param.k
        t = param.t
        N = param.N 

        round_commitments = bytes()

        Trees = []
        for u in range(0,t):
            #round commitments 
            leafs = []
            Gtilde_u = codes[u]
            #node commitments    
            for i in range(1, len(Gtilde_u) - 1):
              G_i = Gtilde_u[i]
              compressed = Compress(G_i[:,k:])
              leafs.append(H(param)(compressed + salt + (u).to_bytes(2) + (i).to_bytes(2)))
            # build a Merkle tree out of the node commitments 
            Trees.append(merkleTree.MerkleTree(param, leafs))
            # set the round commitment to the root of the tree
            round_commitments += Trees[u].root
        
        for u in range(0,t):
          #commit to the last node of each round  
          Gtilde_u = codes[u]
          round_commitments += H(param)(Compress(Gtilde_u[-1][:,k:]) + salt + (u).to_bytes(2) + (N).to_bytes(2))

        # Hash all the roots together into the c
        return H(param)(round_commitments + msg), Trees 

def commit_verifier(param, salt, merkleProofs, recomputed_nodes, msg, interruption ):
        #params 
        k = param.k
        t = param.t
        N = param.N

        round_commitments = bytes()
        f_rp = 0

        for u in range(0,t):
            if interruption[u] < N: 
              assert(len(recomputed_nodes[u]) > 1)
              leafs = []
              Gtilde_u = recomputed_nodes[u]
              j = interruption[u]

              # For each recomputed node except the N'th (= last)
              for i in range(len(Gtilde_u) - 1):
                G_i = Gtilde_u[i]
                compressed = Compress(G_i[:,k:])
                leafs.append(H(param)(compressed + salt + (u).to_bytes(2) + (j).to_bytes(2)))
                j += 1
              
              round_root, f_rp = recompute_root(param, leafs, merkleProofs, f_rp)
              round_commitments += round_root
            else: 
               assert(len(recomputed_nodes[u]) == 1)
               round_root = merkleProofs[f_rp : f_rp + param.digest_bytes]
               f_rp = f_rp + param.digest_bytes
               round_commitments += round_root

        #assert that the entire signature has been processed
        assert(f_rp == len(merkleProofs))

        for u in range(t):
          #commit to the last node of each round  
          Gtilde_u = recomputed_nodes[u]
          round_commitments += H(param)(Compress(Gtilde_u[-1][:,k:]) + salt + (u).to_bytes(2) + (N).to_bytes(2))

        return H(param)(round_commitments +msg)

def challenge(param, commitment):
    t = param.t # the amount of rounds
    N = param.N # the number of keys in a round
    M = param.M # the number of key-pairs 
    w = param.w # the amount of non-zero interruptions. 
    
    #   The 0 interruptions should be set to N, since that corresponds to "no interruption" in this scheme
    interruption = ParseHash(commitment+b'interruption', t, N, w)
    # so fixing all that:
    for u in range(t):
        if interruption[u] == 0: 
            interruption[u] = N

    # the k-1 and +1 are needed so that the output is in {0, M-1} instead of {1,M-1}
    key_position = ParseHash(commitment+b'key_position', t, M+1, t)
    key_position = [k-1 for k in key_position] 
    
    return interruption, key_position

def reconstruct_sk(GFq, param, secret_key):
  k = param.k
  m = param.m
  n = param.n
  M = param.M
  q = param.q

  # this parameter is used as a pointer to parse the secret_key
  f_sk = param.sec_seed_bytes

  sigma_G0 = secret_key[f_sk : f_sk + param.pub_seed_bytes]
  G_0 = expand_systematic_matrix(sigma_G0, GFq, k, m, n)
  
  # reconstruct private keys
  GF_BITS = ceil(log(q, Integer(2)))
  f_sk += param.pub_seed_bytes
  
  # length of the B matrices
  l_Fq_nn = ceil((GF_BITS * n * n) / Integer(8) )
  # length of the A matrices
  l_Fq_mm = ceil((GF_BITS * m * m) / Integer(8) )

  A_inv = [None]*M
  B_inv = [None]*M

  for i in range(M):
      A_inv[i] = Decompress(secret_key[f_sk : f_sk + l_Fq_mm], GFq, m, m)
      f_sk += l_Fq_mm

  for i in range(M):
      B_inv[i] = Decompress(secret_key[f_sk : f_sk + l_Fq_nn], GFq, n, n)
      f_sk += l_Fq_nn
  
  return G_0, A_inv, B_inv

def reconstruct_rsp(GFq, param, response, interruption, f_rp, salt):
  n = param.n
  m = param.m 
  N = param.N 
  q = param.q
  t = param.t

  # length of an element in the field in bits
  GF_BITS = ceil(log(q, Integer(2) ))
  # length of the B matrices
  l_Fq_nn = ceil((GF_BITS * n * n) / Integer(8) )
  # length of the A matrices
  l_Fq_mm = ceil((GF_BITS * m * m) / Integer(8) )

  A = [0 for _ in range(t)]
  B = [0 for _ in range(t)]

  for u in range(t):
      if interruption[u] != N:
          A[u] = Decompress(response[f_rp : f_rp + l_Fq_mm], GFq, m, m)
          f_rp += l_Fq_mm

  for u in range(t):
      if interruption[u] != N:
        B[u] = Decompress(response[f_rp : f_rp + l_Fq_nn], GFq, n, n)
        f_rp += l_Fq_nn

  master_seed_path = response[f_rp : f_rp + param.master_seed_tree_cost]
  master_seed_tree = PathToSeedTree(interruption, t, master_seed_path, salt, param)
  f_rp += param.master_seed_tree_cost

  round_seed_trees = [0 for _ in range (t)]
  for u in range(t):
     if interruption[u] != N: 
        seed_tree_path = response[f_rp : f_rp + param.round_seed_tree_cost]
        f_rp += param.round_seed_tree_cost

        single_interruption = [0 if j == interruption[u] else N for j in range(N)]
        round_seed_trees[u] = PathToSeedTree(single_interruption, N, seed_tree_path, salt, param)

  return A, B, master_seed_tree, round_seed_trees, f_rp

def reconstruct_pk(GFq, param, public_key):

  k = param.k
  m = param.m
  n = param.n
  q = param.q
  M = param.M

  GF_BITS = ceil(log(q, Integer(2) ))

  sigma_G0 = public_key[: param.pub_seed_bytes]
  G_0 = expand_systematic_matrix(sigma_G0, GFq, k, m, n)

  Gprime = [None] * M 

  #pointer
  f_pk = param.pub_seed_bytes 
  #length of the codes
  l_Gi = ceil(((k-Integer(2) )*(m*n-k) + n) * GF_BITS / Integer(8) )

  for j in range(M):
      Gprime[j] = DecompressG(public_key[f_pk : f_pk + l_Gi], GFq, k, m, n)
      f_pk += l_Gi
  
  #print(f"check length digest:{len(public_key) == param.pk_size}")

  return G_0, Gprime

def recompute_root(param, recomputed_leafs, interruption_proof, f_rp):    
    n = param.N - 1
    old_layer = recomputed_leafs
    height = ceil(log(n, 2))
    
    assert(len(recomputed_leafs) > 0)
    assert( (n & (n-1) == 0) and n != 0 )

    for k in range(height): 
        new_layer = []
        i = 0
        if len(old_layer) % 2 == 1:
            proof_node = interruption_proof[f_rp : f_rp + param.digest_bytes]
            f_rp += param.digest_bytes

            new_layer.append(H(param)(proof_node + old_layer[0] ))
            i += 1 

        while i < len(old_layer):
            new_layer.append(H(param)(old_layer[i] + old_layer[i+1]))
            i += 2

        old_layer = new_layer

    return new_layer[0], f_rp
