#imports
import os.path as path # to import custom modules
from math import log2
from math import ceil
import util
import params

class MerkleTree: 
    def __init__(self, param, leafs):
        self.param = param
        self.height = ceil(log2(len(leafs)))
        self.tree = self.build_tree(leafs)
        self.root = self.tree[0][0] 

    def build_tree(self, leafs):
        n = len(leafs)
        height = self.height
        param = self.param

        #assert that the number of leafs is a power of 2.
        assert( (n & (n-1) == 0) and n != 0 )

        # the number of layers needed to get to a single root
        tree = [[]] * (height+1) 
        tree[height] = leafs

        for i in reversed(range(height)):
            # each level needs half as many nodes as the level below
            tree[i] = [[]] * ((int) (len(tree[i+1])/2))
            # for each of these nodes, combine the two leaves below it
            for j in range(len(tree[i])):
                tree[i][j] = util.H(param)(tree[i+1][2*j] + tree[i+1][2*j+1]) 
        
        return tree
    
    def proof(self, interruption): 
        # so we recompute node at interruption, and everything above. This should be a proof of all the nodes below. 
        height = self.height
        tree = self.tree

        proof = bytes()
        compute_from = interruption

        for i in reversed(range(1,height+1)):
            if (len(tree[i]) - compute_from) % 2 == 0: # case = even
                # so all nodes on this level can be compared pairwise
                compute_from = (int) (compute_from / 2)

            else: #case = odd
                # a proof node is needed to combine pairwise to the next level
                proof += tree[i][compute_from - 1 ]
                compute_from = (int) ((compute_from - 1) / 2)

        return proof

if __name__ == "__main__":
    import random

    tests = []
    n_tests = 8
    # To test, the number of leafs should be equal to N-1 in your parameter set
    leafs = [b'This is a test', b'to see', b'if the Merkle tree', b'works as I think', b'This is a test -wobble', b'to see-wobble', b'if the merkle tree-wobble', b'works as I think-wobble']
    
    for i in range(n_tests):
        tests.append( [ util.H(params.toy)(b + i.to_bytes(2, 'big')) for b in leafs])

    merkleTrees = []
    for i in range(n_tests):
        merkleTrees.append(MerkleTree(params.toy, tests[i]))

    proofs = bytes()
    i = [ i for i in range(n_tests)]
    for j in range(n_tests):
        p =merkleTrees[j].proof(i[j])
        proofs += p

    f_rp = 0
    for j in range(n_tests):
        old_f_rp = f_rp

        root, f_rp = util.recompute_root(params.toy, tests[j][i[j]:], proofs, f_rp)
        print(f'Interruption: {i[j]}')
        old_f_rp = f_rp

        if  root == merkleTrees[j].root:
            print("Yay")
        else:
            print("Nay")

    if f_rp == len(proofs):
        print("fully processed")
    else:
        print(" oh noh... ")


