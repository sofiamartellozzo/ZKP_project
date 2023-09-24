import random

import hashlib
from math import log2, ceil

"""
The Partition Problem
Given a list of numbers (l) partition it in two subset (m)
that sumup to the same number, 
computing another list (p) with the partial dot product between l and m
Example. 
l = [4,11,8,1]
m = [1,-1,1,-1]
p = [0,4,-7,1,0]
Given a problem (l) and a satisfying assignment (m), the function below construct a witeness (p) that will attest the satisfiability of the problem instance.
"""

def get_witness(problem, assignment):
    """
    Given an instance of a partition problem via a list of numbers (the problem) and a list of (-1, 1), we say that the assignment satisfies the problem if their dot product is 0.
    """
    sum = 0
    mx = 0    
    side_obfuscator = 1 - 2 * random.randint(0, 1)
    witness = [sum]
    assert len(problem) == len(assignment)
    for num, side in zip(problem, assignment):
        assert side == 1 or side == -1
        sum += side * num * side_obfuscator
        witness += [sum]
        mx = max(mx, num)
    # make sure that it is a satisfying assignment
    assert sum == 0
    shift = random.randint(0, mx)
    witness = [x + shift for x in witness]
    return witness

"""
A simple class with a constructor that gets a list of numbers as input, constructs the necessary Merkle Tree, and allows the user to get the root's hash, and obtain authentication paths for the numbers in the underlying list.
"""
def hash_string(s):
    return hashlib.sha256(s.encode()).hexdigest()

class MerkleTree:
    """
    A naive Merkle tree implementation using SHA256
    """
    def __init__(self, data):
        self.data = data
        next_pow_of_2 = int(2**ceil(log2(len(data))))
        self.data.extend([0] * (next_pow_of_2 - len(data)))
        self.tree = ["" for x in self.data] + \
                    [hash_string(str(x)) for x in self.data]
        for i in range(len(self.data) - 1, 0, -1):
            self.tree[i] = hash_string(self.tree[i * 2] + self.tree[i * 2 + 1])

    def get_root(self):
        # save the root at index 1 not 0 (convinient)
        return self.tree[1]

    def get_val_and_path(self, id):
        # root at index 1, children of node i are 2i and 2i+1
        val = self.data[id]
        auth_path = []
        id = id + len(self.data)
        while id > 1:
            auth_path += [self.tree[id ^ 1]]
            id = id // 2
        return val, auth_path

def verify_merkle_path(root, data_size, value_id, value, path):
    cur = hash_string(str(value))
    tree_node_id = value_id + int(2**ceil(log2(data_size)))
    for sibling in path:
        assert tree_node_id > 1
        if tree_node_id % 2 == 0:
            cur = hash_string(cur + sibling)
        else:
            cur = hash_string(sibling + cur)
        tree_node_id = tree_node_id // 2
    assert tree_node_id == 1
    return root == cur

"""
Adding a random data for each leaf to make the Merkle Tree zero knowledge.
"""
class ZkMerkleTree:
    """
    A Zero Knowledge Merkle tree implementation using SHA256
    """
    def __init__(self, data):
        self.data = data
        next_pow_of_2 = int(2**ceil(log2(len(data))))
        self.data.extend([0] * (next_pow_of_2 - len(data)))
        # Intertwine with randomness to obtain zero knowledge.
        rand_list = [random.randint(0, 1 << 32) for x in self.data]
        self.data = [x for tup in zip(self.data, rand_list) for x in tup]
        # Create bottom level of the tree (i.e. leaves).
        self.tree = ["" for x in self.data] + \
                    [hash_string(str(x)) for x in self.data]
        for i in range(len(self.data) - 1, 0, -1):
            self.tree[i] = hash_string(self.tree[i * 2] + self.tree[i * 2 + 1])

    def get_root(self):
        return self.tree[1]

    def get_val_and_path(self, id):
        # Because of the zk padding, the data is now at id * 2
        id = id * 2
        val = self.data[id]
        auth_path = []
        id = id + len(self.data)
        while id > 1:
            auth_path += [self.tree[id ^ 1]]
            id = id // 2
        return val, auth_path

def verify_zk_merkle_path(root, data_size, value_id, value, path):
    cur = hash_string(str(value))
    # Due to zk padding, data_size needs to be multiplied by 2, as does the value_id
    tree_node_id = value_id * 2 + int(2**ceil(log2(data_size * 2)))
    for sibling in path:
        assert tree_node_id > 1
        if tree_node_id % 2 == 0:
            cur = hash_string(cur + sibling)
        else:
            cur = hash_string(sibling + cur)
        tree_node_id = tree_node_id // 2
    assert tree_node_id == 1
    return root == cur

"""
The prover generates a witness (using get_witness from the first post in this series).
The prover creates a ZK Merkle Tree from the witness, and sends its root-hash to the verifier.
The verifier sends a random number i to the prover.
If i < n then the prover sends to the verifier:
    The elements in places i and i + 1 in the witness.
    The authentication paths proving that these answers are consistent with the root sent in step (2).
If i == n then the prover sends the first and the last elements in the witness, with the authentication paths etc.
The verifier checks the authentication paths against the root, and the returned numbers against the problem instance.
The verifier returns true iff everything checks out.
"""
# PROVER
l = [4,11,8,1]
m = [1,-1,1,-1]
w = get_witness(l,m)
print('generated witness', w)
tree = ZkMerkleTree(w)
root = tree.get_root
print('the root is', tree.get_root())
# VERIFIER
i = int(input())
print('I want i= ', i)
# PROVER
print('The two elements are ', w[i], w[i+1])
val1, path1 = tree.get_val_and_path(i)
val2, path2 = tree.get_val_and_path(i+1)
print('The path of elem i is: ', tree.get_val_and_path(i))
print('The path of elem i+1 is: ', tree.get_val_and_path(i+1))
# VERIFIER
sol = verify_zk_merkle_path(tree.get_root(), len(l)+1, i, val1, path1)
print(sol)


