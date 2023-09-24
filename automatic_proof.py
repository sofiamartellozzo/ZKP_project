import random

import hashlib
from math import log2, ceil

from MerkleTree import *

def get_proof(problem, assignment, num_queries):
    proof = []
    randomness_seed = problem[:]
    for i in range(num_queries):
        witness = get_witness(problem, assignment)
        tree = ZkMerkleTree(witness)
        random.seed(str(randomness_seed))
        query_idx = random.randint(0, len(problem))
        query_and_response = [tree.get_root()]
        query_and_response += [query_idx]
        query_and_response += tree.get_val_and_path(query_idx)
        query_and_response += tree.get_val_and_path((query_idx + 1) % len(witness))
        proof += [query_and_response]
        randomness_seed += [query_and_response]
    return proof

def verify_proof(problem, proof):
    proof_checks_out = True
    randomness_seed = problem[:]
    for query in proof:
        random.seed(str(randomness_seed))
        query_idx = random.randint(0, len(problem))
        merkle_root = query[0]
        proof_checks_out &= query_idx == query[1]
        # Test witness properties.
        if query_idx < len(problem):
            proof_checks_out &= abs(query[2] - query[4]) == abs(problem[query_idx])
        else:
            proof_checks_out &= query[2] == query[4]
        # Authenticate paths
        proof_checks_out &= \
            verify_zk_merkle_path(merkle_root, len(problem) + 1, query_idx, query[2], query[3])
        proof_checks_out &= \
            verify_zk_merkle_path(merkle_root, len(problem) + 1, \
                                 (query_idx + 1) % (len(problem) + 1), query[4], query[5])
        randomness_seed += [query]
    return proof_checks_out


def test(q):
    problem = [1, 2, 3, 6, 6, 6, 12]
    assignment = [1, 1, 1, -1, -1, -1, 1]
    proof = get_proof(problem, assignment, q)
    print(proof)
    return verify_proof(problem, proof)

test(2)