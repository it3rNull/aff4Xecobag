import hashlib

class MerkleTree:
    def __init__(self, sha1_list, md5_list):
        self.sha1_list = sha1_list
        self.md5_list = md5_list
        self.tree_sha1 = self.build_full_tree(self.sha1_list, "sha1")
        self.tree_md5 = self.build_full_tree(self.md5_list, "md5")
        self.root_sha1 = self.tree_sha1[-1][0]
        self.root_md5 = self.tree_md5[-1][0]

    def build_full_tree(self, hash_list, hash_type):
        """Builds the full tree and returns all levels, not just the root."""
        levels = [hash_list]  # Start with the leaf nodes (first level)
        
        while len(levels[-1]) > 1:
            current_level = levels[-1]
            new_level = []
            for i in range(0, len(current_level), 2):
                if i + 1 < len(current_level):
                    combined_hash = self.hash_pair(current_level[i], current_level[i + 1], hash_type)
                else:
                    combined_hash = current_level[i]  # Propagate last hash if odd number of nodes
                new_level.append(combined_hash)
            levels.append(new_level)
        
        return levels

    def hash_pair(self, left_hash, right_hash, hash_type):
        combined = left_hash + right_hash
        if hash_type == "sha1":
            return hashlib.sha1(combined.encode('utf-8')).hexdigest()
        elif hash_type == "md5":
            return hashlib.md5(combined.encode('utf-8')).hexdigest()

    def get_root_sha1(self):
        return self.root_sha1

    def get_root_md5(self):
        return self.root_md5

    def get_proof(self, index, hash_type="sha1"):
        """Generates the Merkle proof for a given leaf index."""
        if hash_type == "sha1":
            tree = self.tree_sha1
        else:
            tree = self.tree_md5

        proof = []
        level = 0
        while level < len(tree) - 1:
            # Determine the sibling index
            if index % 2 == 0:  # Left child
                sibling_index = index + 1 if index + 1 < len(tree[level]) else None
                if sibling_index is not None:
                    proof.append((tree[level][sibling_index], 'right'))
            else:  # Right child
                proof.append((tree[level][index - 1], 'left'))
            
            # Move up to the parent level
            index = index // 2
            level += 1

        return proof

    def verify_proof(self, leaf, index, proof, root, hash_type="sha1"):
        """Verifies the integrity of the Merkle tree using the proof."""
        current_hash = leaf

        for sibling_hash, direction in proof:
            if direction == 'left':
                current_hash = self.hash_pair(sibling_hash, current_hash, hash_type)
            else:
                current_hash = self.hash_pair(current_hash, sibling_hash, hash_type)

        return current_hash == root

# Example usage
sha1_hashes = [
    '9ae1b46bead70c322eef7ac8bc36a8ea2055595c', 
    'f10e2821bbbea527ea02200352313bc059445190', 
    '5baa61e4c9b93f3f0682250b6cf8331b7ee68fd8',
    '2fd4e1c67a2d28fced849ee1bb76e7391b93eb12'
]
md5_hashes = [
    'd41d8cd98f00b204e9800998ecf8427e', 
    '0cc175b9c0f1b6a831c399e269772661', 
    '900150983cd24fb0d6963f7d28e17f72',
    'f96b697d7cb7938d525a2f31aaf161d0'
]

# Construct the Merkle tree
merkle_tree = MerkleTree(sha1_hashes, md5_hashes)

# Get the root hash
print("SHA-1 Merkle Tree Root:", merkle_tree.get_root_sha1())

# Get proof for the first leaf (index 0)
proof_sha1 = merkle_tree.get_proof(0, hash_type="sha1")
leaf_sha1 = sha1_hashes[1]

# Verify the proof
is_valid = merkle_tree.verify_proof(leaf_sha1, 0, proof_sha1, merkle_tree.get_root_sha1(), hash_type="sha1")
print("SHA-1 Leaf at index 0 is valid:", is_valid)
