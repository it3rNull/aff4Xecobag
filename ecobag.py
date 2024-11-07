from __future__ import print_function
from __future__ import absolute_import
from __future__ import unicode_literals

from builtins import next
from builtins import str
from builtins import object
import subprocess
import pickle
import time
import hashlib
from pprint import pprint

import argparse
import sys, os, errno, shutil, uuid
import zipfile


#logging.basicConfig(level=logging.DEBUG)

VERBOSE = False
TERSE = False



def meta(ecb_path):
    #subprocess.run(['python3', 'aff4.py', '-m', aff4])
     if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                print("------------------------------------------------------EcoBag MetaData------------------------------------------------------")
                ecb = pickle.load(fr)         
                print("* EcoBag Hash: ",ecb['hash'])
                print("* aff4 container URN: ",ecb['urn'])
                print("* EcoBag version: ",ecb['version'])
                print("* state number: ",ecb['state'])
                print("* birthdate of EcoBag file: ",ecb['birth'])
                print("* Command operated time: ",ecb['operated'])
                print("* Used EcoBag Hash function: ",ecb['function'])
                print("* MerkleRoot of item hashes: ",ecb['merkleroot'])
                sha = ecb['sha1_hashes']
                md = ecb['md5_hashes']
                print("* Number of items included: ",ecb['nitem'])
                print("---------------------------------------------------------File info---------------------------------------------------------")
                for i in range(ecb["nitem"]):
                    items = ecb["items"][i+1]
                    print("* item Index: ",i+1)
                    print("   item name: ",items['itemName'])
                    print("   item hash: ",items["itemHash"])
                    print("   type: ",items["type"])
                    print("   item state: ", items["itemState"])
                    if items["itemState"] == "encrypted":
                        print("      Encryption algorithm: ",items['method']['algorithm'])
                        print("      Encryption IV :",items['method']['iv'])
                        print("      Encryption keyhash: ",items['method']['keyhash'])
                print("---------------------------------------------------------History---------------------------------------------------------")
                for i in range(ecb['state']+1):
                    print("state ",i,": ",ecb['history'][i])
                print("--------------------------------------------------------------------------------------------------------------------------")
                return sha,md   
                
    
def encrypt(ecb_path,idx,aff4_path):
    extract_ecb(aff4_path)
    if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                item = ecb["items"][int(idx)]
                if item["itemState"] != "normal":
                    print("only normal item can be encrypted .. ")
                    return
    os.remove(ecb_path)
    key = os.popen('python3 aff4.py -E %s %s' % (aff4_path, item['itemName'])).read()
    print("your encryption key: ",key)
    
def decrypt(ecb_path,idx,aff4_path):
    extract_ecb(aff4_path)
    key = input("insert key: ")
    if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                item = ecb["items"][int(idx)]
                if item["itemState"] != "encrypted":
                    print("only encrypted item can be decrypted .. ")
                    return
    os.remove(ecb_path)
    os.system('python3 aff4.py -D %s %s %s' % (key, aff4_path, item['itemName']))
                #print("your encryption key: ",key)
                
def compress(ecb_path,idx,aff4_path):
    extract_ecb(aff4_path)
    if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                item = ecb["items"][int(idx)]
                if item["itemState"] != "normal":
                    print("only normal item can be compressed .. ")
                    return
    os.remove(ecb_path)
    os.system('python3 aff4.py -C %s %s' % (aff4_path, item['itemName']))
                
def decompress(ecb_path,idx,aff4_path):
    extract_ecb(aff4_path)
    if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                item = ecb["items"][int(idx)]
                if item["itemState"] != "compressed":
                    print("only compressed item can be decompressed .. ")
                    return
    os.remove(ecb_path)
    os.system('python3 aff4.py -U %s %s' % (aff4_path, item['itemName']))
                
def delete(ecb_path,idx,aff4_path):
    extract_ecb(aff4_path)
    if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                item = ecb["items"][int(idx)]
    os.remove(ecb_path)            
    os.system('python3 aff4.py -d %s %s' % (aff4_path, item['itemName']))
                
def preview(ecb_path,idx,aff4_path):
    extract_ecb(aff4_path)
    if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                sha1_hashes = []
                md5_hashes = []
                for i in range(ecb['nitem']):
                    items = ecb['items'][i+1]
                    sha1_hashes.append(items['itemHash'][0])
                    md5_hashes.append(items['itemHash'][1])
                    
                sha1_root, _ = compute_merkle_root(sha1_hashes, hashlib.sha1)
                print("SHA-1 Merkle Root:", sha1_root)

                # Verify a hash at index 1 in the SHA-1 tree
                is_valid_sha1 = verify_merkle_tree_index(sha1_hashes, int(idx)-1, sha1_root, hashlib.sha1)
                print("Is SHA-1 valid?", is_valid_sha1)

                # Compute the Merkle root for MD5
                md5_root, _ = compute_merkle_root(md5_hashes, hashlib.md5)
                print("MD5 Merkle Root:", md5_root)

                # Verify a hash at index 2 in the MD5 tree
                is_valid_md5 = verify_merkle_tree_index(md5_hashes, int(idx)-1, md5_root, hashlib.md5)
                print("Is MD5 valid?", is_valid_md5)
    os.remove(ecb_path)


def verify(ecb_path,aff4_path):
    extract_ecb(aff4_path)
    os.system('python3 aff4.py -V %s' % (aff4_path))
    if os.path.isfile(ecb_path):
            os.remove(ecb_path)
    
def hash_pair(left, right, hash_fn):
    combined = left + right
    return hash_fn(combined.encode()).hexdigest()

# Function to compute the Merkle root from a list of hashes
def compute_merkle_root(hashes, hash_fn):
    if len(hashes) == 0:
        return None
    
    tree = [hashes]  # Store all levels of the tree

    # Continue until we reduce to a single hash (the root)
    while len(hashes) > 1:
        if len(hashes) % 2 != 0:
            # If the number of hashes is odd, duplicate the last one
            hashes.append(hashes[-1])
        
        # Hash pairs of elements and update the list
        new_level = []
        for i in range(0, len(hashes), 2):
            new_hash = hash_pair(hashes[i], hashes[i + 1], hash_fn)
            new_level.append(new_hash)
        hashes = new_level
        tree.append(hashes)  # Store this level of the tree

    return tree[-1][0], tree  # The Merkle root and the full tree

# Function to generate proof for a specific index
def generate_proof(index, tree):
    proof = []
    num_levels = len(tree)
    for level in range(num_levels - 1):
        level_len = len(tree[level])
        # Ensure the index has a pair
        if index % 2 == 0:
            # If it's even, the sibling is the next one
            sibling_index = index + 1 if index + 1 < level_len else index
            proof.append((tree[level][sibling_index], 'right'))
        else:
            # If it's odd, the sibling is the previous one
            sibling_index = index - 1
            proof.append((tree[level][sibling_index], 'left'))
        index = index // 2
    return proof

# Function to verify a Merkle tree given the index
def verify_merkle_tree_index(hashes, index, root, hash_fn):
    leaf_hash = hashes[index]  # The hash at the given index
    
    # Compute the Merkle root and the tree
    _, tree = compute_merkle_root(hashes, hash_fn)
    
    # Generate the proof for the given index
    proof = generate_proof(index, tree)
    
    # Verify the proof using the previously defined function
    return verify_merkle_tree(leaf_hash, proof, root, hash_fn)

# Function to verify the proof given the leaf hash, proof, and root
def verify_merkle_tree(leaf_hash, proof, root, hash_fn):
    current_hash = leaf_hash
    
    for sibling_hash, direction in proof:
        if direction == 'left':
            current_hash = hash_pair(sibling_hash, current_hash, hash_fn)
        else:  # direction == 'right'
            current_hash = hash_pair(current_hash, sibling_hash, hash_fn)
    
    # If the computed hash equals the root, the proof is valid
    return current_hash == root
    
def extract_ecb(file_path):
    dir_path = os.path.dirname(file_path)
    ecb_path = file_path.split('.aff4')[:-1][0] + ".ecb"

    with zipfile.ZipFile(file_path,'r') as zip_ref:
        zip_ref.extract('ecobag',path=dir_path)
    os.rename(dir_path+'/ecobag',ecb_path)
    
    return ecb_path
    

def main(argv):
    #print(sys.argv[1])
    aff4_path = sys.argv[1]
    
    while(1):
        ecb_path = extract_ecb(aff4_path)
        meta(ecb_path)
        os.remove(ecb_path)
        print("* Options available: encrypt <idx> | decrypt <idx> | compress <idx> | decompress <idx> | deletion <idx> | preview <idx> | verify | quit")
        print("* Enter operation option and target file index")
        print("* usage: <option> <index>            ex) encryption 1")        
        query = input().split()
        #print(len(query))
        if query[0] == "verify":
            verify(ecb_path,aff4_path)
        elif query[0] == "quit":
            
            return
        elif len(query) != 2:
            print("inappropriate input .. ")
        elif query[0] == "encrypt":
            encrypt(ecb_path,query[1],aff4_path)
        elif query[0] == "decrypt":
            decrypt(ecb_path,query[1],aff4_path)
        elif query[0] == "compress":
            compress(ecb_path,query[1],aff4_path)
        elif query[0] == "decompress":
            decompress(ecb_path,query[1],aff4_path)
        elif query[0] == "deletion":
            delete(ecb_path,query[1],aff4_path)
        elif query[0] == "preview":
            preview(ecb_path,query[1],aff4_path)        
        else:
            print("inappropriate input .. ")
            continue
        
        


if __name__ == "__main__":
    main(sys.argv)
