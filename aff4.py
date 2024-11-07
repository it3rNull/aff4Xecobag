# Copyright 2018-2019 Schatz Forensic Pty Ltd. All rights reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not
# use this file except in compliance with the License.  You may obtain a copy of
# the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
# License for the specific language governing permissions and limitations under
# the License.
# author bradley@evimetry.com

from __future__ import print_function
from __future__ import absolute_import
from __future__ import unicode_literals

from builtins import next
from builtins import str
from builtins import object

import argparse
import sys, os, errno, shutil, uuid
import time
import logging
import json
from collections import OrderedDict
import hashlib
from glob import glob
import random
from pprint import pprint
import zipfile

from pyaff4 import container, version
from pyaff4 import lexicon, logical, escaping
from pyaff4 import rdfvalue, hashes, utils
from pyaff4 import block_hasher, data_store, linear_hasher, zip
from pyaff4 import aff4_map
import merkletree
from datetime import datetime
import struct, hashlib, time
import binascii
import os
from Crypto.Cipher import AES
import pickle

#logging.basicConfig(level=logging.DEBUG)

VERBOSE = False
TERSE = False

def hash_dict(d):
    # Sort the dictionary items and convert them to a tuple
    dict_items = tuple(sorted(d.items()))
    # Create a hash of the tuple
    return hashlib.sha256(str(dict_items).encode()).hexdigest()

def initEcb(urn):
    state_info = {}
    state_info["hash"] = None
    state_info["urn"] = urn
    state_info["version"] = 1
    state_info["state"] = 0
    state_info["birth"] = datetime.now()
    state_info["operated"] = []
    state_info["function"] = ["sha1","md5"]
    state_info["merkleroot"] = []
    state_info["nitem"] = 0
    state_info["items"] = {}
    state_info["history"] = {0:{}}
    #print(state_info)
    
    return state_info

def EcbAddItem(ecb,pathname,state,type):
    ecb["nitem"] += 1
    nitems = ecb["nitem"]
    ecb["items"][(ecb["nitem"])] = {
                    "type":type,
                "itemState":"normal",
                "itemName":pathname,
                "method":{},
                "itemHash":[]
            }
    ecb["history"][ecb["state"]][(ecb["nitem"])] = state
    
def chk_key(key,ecb_key):
    if binascii.hexlify(hashlib.sha256(key).digest()) == ecb_key:
        return False
    else:
        return True
    
def EcbEncryptItem(ecb,pathname,key,iv):
    if '.enc' not in pathname:
        return
    pathname2 = pathname.strip('./enc')
    enc_idx = []
    for i in range(ecb["nitem"]):
        items = ecb["items"][i+1]
        if items["itemName"][2:] == pathname2:
            items['itemName'] = pathname
            items["itemState"] = "encrypted"
            items["method"]["algorithm"] = "aes256"
            items["method"]["iv"] = binascii.hexlify(bytearray(iv))
            items["method"]["keyhash"] = binascii.hexlify(hashlib.sha256(key).digest())
            #print(binascii.hexlify(bytearray(key)),binascii.hexlify(bytearray(iv)))
            enc_idx.append(i+1)
            #ecb['history'][ecb['state']][i+1] = "encrypted"
    for i in enc_idx:
        ecb['history'][ecb['state']][i] = "encrypted"
    #print(ecb['history'])

    #pprint(ecb["items"][1])
    
def EcbDecryptItem(ecb,pathname):
    if '.enc' in pathname:
        return
    enc_idx = []
    for i in range(ecb["nitem"]):
        items = ecb["items"][i+1]
        if items['itemName'] == pathname+'.enc':
            print(items['itemName'])
            items['itemName'] = pathname
            items["itemState"] = ecb['history'][ecb['state']-2][i+1]
            items["method"] = {}
            #print(binascii.hexlify(bytearray(key)),binascii.hexlify(bytearray(iv)))
            enc_idx.append(i+1)
            #ecb['history'][ecb['state']][i+1] = "encrypted"
    for i in enc_idx:
        ecb['history'][ecb['state']][i] = ecb['history'][ecb['state']-2][i]
    #print(ecb['history'])

    #pprint(ecb["items"][1])
    
def EcbAliveItem(ecb,pathname,deleted_file):
    del_idx = []
    for i in range(ecb["nitem"]):
        items = ecb["items"][i+1]
        if items['itemName'] in deleted_file:
            items['itemState'] = "deleted"
            items['method'] = {}
            del_idx.append(i+1)
    for i in del_idx:
        ecb['history'][ecb['state']][i] = "deleted"
    
def EcbCompressItem(ecb,pathname,compressed_file):
    if '.compressed' not in pathname:
        return
    del_idx = []
    
    for i in range(ecb["nitem"]):
        items = ecb["items"][i+1]
        if items['itemName'] in compressed_file:
            print(items['itemName'])
            items['itemName'] = pathname
            items['itemState'] = "compressed"
            del_idx.append(i+1)
    for i in del_idx:
        ecb['history'][ecb['state']][i] = "compressed"
        
def EcbUnCompressItem(ecb,pathname,compressed_file):
    del_idx = []

    for i in range(ecb["nitem"]):
        items = ecb["items"][i+1]
        if items['itemName'] in compressed_file:
            #print("asdasd",items['itemName'],pathname)
            items['itemName'] = '.'+items['itemName'].strip('.compressed')
            items['itemState'] = "normal"
            del_idx.append(i+1)
    for i in del_idx:
        ecb['history'][ecb['state']][i] = "normal"
    

def EcbDictHash(ecb):
    ecb.pop('hash')
    hashed_dict = hash_dict(ecb)
    ecb['hash'] = hashed_dict
    

    
def EcbGenHistory(ecb,state):
    ecb["history"][state] = {}
    
def EcbItemHash(ecb,hash):
    ecb["items"][(ecb["nitem"])]["itemHash"].append(hash)
    
def compress_file(file_path, newSrcFiles):
    with zipfile.ZipFile(file_path+'.compressed', 'w') as zipf:
        zipf.write(file_path, arcname=file_path.split('/')[-1])
        newSrcFiles.append(file_path+'.compressed')
        
def uncompress_file(file_path, newSrcFiles,out_filename):
    dest = '/'.join(out_filename.split('/')[:-1])
    #print("uncom :",file_path,'/'.join(out_filename.split('/')[:-1]))
    with zipfile.ZipFile(file_path, 'r') as zipf:
        zipf.extractall(dest)
        newSrcFiles.append(out_filename)
    

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




    
    

def printImageMetadata(resolver, volume, image):
    print("\t%s <%s>" % (image.name(), trimVolume(volume.urn, image.urn)))
    with resolver.AFF4FactoryOpen(image.urn) as srcStream:
        if type(srcStream) == aff4_map.AFF4Map2:
            source_ranges = sorted(srcStream.tree)
            for n in source_ranges:
                d = n.data
                print("\t\t[%x,%x] -> %s[%x,%x]" % (
                d.map_offset, d.length, srcStream.targets[d.target_id], d.target_offset, d.length))

def printTurtle(resolver, volume):
    metadataURN = volume.urn.Append("information.turtle")
    try:
        with resolver.AFF4FactoryOpen(metadataURN) as fd:
            txt = fd.ReadAll()
            print(utils.SmartUnicode(txt))
    except:
        pass

def meta(file, password):
    with container.Container.openURNtoContainer(rdfvalue.URN.FromFileName(file)) as volume:
        printTurtle(volume.resolver, volume)

        if password != None:
            assert not issubclass(volume.__class__, container.PhysicalImageContainer)
            volume.setPassword(password[0])
            childVolume = volume.getChildContainer()
            printTurtle(childVolume.resolver, childVolume)
            for image in childVolume.images():
                printImageMetadata(childVolume.resolver, childVolume, image)
        else:
            for image in volume.images():
                printImageMetadata(volume.resolver, volume, image)



def list(file, password):
    start = time.time()
    with container.Container.openURNtoContainer(rdfvalue.URN.FromFileName(file)) as volume:
        if password != None:
            assert not issubclass(volume.__class__, container.PhysicalImageContainer)
            #volume.block_store_stream.DEBUG = True
            volume.setPassword(password[0])
            childVolume = volume.getChildContainer()
            printLogicalImageInfo(file, childVolume)
        else:
            print("Finished in %d (s)" % int(time.time() - start))
            if issubclass(volume.__class__, container.PhysicalImageContainer):
                printDiskImageInfo(file, volume)
            elif issubclass(volume.__class__, container.LogicalImageContainer):
                printLogicalImageInfo(file, volume)

def printLogicalImageInfo(file, volume):
    printVolumeInfo(file, volume)
    printCaseInfo(volume)

    for image in volume.images():
        print ("\t%s <%s>" % (image.name(), trimVolume(volume.urn, image.urn)))


def printVolumeInfo(file, volume):
    volumeURN = volume.urn

    #print("AFF4Container: file://%s <%s>" % (file, str(volumeURN)))

def printCaseInfo(volume):
    caseDetails = volume.getMetadata("CaseDetails")
    if caseDetails == None:
        return
    print ("\tCase Description: %s" % caseDetails.caseDescription)
    print ("\tCase Name: %s" % caseDetails.caseName)
    print ("\tExaminer: %s" % caseDetails.examiner)

def printDiskImageInfo(file, volume):
    printVolumeInfo(file, volume)
    printCaseInfo(volume)

    image = volume.getMetadata("DiskImage")
    print ("\t%s (DiskImage)" % image.urn)
    print ("\t\tSize: %s (bytes)" % image.size)
    print ("\t\tSize: %s (bytes)" % image.size)
    print ("\t\tSectors: %s" % image.sectorCount)
    print ("\t\tBlockMapHash: %s" % image.hash)

    # the following property is to test that unknown properties are handled OK
    print ("\t\tUnknownproperty: %s" % image.foobar)

    computerInfo = volume.getMetadata("ComputeResource")
    if computerInfo != None:
        print ("\tAcquisition computer details")
        print ("\t\tSystem board vendor: %s" % computerInfo.systemboardVendor)
        print ("\t\tSystem board serial: %s" % computerInfo.systemboardSerial)
        print ("\t\tUnknownproperty: %s" % computerInfo.foobar)


class VerificationListener(object):
    def __init__(self):
        self.results = []

    def onValidBlockHash(self, a):
        pass

    def onInvalidBlockHash(self, a, b, imageStreamURI, offset):
        self.results.append("Invalid block hash comarison for stream %s at offset %d" % (imageStreamURI, offset))

    def onValidHash(self, typ, hash, imageStreamURI):
        self.results.append("Validation of %s %s succeeded. Hash = %s" % (imageStreamURI, typ, hash))

    def onInvalidHash(self, typ, a, b, streamURI):
        self.results.append("Invalid %s comarison for stream %s" % (typ, streamURI))

class LinearVerificationListener(object):
    def __init__(self):
        self.results = []

    def onValidHash(self, typ, hash, imageStreamURI):
        print ("\t\t%s Verified (%s)" % (typ, hash))

    def onInvalidHash(self, typ, hasha, hashb, streamURI):
        print ("\t\t%s Hash failure stored = %s calculated = %s)" % (typ, hasha, hashb))



def trimVolume(volume, image):
    global TERSE
    if TERSE:
        volstring = utils.SmartUnicode(volume)
        imagestring = utils.SmartUnicode(image)
        if imagestring.startswith(volstring):
            imagestring = imagestring[len(volstring):]
        return imagestring
    else:
        return image


def verify(file, password):
    with container.Container.openURNtoContainer(rdfvalue.URN.FromFileName(file)) as volume:
        if password != None:
            assert not issubclass(volume.__class__, container.PhysicalImageContainer)
            volume.setPassword(password[0])
            childVolume = volume.getChildContainer()
            printVolumeInfo(file, childVolume)
            printCaseInfo(childVolume)
            resolver = childVolume.resolver
            hasher = linear_hasher.LinearHasher2(resolver, LinearVerificationListener())
            for image in childVolume.images():
                print("\t%s <%s>" % (image.name(), trimVolume(childVolume.urn, image.urn)))
                hasher.hash(image)
        else:
            printVolumeInfo(file, volume)
            printCaseInfo(volume)
            resolver = volume.resolver

            if type(volume) == container.PhysicalImageContainer:
                image = volume.image
                listener = VerificationListener()
                validator = block_hasher.Validator(listener)
                print("Verifying AFF4 File: %s" % file)
                validator.validateContainer(rdfvalue.URN.FromFileName(file))
                for result in listener.results:
                    print("\t%s" % result)
            elif type(volume) == container.LogicalImageContainer:
                #print ("\tLogical Images:")
                hasher = linear_hasher.LinearHasher2(resolver, LinearVerificationListener())
                for image in volume.images():
                    print ("\t%s <%s>" % (image.name(), trimVolume(volume.urn, image.urn)))
                    hasher.hash(image)

def ingestZipfile(container_name, zipfiles, append, check_bytes):
    # TODO: check path in exists
    start = time.time()
    with data_store.MemoryDataStore() as resolver:


        container_urn = rdfvalue.URN.FromFileName(container_name)
        urn = None

        if not os.path.exists(container_name):
            volume = container.Container.createURN(resolver, container_urn)
            #print("Creating AFF4Container: file://%s <%s>" % (container_name, volume.urn))
        else:
            volume = container.Container.openURNtoContainer(container_urn, mode="+")
            #print("Appending to AFF4Container: file://%s <%s>" % (container_name, volume.urn))

        resolver = volume.resolver

        with volume as volume:
            for zipfile in zipfiles:
                basefilename = os.path.basename(zipfile)
                if basefilename.endswith(".bag.zip"):
                    basefilename = basefilename[0:len(basefilename) - len(".bag.zip")]


                filename_arn = rdfvalue.URN.FromFileName(zipfile)

                # the following coaxes our ZIP implementation to treat this file
                # as a regular old zip
                result = zip.BasicZipFile(resolver, urn=None, version=version.basic_zip)
                resolver.Set(lexicon.transient_graph, result.urn, lexicon.AFF4_TYPE, rdfvalue.URN("StandardZip"))
                resolver.Set(lexicon.transient_graph, result.urn, lexicon.AFF4_STORED, rdfvalue.URN(filename_arn))

                with resolver.AFF4FactoryOpen(result.urn, version=version.basic_zip) as zip_file:
                    for member in zip_file.members:
                        info = zip_file.members[member]
                        pathname = basefilename +  member.SerializeToString()[len(result.urn.SerializeToString()):]
                        print(pathname)

                        with resolver.AFF4FactoryOpen(member, version=version.aff4v10) as src:

                            hasher = linear_hasher.StreamHasher(src, [lexicon.HASH_SHA1, lexicon.HASH_MD5])
                            if volume.containsLogicalImage(pathname):
                                print("\tCollision: this ARN is already present in this volume.")
                                continue

                            urn = volume.writeLogicalStreamRabinHashBased(pathname, hasher, info.file_size, check_bytes)
                            #fsmeta.urn = urn
                            #fsmeta.store(resolver)
                            for h in hasher.hashes:
                                hh = hashes.newImmutableHash(h.hexdigest(), hasher.hashToType[h])
                                resolver.Add(container_urn, urn, rdfvalue.URN(lexicon.standard.hash), hh)

        print ("Finished in %d (s)" % int(time.time() - start))
        return urn
    
    
def decrypt_file(key, in_filename,origin, out_filename, chunksize=24 * 1024):
    with open(in_filename, 'rb') as infile:
        origsize = struct.unpack('<Q', infile.read(struct.calcsize('Q')))[0]
        iv = infile.read(16)
        decryptor = AES.new(key, AES.MODE_CBC, iv)
        with open(out_filename, 'wb') as outfile:
            while True:
                chunk = infile.read(chunksize)
                if len(chunk) == 0:
                    break
                outfile.write(decryptor.decrypt(chunk))
            outfile.truncate(origsize)
        origin.append(out_filename)
            
def encrypt_file(key, iv,in_filename, origin,out_filename=None, chunksize=65536):
    if not out_filename:
        out_filename = in_filename + '.enc'
    origin.append(out_filename)
    #print(out_filename)
    encryptor = AES.new(key, AES.MODE_CBC, iv)
    filesize = os.path.getsize(in_filename)
    with open(in_filename, 'rb') as infile:
        with open(out_filename, 'wb') as outfile:
            outfile.write(struct.pack('<Q', filesize))
            outfile.write(iv)
            while True:
                chunk = infile.read(chunksize)
                if len(chunk) == 0:
                    break
                elif len(chunk) % 16 != 0:
                    chunk += b' ' * (16 - len(chunk) % 16)
                outfile.write(encryptor.encrypt(chunk))
                
def make_pass():
    timekey = int(time.time()) + random.randrange(1,200)
    #print(timekey)
    return str(timekey)



def addPathNamesToVolume(resolver, volume, pathnames, recursive, hashbased,key = None, iv = None,itemchangetype = None, ecbUpdate = None,ecb = None,deleted_file = None,compressed_file = None):
    sha1_hashes = []
    md5_hashes = []

    for pathname in pathnames:
        if not os.path.exists(pathname):
            print("Path %s not found. Skipping." % pathname)
            continue
        pathname = utils.SmartUnicode(pathname)
        fsmeta = logical.FSMetadata.create(pathname)
        if os.path.isdir(pathname):
            image_urn = None
            if volume.isAFF4Collision(pathname):
                image_urn = rdfvalue.URN("aff4://%s" % uuid.uuid4())
            else:
                image_urn = volume.urn.Append(escaping.arnPathFragment_from_path(pathname), quote=False)

            fsmeta.urn = image_urn
            fsmeta.store(resolver)                    
            
            resolver.Set(volume.urn, image_urn, rdfvalue.URN(lexicon.standard11.pathName), rdfvalue.XSDString(pathname))
            resolver.Add(volume.urn, image_urn, rdfvalue.URN(lexicon.AFF4_TYPE),
                         rdfvalue.URN(lexicon.standard11.FolderImage))
            resolver.Add(volume.urn, image_urn, rdfvalue.URN(lexicon.AFF4_TYPE), rdfvalue.URN(lexicon.standard.Image))
            if recursive:
                for child in os.listdir(pathname):
                    pathnames.append(os.path.join(pathname, child))
        else:
            with open(pathname, "rb") as src:
                hasher = linear_hasher.StreamHasher(src, [lexicon.HASH_SHA1, lexicon.HASH_MD5])
                if hashbased == False:
                    if ecbUpdate == True:
                        if itemchangetype == "encrypted":
                            EcbEncryptItem(ecb,pathname,key,iv)
                        elif itemchangetype == "decrypted":
                            EcbDecryptItem(ecb,pathname)
                        elif itemchangetype == "deleted":
                            EcbAliveItem(ecb,pathname,deleted_file)
                        elif itemchangetype == "compressed":
                            EcbCompressItem(ecb,pathname,compressed_file)
                        elif itemchangetype == "uncompressed":
                            EcbUnCompressItem(ecb,pathname,compressed_file)
                    else:
                        EcbAddItem(ecb,pathname,"normal","ImageMap")
                        
                    urn = volume.writeLogicalStream(pathname, hasher, fsmeta.length)
                else:
                    if ecbUpdate == True:
                        if itemchangetype == "encrypted":
                            EcbEncryptItem(ecb,pathname,key,iv)
                    else:
                        EcbAddItem(ecb,pathname,"normal","HashbasedImageMap")
                        
                    urn = volume.writeLogicalStreamRabinHashBased(pathname, hasher, fsmeta.length)
                
                
                fsmeta.urn = urn
                fsmeta.store(resolver)
                idx = 0
                for h in hasher.hashes:
                    hh = hashes.newImmutableHash(h.hexdigest(), hasher.hashToType[h])
                    if ecbUpdate == False:
                        EcbItemHash(ecb,h.hexdigest())
                    if idx % 2 == 0:
                        sha1_hashes.append(h.hexdigest())
                    else:
                        md5_hashes.append(h.hexdigest())
                    idx += 1
                    #print(ecb)
                    resolver.Add(urn, urn, rdfvalue.URN(lexicon.standard.hash), hh)

    if ecbUpdate == False:          
        sha1_root, _ = compute_merkle_root(sha1_hashes, hashlib.sha1)
        md5_root, _ = compute_merkle_root(md5_hashes, hashlib.md5)
        ecb['merkleroot'].append(sha1_root)
        ecb['merkleroot'].append(md5_root)
        ecb['sha1_hashes'] = sha1_hashes
        ecb['md5_hashes'] = md5_hashes
    
    return ecb
    #MerkleHashlists = []
    #MerkleHashlists.append()

def addPathNames(container_name, pathnames, recursive, append, hashbased, password,key = None,iv = None,itemchangetype = None,deleted_file = None,compressed_file = None):
    with data_store.MemoryDataStore() as resolver:
        container_urn = rdfvalue.URN.FromFileName(container_name)
        urn = None
        encryption = False
        parentVolume = None
        if password != None:
            encryption = True

        if append == False:
            with container.Container.createURN(resolver, container_urn, encryption=encryption) as volume:
                ecb_path = container_name.split('.aff4')[:-1][0] + ".ecb"
                
                if os.path.isfile(ecb_path):
                    ecbUpdate = True
                    with open(ecb_path,'rb') as fr:
                        ecb = pickle.load(fr)
                        ecb["state"] += 1
                        ecb["history"][ecb["state"]] = ecb["history"][ecb["state"]-1].copy()
                        ecb["operated"].append(datetime.now())
                
                else:
                    ecbUpdate = False
                    ecb = initEcb(volume.urn)
                    
                if password != None:
                    volume.setPassword(password[0])
                    childVolume = volume.getChildContainer()
                    addPathNamesToVolume(childVolume.resolver, childVolume, pathnames, recursive, hashbased)
                else:
                    if itemchangetype == "encrypted":
                        ecb = addPathNamesToVolume(resolver, volume, pathnames, recursive, hashbased,key,iv,itemchangetype = itemchangetype, ecbUpdate=ecbUpdate,ecb = ecb)
                        ecb['history'][ecb['state']-1]['hash'] = ecb['hash']
                        EcbDictHash(ecb)
                    elif itemchangetype == "decrypted":
                        ecb = addPathNamesToVolume(resolver, volume, pathnames, recursive, hashbased,itemchangetype = itemchangetype, ecbUpdate=ecbUpdate,ecb = ecb)
                        ecb['history'][ecb['state']-1]['hash'] = ecb['hash']
                        EcbDictHash(ecb)
                    elif itemchangetype == "deleted":
                        ecb = addPathNamesToVolume(resolver, volume, pathnames, recursive, hashbased,itemchangetype = itemchangetype, ecbUpdate=ecbUpdate,ecb = ecb,deleted_file=deleted_file)
                        ecb['history'][ecb['state']-1]['hash'] = ecb['hash']
                        EcbDictHash(ecb)
                    elif itemchangetype == "compressed" or itemchangetype == "uncompressed":
                        ecb = addPathNamesToVolume(resolver, volume, pathnames, recursive, hashbased,itemchangetype = itemchangetype, ecbUpdate=ecbUpdate,ecb = ecb,compressed_file = compressed_file)
                        ecb['history'][ecb['state']-1]['hash'] = ecb['hash']
                        EcbDictHash(ecb)
                    else:
                        ecb = addPathNamesToVolume(resolver, volume, pathnames, recursive, hashbased,itemchangetype = itemchangetype, ecbUpdate=ecbUpdate,ecb = ecb)
                        EcbDictHash(ecb)
                    #print("EcoBag")
            
                #pprint(ecb)
                with open(ecb_path,'wb') as fw:
                    pickle.dump(ecb, fw)
                
                    
        else:
            with container.Container.openURNtoContainer(container_urn, mode="+") as volume:
                #print("Appending to AFF4Container: file://%s <%s>" % (container_name, volume.urn))
                if password != None:
                    volume.setPassword(password[0])
                    childVolume = volume.getChildContainer()
                    addPathNamesToVolume(childVolume.resolver, childVolume, pathnames, recursive, hashbased)
                else:
                    addPathNamesToVolume(resolver, volume, pathnames, recursive, hashbased)

        return urn


def nextOrNone(iterable):
    try:
        return next(iterable)
    except:
        return None

def extractAllFromVolume(container_urn, volume, destFolder):
    printVolumeInfo(container_urn.original_filename, volume)
    resolver = volume.resolver
    pathNames = []
    originpath = []
    for imageUrn in resolver.QueryPredicateObject(volume.urn, lexicon.AFF4_TYPE, lexicon.standard11.FileImage):
        imageUrn = utils.SmartUnicode(imageUrn)

        pathName = next(resolver.QuerySubjectPredicate(volume.urn, imageUrn, lexicon.standard11.pathName)).value
        with resolver.AFF4FactoryOpen(imageUrn) as srcStream:
            if destFolder != "-":
                drive, pathName = os.path.splitdrive(pathName) # Windows drive letters
                destFile = os.path.join(destFolder, drive[:-1], pathName.strip("/\\"))
                if not os.path.exists(os.path.dirname(destFile)):
                    try:
                        os.makedirs(os.path.dirname(destFile))
                    except OSError as exc:  # Guard against race condition
                        if exc.errno != errno.EEXIST:
                            raise
                
                
                destFile = destFile[3:-1]
                pathNames.append(destFile)
                dstpath = '/'.join(destFile.split('/')[:-1]) + '/'
                if dstpath.startswith('./'):
                    dstpath = dstpath[2:]
                #print("dst :", dstpath)
                #print(glob('**/',recursive=True))
                if dstpath not in glob('**/',recursive=True):
                    originpath.append(dstpath)
                    os.mkdir(dstpath)
                
                with open(destFile, "wb") as destStream:
                    shutil.copyfileobj(srcStream, destStream)
                    #print("\tExtracted %s to %s" % (pathName, destFile))

                lastWritten = nextOrNone(
                    resolver.QuerySubjectPredicate(volume.urn, imageUrn, lexicon.standard11.lastWritten))
                lastAccessed = nextOrNone(
                    resolver.QuerySubjectPredicate(volume.urn, imageUrn, lexicon.standard11.lastAccessed))
                recordChanged = nextOrNone(
                    resolver.QuerySubjectPredicate(volume.urn, imageUrn, lexicon.standard11.recordChanged))
                birthTime = nextOrNone(
                    resolver.QuerySubjectPredicate(volume.urn, imageUrn, lexicon.standard11.birthTime))
                logical.resetTimestamps(destFile, lastWritten, lastAccessed, recordChanged, birthTime)

            else:
                shutil.copyfileobj(srcStream, sys.stdout)
    return pathNames,originpath

def extractAll(container_name, destFolder, password):
    container_urn = rdfvalue.URN.FromFileName(container_name)
    urn = None

    with container.Container.openURNtoContainer(container_urn) as volume:
        if password != None:
            assert not issubclass(volume.__class__, container.PhysicalImageContainer)
            volume.setPassword(password[0])
            childVolume = volume.getChildContainer()
            extractAllFromVolume(container_urn, childVolume, destFolder)
        else:
            return extractAllFromVolume(container_urn, volume, destFolder)



def extractFromVolume(container_urn, volume, imageURNs, destFolder):
    printVolumeInfo(container_urn.original_filename, volume)
    resolver = volume.resolver
    for imageUrn in imageURNs:
        imageUrn = utils.SmartUnicode(imageUrn)
        pathName = next(resolver.QuerySubjectPredicate(volume.urn, imageUrn, volume.lexicon.pathName))

        with resolver.AFF4FactoryOpen(imageUrn) as srcStream:
            if destFolder != "-":
                pathName = escaping.arnPathFragment_from_path(pathName.value)
                while pathName.startswith("/"):
                    pathName = pathName[1:]
                drive, pathName = os.path.splitdrive(pathName) # Windows drive letters
                destFile = os.path.join(destFolder, drive[:-1], pathName.strip("/\\"))
                if not os.path.exists(os.path.dirname(destFile)):
                    try:
                        os.makedirs(os.path.dirname(destFile))
                    except OSError as exc:  # Guard against race condition
                        if exc.errno != errno.EEXIST:
                            raise
                with open(destFile, "wb") as destStream:
                    shutil.copyfileobj(srcStream, destStream, length=32 * 2014)
                    print("\tExtracted %s to %s" % (pathName, destFile))
            else:
                shutil.copyfileobj(srcStream, sys.stdout)

def extract(container_name, imageURNs, destFolder, password):
    with data_store.MemoryDataStore() as resolver:
        container_urn = rdfvalue.URN.FromFileName(container_name)
        urn = None

        with container.Container.openURNtoContainer(container_urn) as volume:
            if password != None:
                assert not issubclass(volume.__class__, container.PhysicalImageContainer)
                volume.setPassword(password[0])
                childVolume = volume.getChildContainer()
                extractFromVolume(container_urn, childVolume, imageURNs, destFolder)
            else:
                extractFromVolume(container_urn, volume, imageURNs, destFolder)

def insert_ecb(dest):
    ecb_path = dest[:-4]+'ecb'
    with zipfile.ZipFile(dest,'a') as zip_ref:
        zip_ref.write(ecb_path,arcname='ecobag')
    if os.path.isfile(ecb_path):
            os.remove(ecb_path)

def extract_ecb(file_path):
    dir_path = os.path.dirname(file_path)
    ecb_path = file_path.split('.aff4')[:-1][0] + ".ecb"

    with zipfile.ZipFile(file_path,'r') as zip_ref:
        zip_ref.extract('ecobag',path=dir_path)
    os.rename(dir_path+'/ecobag',ecb_path)

def main(argv):
    
    parser = argparse.ArgumentParser(description='AFF4 command line utility.')
    parser.add_argument("--verbose", action="store_true",
                        help='enable verbose output')
    parser.add_argument('-t', "--terse", action="store_true",
                        help='enable terse output')
    parser.add_argument('-l', "--list", action="store_true",
                        help='list the objects in the container')
    parser.add_argument('-m', "--meta", action="store_true",
                        help='dump the AFF4 metadata found in the container')
    parser.add_argument('-f', "--folder", nargs=1, action="store", default=os.getcwd(),
                        help='the destination folder for extraction of logical images')
    parser.add_argument('-r', "--recursive", action="store_true",
                        help='add files and folders recursively')
    parser.add_argument('-c', "--create-logical", action="store_true",
                        help='create an AFF4 logical container containing srcFiles')
    parser.add_argument('-x', "--extract", action="store_true",
                        help='extract objects from the container')
    parser.add_argument('-X', "--extract-all", action="store_true",
                        help='extract ALL objects from the container')
    parser.add_argument('-H', "--hash", action="store_true",
                        help='use hash based imaging for storing content')
    parser.add_argument('-p', "--paranoid", action="store_true",
                        help='do a byte-for-byte comparison when matching hashes are found with hash based imaging')
    parser.add_argument('-a', "--append", action="store_true",
                        help='append to an existing image')
    parser.add_argument('-i', "--ingest", action="store_true",
                        help='ingest a zip file into a hash based image')
    parser.add_argument('-E', "--encrypt", action="store_true",
                        help='aes256 encryption')
    parser.add_argument('-d', "--delete", action="store_true",
                        help='file deletion')
    parser.add_argument('-C', "--compress", action="store_true",
                        help='zip file compression') 
    parser.add_argument('-U', "--uncompress", action="store_true",
                        help='zip uncompress')    
    parser.add_argument('-D', "--decrypt", action="store", nargs=1,
                        help='decryption with a key')
    parser.add_argument('-V', "--full", action="store_true",
                        help='merkle root full mode verify') 
    parser.add_argument('-e', "--password", nargs=1, action="store",
                        help='provide a password for encryption. This causes an encrypted container to be used.')
    parser.add_argument('aff4container', help='the pathname of the AFF4 container')
    parser.add_argument('srcFiles', nargs="*", help='source files and folders to add as logical image')


    args = parser.parse_args()
    global TERSE
    global VERBOSE
    VERBOSE = args.verbose
    TERSE = args.terse
    

    if args.create_logical == True:
        dest = args.aff4container
        addPathNames(dest, args.srcFiles, args.recursive, args.append, args.hash, args.password)
        insert_ecb(dest)
    elif  args.meta == True:
        dest = args.aff4container
        meta(dest, args.password)
    elif  args.list == True:
        dest = args.aff4container
        list(dest, args.password)
    elif args.extract == True:
        dest = args.aff4container
        extract(dest, args.srcFiles, args.folder[0], args.password)
    elif args.extract_all == True:
        dest = args.aff4container
        extractAll(dest, args.folder[0], args.password)
    elif args.ingest == True:
        dest = args.aff4container
        ingestZipfile(dest, args.srcFiles, False, args.paranoid)
    elif args.decrypt:
        #print(args)
        dest = args.aff4container
        if len(args.srcFiles) == 0:
            print("Enter at least 1 srcFiles")
            return
        origin, originpath = extractAll(dest, args.folder[0], args.password)
        
        deleted = []
        for targets in origin:
            if targets not in args.srcFiles:
                deleted.append(targets)        
                
        ecb_path = dest.split('.aff4')[:-1][0] + ".ecb"
        extract_ecb(dest)
        if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                
        key = bytes.fromhex(args.decrypt[0])
        for i in range(ecb["nitem"]):
            items = ecb["items"][i+1]
            if items['itemName'] in args.srcFiles:
                if(items['itemState'] != "encrypted"):
                    print("Only encryped file can be decrypted ... ")
                if(chk_key(key,items['method']['keyhash'])):
                    print("Wrong key...")
                    return          

        newSrcFiles = deleted
        for target in args.srcFiles:
            out_filename = target.replace('.enc','')
            decrypt_file(key,target,newSrcFiles,out_filename)
        addPathNames(dest, newSrcFiles, args.recursive, args.append, args.hash, args.password,itemchangetype="decrypted")
        insert_ecb(dest)
        
        
        for file in args.srcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for file in newSrcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for path in originpath:
            if os.path.isdir(path):
                os.rmdir(path)
                
    elif args.full:
        dest = args.aff4container
        origin, originpath = extractAll(dest, args.folder[0], args.password)

        ecb_path = dest.split('.aff4')[:-1][0] + ".ecb"
        extract_ecb(dest)
        if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)

        tmp = ecb.copy()
        tmp.pop('hash')
        print("* original stateinfo hash :",ecb['hash'])
        print("* new stateinfo hash:",hash_dict(tmp))
        if ecb['hash'] != hash_dict(tmp):
            print("file contaminated!")
            return
        else:   
            print("Pass")
            print("----------------------------------------------------------------------------------------------------------------------")

        sha1_hashes = []
        md5_hashes = []
        newSrcFiles = []
        for i in range(ecb["nitem"]):
            items = ecb["items"][i+1]
            if items['itemState'] == "normal":
                f = open(items['itemName'], 'rb')
                data = f.read()
                f.close()
                sha1 = hashlib.sha1(data).hexdigest()
                md5 = hashlib.md5(data).hexdigest()
                if sha1 != items['itemHash'][0] or md5 != items['itemHash'][1]:
                    print("file contaminated! %s" % (items['itemName']))
                    return
                print("Re-calculated hash for \'normal\' file \'%s\' :" % items['itemName'],sha1,md5)
                sha1_hashes.append(sha1)
                md5_hashes.append(md5)
                newSrcFiles.append(items['itemName'])
            elif items['itemState'] == "encrypted":
                key = input("insert key of %s" % items['itemName'])
                key = bytes.fromhex(key)
                out_filename = items['itemName'][:-4]
                decrypt_file(key,items['itemName'],newSrcFiles,out_filename)
                f = open(out_filename, 'rb')
                data = f.read()
                f.close()
                sha1 = hashlib.sha1(data).hexdigest()
                md5 = hashlib.md5(data).hexdigest()
                if sha1 != items['itemHash'][0] or md5 != items['itemHash'][1]:
                    print("file contaminated! %s" % (items['itemName']))
                    return
                print("* hash for \'encrypted\' file \'%s\' :" % items['itemName'],sha1,md5)
                sha1_hashes.append(sha1)
                md5_hashes.append(md5)
            elif items['itemState'] == "compressed":
                out_filename = items['itemName'].replace('.compressed','')
                uncompress_file(items['itemName'],newSrcFiles,out_filename)
                f = open(out_filename, 'rb')
                data = f.read()
                f.close()
                sha1 = hashlib.sha1(data).hexdigest()
                md5 = hashlib.md5(data).hexdigest()
                if sha1 != items['itemHash'][0] or md5 != items['itemHash'][1]:
                    print("file contaminated! %s" % (items['itemName']))
                    return
                print("* hash for \'compressed\' file \'%s\' :" % items['itemName'],sha1,md5)
                sha1_hashes.append(sha1)
                md5_hashes.append(md5)
            elif items['itemState'] == "deleted":
                sha1_hashes.append(items["itemHash"][0])
                md5_hashes.append(items["itemHash"][1])
                newSrcFiles.append(items['itemName'])
                print("* hash for \'deleted\' file \'%s\' :" % items['itemName'],items["itemHash"][0],items["itemHash"][1])
        
        sha1_root, _ = compute_merkle_root(sha1_hashes, hashlib.sha1)
        md5_root, _ = compute_merkle_root(md5_hashes, hashlib.md5)
        
        print("----------------------------------------------------------------------------------------------------------------------")
        print("* original merkle root :",ecb['merkleroot'][0],ecb['merkleroot'][1])
        print("* new merkle root      :", sha1_root,md5_root)
        if sha1_root == ecb['merkleroot'][0] and md5_root == ecb['merkleroot'][1]:
            print("Pass")
        else:
            print("Fail")
        
        for file in origin:
            if os.path.isfile(file):
                os.remove(file)
        for file in newSrcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for path in originpath:
            if os.path.isdir(path):
                os.rmdir(path)
        if os.path.isfile(ecb_path):
            os.remove(ecb_path)
        
        
        
                
    elif args.delete:
        #print(args)
        dest = args.aff4container
        if len(args.srcFiles) == 0:
            print("Enter at least 1 srcFiles")
            return
        origin, originpath = extractAll(dest, args.folder[0], args.password)
        
        extract_ecb(dest)
        
        deleted = []
        for targets in origin:
            if targets not in args.srcFiles:
                deleted.append(targets)        
            
                
        newSrcFiles = deleted
        addPathNames(dest, newSrcFiles, args.recursive, args.append, args.hash, args.password,itemchangetype="deleted",deleted_file=args.srcFiles)
        insert_ecb(dest)
        
        
        for file in args.srcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for file in newSrcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for path in originpath:
            if os.path.isdir(path):
                os.rmdir(path)
                
    elif args.compress:
        #print(args)
        dest = args.aff4container
        if len(args.srcFiles) == 0:
            print("Enter at least 1 srcFiles")
            return
        origin, originpath = extractAll(dest, args.folder[0], args.password)
        
        deleted = []
        for targets in origin:
            if targets not in args.srcFiles:
                deleted.append(targets)  
                
        extract_ecb(dest)
        ecb_path = dest.split('.aff4')[:-1][0] + ".ecb"
        if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                
        for i in range(ecb["nitem"]):
            items = ecb["items"][i+1]
            if items['itemName'] in args.srcFiles:
                if(items['itemState'] != "normal"):
                    print("Only normal file can be compressed ... ")
                    return  
          
        newSrcFiles = deleted
        for target in args.srcFiles:
            compress_file(target,newSrcFiles)
        addPathNames(dest, newSrcFiles, args.recursive, args.append, args.hash, args.password,itemchangetype="compressed",compressed_file=args.srcFiles)
        insert_ecb(dest)
        
        for file in args.srcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for file in newSrcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for path in originpath:
            if os.path.isdir(path):
                os.rmdir(path)

    elif args.uncompress:
        #print(args)
        dest = args.aff4container
        if len(args.srcFiles) == 0:
            print("Enter at least 1 srcFiles")
            return
        origin, originpath = extractAll(dest, args.folder[0], args.password)
        
        deleted = []
        for targets in origin:
            if targets not in args.srcFiles:
                deleted.append(targets)  
                
        extract_ecb(dest)
        ecb_path = dest.split('.aff4')[:-1][0] + ".ecb"
        if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                
        for i in range(ecb["nitem"]):
            items = ecb["items"][i+1]
            if items['itemName'] in args.srcFiles:
                if(items['itemState'] != "compressed"):
                    print("Only compressed file can be uncompressed ... ")
                    return  
          
        newSrcFiles = deleted
        for target in args.srcFiles:
            out_filename = target.replace('.compressed','')
            uncompress_file(target,newSrcFiles,out_filename)
        addPathNames(dest, newSrcFiles, args.recursive, args.append, args.hash, args.password,itemchangetype="uncompressed",compressed_file=args.srcFiles)
        insert_ecb(dest)
        
        for file in args.srcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for file in newSrcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for path in originpath:
            if os.path.isdir(path):
                os.rmdir(path)
                
    elif args.encrypt:
        #print(args)
        dest = args.aff4container
        if len(args.srcFiles) == 0:
            print("Enter at least 1 srcFiles")
            return
        origin, originpath = extractAll(dest, args.folder[0], args.password)
        
        deleted = []
        for targets in origin:
            if targets not in args.srcFiles:
                deleted.append(targets)
        #print("test :",deleted)   

        extract_ecb(dest)
        ecb_path = dest.split('.aff4')[:-1][0] + ".ecb"
        
        
        if os.path.isfile(ecb_path):
            with open(ecb_path,'rb') as fr:
                ecb = pickle.load(fr)
                
        for i in range(ecb["nitem"]):
            items = ecb["items"][i+1]
            if items['itemName'] in args.srcFiles:
                if(items['itemState'] != "normal"):
                    print("Only normal file can be encrypted ... ")
                    return     
          
        password1 = make_pass()
        password2 = make_pass()
        
        key = hashlib.sha256(bytes(password1,encoding='utf-8')).digest()
        iv = hashlib.sha256(bytes(password2,encoding='utf-8')).digest()[0:16]
        
        print(binascii.hexlify(bytearray(key)))
        newSrcFiles = deleted
        for target in args.srcFiles:
            encrypt_file(key,iv,target,newSrcFiles)
        addPathNames(dest, newSrcFiles, args.recursive, args.append, args.hash, args.password,key=key,iv=iv,itemchangetype="encrypted")
        insert_ecb(dest)
        
        for file in args.srcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for file in newSrcFiles:
            if os.path.isfile(file):
                os.remove(file)
        for path in originpath:
            if os.path.isdir(path):
                os.rmdir(path)
        

        #print('Encrypt Done !')
        #addPathNames(dest, args.srcFiles, args.recursive, args.append, args.hash, args.password)


if __name__ == "__main__":
    main(sys.argv)
