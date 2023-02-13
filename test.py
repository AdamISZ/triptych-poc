#!/usr/bin/env python
help = """
A demo of using Triptych on random Bitcoin keys
(see lib.py for algo).

To run this as a test:
Provide 3 arguments, base, exponent and message to sign, e.g.:

python test.py 3 4 "hello"

Ring size will be 3^4 (81), the position of the "real" (randomly chosen)
key will be randomized in the list/ring.

The secret key is generated at random and so are all the decoys,
but they are valid secp256k1 keys.

The ring signature is generated and displayed, then verified according to the
algorithm in the paper.

"""

import sys
import copy
import time
import base64
from jmbase import bintohex
from lib import (ring_sign_triptych, verify_triptych,
                 triptych_serialize_signature,
                 gen_rand, Scalar)
import jmbitcoin as btc

def hexer(x):
    if isinstance(x, Scalar):
        return bintohex(x.to_bytes())
    else:
        return bintohex(x)

def test_triptych(n, m, message):
    ringsize = n ** m
    seckey = gen_rand()
    ring = []
    for _ in range(ringsize-1):
        ring.append(btc.privkey_to_pubkey(gen_rand() + b"\x01"))
    ring.append(btc.privkey_to_pubkey(seckey + b"\x01"))
    start_sign_time = time.time()
    sigdata, ring = ring_sign_triptych(seckey, message.encode(), ring, n, m)
    end_sign_time = time.time()
    orig_sigdata = copy.deepcopy(sigdata)
    print("Signing took: {} seconds.".format(end_sign_time - start_sign_time))
    print("... now verifying")
    start_verify_time = time.time()    
    if not verify_triptych(sigdata, message.encode(), ring, n, m):
        print("Test failed; the ring signature did not verify.")
    else:
        end_verify_time = time.time()
        print("It verified, for the message: ", message)
        print("Verifying took: {} seconds.".format(end_verify_time - start_verify_time))
        sigstring, key_image = triptych_serialize_signature(orig_sigdata, hexed=False)
        b64string = base64.b64encode(sigstring)
        print("Here is the raw signature: ")
        print(bintohex(sigstring))
        print("It has length: ", len(sigstring))
        print("Here is the base64 encoded signature:")
        print(b64string.decode())
        print("and here is the key image: ")
        print(bintohex(key_image))
        print("The signature's length is {} bytes, in base64, for {} keys.".format(
            len(b64string.decode()), ringsize))        

if __name__ == "__main__":
    nkeys_base = int(sys.argv[1])
    nkeys_exponent = int(sys.argv[2])
    message = str(sys.argv[3])
    test_triptych(nkeys_base, nkeys_exponent, message)
