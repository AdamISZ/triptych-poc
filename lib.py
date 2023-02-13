#!/usr/bin/env python
help = """
An implementation of the algorithm of Triptych:
https://eprint.iacr.org/2020/018

(log sized linkable ring signatures)

For more detailed discussion of how Triptych works, see:

https://reyify.com/blog/little-riddle

This uses the Joinmarket bitcoin backend, mostly just for its encapsulation
of the package python-bitcointx (`pip install bitcointx` or github:
https://github.com/Simplexum/python-bitcointx).

(though it also uses a couple other helpful functions, so if you do
want to run it then download and run `./install.sh` from:

https://github.com/Joinmarket-Org/joinmarket-clientserver
).
"""

import os
import random
import math
import hashlib
from bitcointx.core.key import CKey
import jmbitcoin as btc
from jmclient.podle import getNUMS
from jmbase import bintohex

groupN  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

infty = "INFTY"

# probably overkill, but just to encapsulate arithmetic in the group;
# this class handles the modular arithmetic of x and +.
class Scalar(object):
    def __init__(self, x):
        self.x = x % groupN
    def to_bytes(self):
        return int.to_bytes(self.x, 32, byteorder="big")
    @classmethod
    def from_bytes(cls, b):
        return cls(int.from_bytes(b, byteorder="big"))
    @classmethod
    def pow(cls, base, exponent):
        return cls(pow(base, exponent, groupN))
    def __add__(self, other):
        if isinstance(other, int):
            y = other
        elif isinstance(other, Scalar):
            y = other.x
        return Scalar((self.x + y) % groupN)
    def __radd__(self, other):
        return self.__add__(other)
    def __sub__(self, other):
        if isinstance(other, int):
            temp = other
        elif isinstance(other, Scalar):
            temp = other.x
        return Scalar((self.x - temp) % groupN)
    def __rsub__(self, other):
        if isinstance(other, int):
            temp = other
        elif isinstance(other, Scalar):
            temp = other.x
        else:
            assert False
        return Scalar((temp - self.x) % groupN)
    def __mul__(self, other):
        if other == 1:
            return self
        if other == 0:
            return Scalar(0)
        return Scalar((self.x * other.x) % groupN)
    def __rmul__(self, other):
        return self.__mul__(other)
    def __str__(self):
        return str(self.x)
    def __repr__(self):
        return str(self.x)
    def __len__(self):
        return len(str(self.x))

def binmult(a, b):
    """ Given two binary strings,
    return their multiplication as a binary string.
    """
    # optimisation for pre-mult with bits:
    if a == 0:
        return b"\x00"*32
    if a == 1:
        return b
    aint = Scalar.from_bytes(a)
    bint = Scalar.from_bytes(b)
    return (aint * bint).to_bytes()

def pointadd(points):
    # NB this is not correct as it does not account for cancellation;
    # not sure how a return is serialized as point at infinity in that case.
    # (but it doesn't happen in the uses in this module).
    pointstoadd = [x for x in points if x != infty]
    if len(pointstoadd) == 1:
        return pointstoadd[0]
    if len(pointstoadd) == 0:
        return infty
    return btc.add_pubkeys(pointstoadd)

def pointmult(multiplier, point):
    # given a scalar 'multiplier' as a binary string,
    # and a pubkey 'point', returns multiplier*point
    # as another pubkey object
    if multiplier == 0:
        return infty
    if multiplier == 1:
        return point
    if int.from_bytes(multiplier, byteorder="big") == 0:
        return infty
    return btc.multiply(multiplier, point, return_serialized=False)

def delta(a, b):
    # kronecker delta
    return 1 if a==b else 0

def poly_mult_lin(coeffs, a, b):
    """ Given a set of polynomial coefficients,
    in *decreasing* order of exponent from len(coeffs)-1 to 0,
    return the equivalent set of coeffs after multiplication
    by ax+b. Note a, b and all the returned elements are type Scalar.
    """
    coeffs_new = [Scalar(0) for _ in range(len(coeffs)+1)]
    coeffs_new[0] = a * coeffs[0]
    for i in range(1, len(coeffs_new)-1):
        coeffs_new[i] = b*coeffs[i-1] + a* coeffs[i]
    coeffs_new[-1] = b*coeffs[-1]
    return coeffs_new

def gen_rand(l=32):
    return os.urandom(l)

def gen_privkey_set(n, m):
    return (CKey(gen_rand(m), True) for _ in range(n))

# reuse NUMS points code from PoDLE
H = getNUMS(255)
J = getNUMS(254)

# the actual secp generator
G = btc.getG(True)

def get_matrix_NUMS(n, m):
    # note that get_NUMS is currently limited to i*j < 256
    pts = []
    for i in range(n):
        inner_pts = []
        for j in range(m):
            inner_pts.append(getNUMS(i*m + j))
        pts.append(inner_pts)
    return pts

def nary_decomp(x, n, m):
    """ Given an integer x, a base n and an exponent m,
    return a digit representation of x in that base, padded
    out with zeros up to n^m-1.
    """
    if n == 0:
        return [0] * m
    digits = []
    while x:
        digits.append(int(x % n))
        x //= n
    return digits + [0] * (m - len(digits))

def hash_transcript(s):
    return hashlib.sha256(s).digest()

def get_bits_from_ring(ring):
    return math.ceil(math.log(len(ring), 2))

def hexer(x):
    if isinstance(x, Scalar):
        return bintohex(x.to_bytes())
    else:
        return bintohex(x)

"""Triptych code starts here
"""

def matrix_pedersen_commit(matrix, randomness):
    """ Given an array of arrays `matrix`, and a
    random 32 byte scalar, return a single commitment
    pubkey/point.
    C = matrix_0,0 * H_0,0 + .. matrix_n-1,m-1 H_n-1,m-1 + rG
    """
    pts = []
    H = get_matrix_NUMS(len(matrix), len(matrix[0]))
    for i, x in enumerate(matrix):
        for j, y in enumerate(x):
            pts.append(pointmult(y.to_bytes(), H[i][j]))
    pts.append(pointmult(randomness.to_bytes(), G))
    return pointadd(pts)

def grwzsr(n, m):
    """ get randoms with zero sum rows/
    generates a matrix of random numbers,
    where there are m rows, and each row has n columns,
    and the sum of all the randoms along one row is always zero.
    """
    matrix = []
    for j in range(m):
        matrix.append([])
        sumrow = Scalar(0)
        for i in range(1, n):
            q = Scalar.from_bytes(gen_rand())
            sumrow += q
            matrix[j].append(q)
        # not efficient but cost is negligible cf crypto
        matrix[j].insert(0, Scalar(-1) * sumrow)
    return matrix

def triptych_get_A(n, m):
    """ returns the commitment to A and its opening.
    """
    matrix = grwzsr(n, m)
    randomness = Scalar.from_bytes(gen_rand())
    commitment = matrix_pedersen_commit(matrix, randomness)
    return (commitment, randomness, matrix)

def triptych_get_C(matrix_a, matrix_s):
    assert len(matrix_a) == len(matrix_s)
    matrix_c = []
    for j in range(len(matrix_a)):
        matrix_c.append([])
        for i in range(len(matrix_a[0])):
            matrix_c[j].append(matrix_a[j][i] * (
                Scalar(1) - Scalar(2) * matrix_s[j][i]))
    randomness = Scalar.from_bytes(gen_rand())
    commitment = matrix_pedersen_commit(matrix_c, randomness)
    return (commitment, randomness, matrix_c)

def triptych_get_D(matrix_a):
    matrix_d = []
    for i in range(len(matrix_a)):
        matrix_d.append([])
        for j in range(len(matrix_a[0])):
            matrix_d[i].append(Scalar(-1) * matrix_a[i][j] * matrix_a[i][j])
    randomness = Scalar.from_bytes(gen_rand())
    commitment = matrix_pedersen_commit(matrix_d, randomness)
    return (commitment, randomness, matrix_d)

def triptych_get_sigma(n, m, l):
    sigma = []
    l_decomp = nary_decomp(l, n, m)
    for j in range(m):
        sigma.append([])
        for i in range(n):
            sigma[j].append(Scalar(delta(l_decomp[j], i)))
    return sigma

def triptych_get_B(n, m, l):
    sigma = triptych_get_sigma(n, m, l)
    randomness = Scalar.from_bytes(gen_rand())
    commitment = matrix_pedersen_commit(sigma, randomness)
    return (commitment, randomness, sigma)

def ring_sign_triptych(seckey, message, ring, n, m):
    """ Unlike GK14, here we need to actually tell the signing
    algorithm how we want to decompose the size of the ring, i.e.
    what exponent and base to use, hence the arguments n, m.
    """
    N = n ** m
    real_pub = btc.privkey_to_pubkey(seckey + b"\x01")
    #print("real pub: ", bytes(real_pub))
    assert bytes(real_pub) in ring
    assert isinstance(ring, list)
    assert len(ring) == N
    random.shuffle(ring)
    l = ring.index(real_pub)
    print("got this index for the signer: ", l)
    comm_A, rand_A, matrix_A = triptych_get_A(n, m)
    comm_B, rand_B, matrix_sigma = triptych_get_B(n, m, l)
    comm_C, rand_C, matrix_C = triptych_get_C(matrix_A, matrix_sigma)
    comm_D, rand_D, matrix_D = triptych_get_D(matrix_A)
    # form the polynomials, one per ring element:
    # to form the polynomial coefficients of the polynomials p_i(x),
    # for each i-th element of the ring:
    polys = []
    for i in range(len(ring)):
        idigits = nary_decomp(i, n, m)
        polyi = [Scalar(1)]
        for j in range(m):
            mult = (matrix_sigma[j][idigits[j]], matrix_A[j][idigits[j]])
            polyi = poly_mult_lin(polyi, *mult)
        polys.append(polyi[::-1]) # reverse order because poly lin mult returns coeffs for x^n-1, x^n-2,...x^0
    rhos = [Scalar.from_bytes(gen_rand()) for _ in range(m)]
    X = triptych_get_X(polys, ring, rhos)
    Y = triptych_get_Y(rhos)
    # get hash challenge
    x = Scalar.from_bytes(hash_transcript(b",".join([str(a).encode() for a in [
        comm_A, comm_B, comm_C, comm_D, X, Y, ring]]) + b"," + message))
    print("Got hash challenge: ", str(x))
    f = triptych_get_f(matrix_sigma, matrix_A, x)
    zA = rand_A + x * rand_B
    zC = rand_C * x + rand_D
    rhopowers = [Scalar.pow(x.x, j) * rhos[j] for j in range(m)]
    z = Scalar.from_bytes(seckey) * Scalar.pow(x.x, m) - sum(rhopowers)
    U = triptych_get_key_image(seckey)
    return ((comm_A, comm_B, comm_C, comm_D, X, Y, f, zA, zC, z, U), ring)

def triptych_get_key_image(seckey):
    """ In future will be expanded to include counters etc.
    """
    return pointmult(seckey, J)

def triptych_serialize_signature(sig, hexed=True):
    """serializes the sigma protocol inputs and outputs,
    and then the key image separately.
    """
    comm_A, comm_B, comm_C, comm_D, X, Y, f, zA, zC, z, U = sig
    ser = b""
    for x in [comm_A, comm_B, comm_C, comm_D]:
        ser += bytes(x)
    for a in [X, Y]:
        for b in a:
            ser += bytes(b)
    for a in f:
        for b in a:
            ser += b.to_bytes()
    for x in [zA, zC, z]:
        ser += x.to_bytes()
    if hexed:
        ser = bintohex(ser)
        u_out = bintohex(U)
    else:
        u_out = bytes(U)
    return (ser, u_out)

def verify_triptych(sig, message, ring, n, m):
    comm_A, comm_B, comm_C, comm_D, X, Y, f, zA, zC, z, U = sig
    # get hash challenge
    x = Scalar.from_bytes(hash_transcript(b",".join([str(a).encode() for a in [
        comm_A, comm_B, comm_C, comm_D, X, Y, ring]]) + b"," + message))
    print("Got hash challenge: ", str(x))
    # first step: the verifier can reconstruct the first element in each
    # row in the response matrix 'f' (this step enforces that only 1 bit
    # in each row is 1, with the rest 0):
    for j in range(m):
        sumrow = sum(f[j])
        f[j].insert(0, x - sumrow)
    # check A + xB:
    lhs1 = pointadd([comm_A, pointmult(x.to_bytes(), comm_B)])
    rhs1 = matrix_pedersen_commit(f, zA)
    assert lhs1 == rhs1
    # check xC + D:
    lhs2 = pointadd([pointmult(x.to_bytes(), comm_C), comm_D])
    # calc f(x-f) matrix
    fxf = []
    for j in range(len(f)):
        fxf.append([])
        for i in range(len(f[0])):
            fxf[j].append(f[j][i] * (x - f[j][i]))
    rhs2 = matrix_pedersen_commit(fxf, zC)
    assert lhs2 == rhs2
    # for the final 2 checks, we are checking per ring element
    sum_m_f_terms = []
    sum_u_f_terms = []
    for k in range(len(ring)):
        prodf = Scalar(1)
        for j in range(m):
            prodf *= f[j][nary_decomp(k, n, m)[j]]
        sum_m_f_terms.append(pointmult(prodf.to_bytes(), ring[k]))
        sum_u_f_terms.append(pointmult(prodf.to_bytes(), U))
    sum_m_f = pointadd(sum_m_f_terms)
    sum_u_f = pointadd(sum_u_f_terms)
    zG = pointmult(z.to_bytes(), G)
    zJ = pointmult(z.to_bytes(), J)
    xX_terms = []
    xY_terms = []
    for j in range(m):
        xX_terms.append(pointmult(Scalar.pow(x.x, j).to_bytes(), X[j]))
        xY_terms.append(pointmult(Scalar.pow(x.x, j).to_bytes(), Y[j]))
    xX = pointadd(xX_terms)
    xY = pointadd(xY_terms)
    # check 3 for the ring itself:
    rhs3 = pointadd([xX, zG])
    assert sum_m_f == rhs3
    # check 4 for the linking tag/image:
    rhs4 = pointadd([xY, zJ])
    assert sum_u_f == rhs4
    return True

def triptych_get_f(matrix_s, matrix_A, x):
    fs = []
    for j in range(len(matrix_s)):
        fs.append([])
        # we omit the first term; the verifier will enforce
        # that the total for the row is 1:
        for i in range(1, len(matrix_s[0])):
            fs[j].append(matrix_s[j][i] * x + matrix_A[j][i])
    return fs

def triptych_get_X(polys, ring, rhos):
    ptsj = []
    for j in range(len(rhos)):
        ptsk = []
        for k in range(len(ring)):
            ptsk.append(pointmult(polys[k][j].to_bytes(), ring[k]))
        ptsk.append(pointmult(rhos[j].to_bytes(), G))
        ptsj.append(pointadd(ptsk))
    return ptsj

def triptych_get_Y(rhos):
    return [pointmult(rhos[i].to_bytes(), J) for i in range(len(rhos))]

