import os
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
