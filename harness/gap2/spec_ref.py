#!/usr/bin/env python3
"""GAP-2 Phase 2 — a reference DECIDER for the spec grammar, written from SPEC.md.

Purpose: hunt for a witness of  parseDoc s = some v  ∧  ¬ Spec.Accepts s.

This is a decision procedure for the relation in lean/Cjson/Spec/Grammar.lean. It is written
from SPEC.md prose, NOT transliterated from Cjson/Parser.lean. Where the spec is ambiguous the
choice is marked  # AMBIGUITY-n  and recorded in GAP2.md.

It returns the MAXIMAL-MUNCH parse (SPEC §S3.1: cJSON consumes the longest strtod-valid number
prefix). It also exposes `any_value_prefix`, which answers the weaker existential question that
C1/C5 actually ask: "is SOME prefix grammatical?"
"""
import sys

DEPTH_LIMIT = 1000                      # SPEC §S2

# The grammar nests up to 1000 deep, and this decider is recursive. Python's default limit is
# 1000 frames, so a legitimate deep document raised RecursionError -- which an earlier version
# CAUGHT AND REPORTED AS A GRAMMAR REJECTION. That is a fail-open instrument bug of exactly the
# kind this project keeps finding in its own harness: it would have manufactured phantom
# "soundness violations" at depth, or hidden real ones. RecursionError is now a HarnessError
# and can never masquerade as a rejection.
sys.setrecursionlimit(50000)


class Reject(Exception):
    """The grammar genuinely does not accept this input."""


class HarnessError(Exception):
    """WE failed, not the grammar. Never silently treated as a rejection."""


def is_ws(b):    return b <= 32         # SPEC §S1.1 — ANY byte <= 32
def is_digit(b): return 0x30 <= b <= 0x39
def is_hex(b):   return b in b"0123456789abcdefABCDEF"


def canon(neg, digits, exp):
    """Canonical exact decimal: strip leading zeros, then trailing zeros (adjusting exp);
    an all-zero mantissa collapses to unsigned zero. Matches Grammar.SameNum's normal form."""
    ds = list(digits)
    while ds and ds[0] == 0:
        ds.pop(0)
    k = 0
    while ds and ds[-1] == 0:
        ds.pop()
        k += 1
    if not ds:
        return (False, (), 0)
    return (neg, tuple(ds), exp + k)


class Ref:
    def __init__(self, s):
        self.s = s
        self.i = 0

    def eof(self):  return self.i >= len(self.s)
    def peek(self): return None if self.eof() else self.s[self.i]

    def skip_ws(self):
        while not self.eof() and is_ws(self.s[self.i]):
            self.i += 1

    # ---------------- numbers (SPEC §S3.1) ----------------
    def number(self):
        """Longest strtod-valid prefix. Caller has already checked the §S2 dispatch gate."""
        neg = False
        if self.peek() == 0x2D:                     # '-'
            neg = True
            self.i += 1
        ip = []
        while not self.eof() and is_digit(self.s[self.i]):
            ip.append(self.s[self.i] - 0x30)
            self.i += 1
        fp = []
        if self.peek() == 0x2E:                     # '.'
            save = self.i
            self.i += 1
            while not self.eof() and is_digit(self.s[self.i]):
                fp.append(self.s[self.i] - 0x30)
                self.i += 1
            # "1." is valid (strtod accepts it); "-." is not, but that is caught by the
            # mantissa test below, so no backtrack is needed here.
            del save
        if not ip and not fp:
            raise Reject("number: no mantissa digit")
        e = 0
        if self.peek() in (0x65, 0x45):             # 'e' | 'E'
            save = self.i
            self.i += 1
            esign = 1
            if self.peek() in (0x2B, 0x2D):
                esign = -1 if self.peek() == 0x2D else 1
                self.i += 1
            ed = []
            while not self.eof() and is_digit(self.s[self.i]):
                ed.append(self.s[self.i] - 0x30)
                self.i += 1
            if not ed:
                self.i = save                       # exponent NOT consumed (so `1e` -> 1)
            else:
                e = esign * int("".join(map(str, ed)))
        return ("num", canon(neg, ip + fp, e - len(fp)))

    # ---------------- strings (SPEC §S4) ----------------
    def string(self):
        assert self.s[self.i] == 0x22
        self.i += 1
        out = bytearray()
        while True:
            if self.eof():
                raise Reject("string: unterminated")
            c = self.s[self.i]
            if c == 0x22:                           # closing quote
                self.i += 1
                return ("str", bytes(out))
            if c != 0x5C:                           # SPEC §S4.2 / §S1.3: raw control bytes and
                out.append(c)                       # invalid UTF-8 pass through unexamined
                self.i += 1
                continue
            # escape
            if self.i + 1 >= len(self.s):
                raise Reject("string: trailing backslash")
            d = self.s[self.i + 1]
            simple = {0x22: 0x22, 0x5C: 0x5C, 0x2F: 0x2F, 0x62: 0x08,
                      0x66: 0x0C, 0x6E: 0x0A, 0x72: 0x0D, 0x74: 0x09}
            if d in simple:
                out.append(simple[d])
                self.i += 2
                continue
            if d != 0x75:
                raise Reject("string: unknown escape")   # SPEC §S4.1
            cp = self._hex4(self.i + 2)                  # D-STR-1: 4 VALID hex required
            self.i += 6
            if 0xDC00 <= cp <= 0xDFFF:
                raise Reject("string: lone low surrogate")
            if 0xD800 <= cp <= 0xDBFF:                   # SPEC §S4.4: must be a PAIR
                if not (self.i + 6 <= len(self.s)
                        and self.s[self.i] == 0x5C and self.s[self.i + 1] == 0x75):
                    raise Reject("string: unpaired high surrogate")
                lo = self._hex4(self.i + 2)
                if not (0xDC00 <= lo <= 0xDFFF):
                    raise Reject("string: bad low surrogate")
                self.i += 6
                cp = 0x10000 + (((cp & 0x3FF) << 10) | (lo & 0x3FF))
            out.extend(chr(cp).encode("utf-8", "surrogatepass"))

    def _hex4(self, j):
        if j + 4 > len(self.s):
            raise Reject(r"string: truncated \u")
        h = self.s[j:j + 4]
        if not all(is_hex(b) for b in h):
            raise Reject(r"string: invalid \u hex")      # D-STR-1 (we reject; cJSON accepts)
        return int(h.decode(), 16)

    # ---------------- values ----------------
    def value(self, depth):
        if self.eof():
            raise Reject("value: eof")
        c = self.s[self.i]
        if self.s[self.i:self.i + 4] == b"null":
            self.i += 4; return ("null",)
        if self.s[self.i:self.i + 4] == b"true":
            self.i += 4; return ("bool", True)
        if self.s[self.i:self.i + 5] == b"false":
            self.i += 5; return ("bool", False)
        if c == 0x22:
            return self.string()
        if c == 0x2D or is_digit(c):                # SPEC §S2 DISPATCH GATE
            return self.number()
        if c == 0x5B:
            return self.array(depth)
        if c == 0x7B:
            return self.object(depth)
        raise Reject("value: no alternative")

    def array(self, depth):
        if depth >= DEPTH_LIMIT:                    # SPEC §S2
            raise Reject("array: nesting limit")
        self.i += 1
        self.skip_ws()
        if self.peek() == 0x5D:
            self.i += 1
            return ("arr", [])
        xs = []
        while True:
            self.skip_ws()
            xs.append(self.value(depth + 1))
            self.skip_ws()
            c = self.peek()
            if c == 0x2C:
                self.i += 1
                continue
            if c == 0x5D:
                self.i += 1
                return ("arr", xs)
            raise Reject("array: expected , or ]")

    def object(self, depth):
        if depth >= DEPTH_LIMIT:
            raise Reject("object: nesting limit")
        self.i += 1
        self.skip_ws()
        if self.peek() == 0x7D:
            self.i += 1
            return ("obj", [])
        kvs = []
        while True:
            self.skip_ws()
            if self.peek() != 0x22:
                raise Reject("object: key must be a string")
            _, k = self.string()
            self.skip_ws()
            if self.peek() != 0x3A:
                raise Reject("object: expected :")
            self.i += 1
            self.skip_ws()
            v = self.value(depth + 1)
            kvs.append((k, v))                      # SPEC §S2: duplicates PRESERVED, in order
            self.skip_ws()
            c = self.peek()
            if c == 0x2C:
                self.i += 1
                continue
            if c == 0x7D:
                self.i += 1
                return ("obj", kvs)
            raise Reject("object: expected , or }")


def jdepth(v):
    if v[0] == "arr":
        return 1 + max([jdepth(x) for x in v[1]], default=0)
    if v[0] == "obj":
        return 1 + max([jdepth(x) for _, x in v[1]], default=0)
    return 0


def parse_doc(s):
    """Decide SDoc. Returns (value, consumed_end) or None.

    SPEC §S5.1: trailing bytes after a complete top-level value are ACCEPTED, so this returns
    a value even when bytes remain.
    """
    if s.startswith(b"\xef\xbb\xbf"):               # SPEC §S1.2
        s = s[3:]
    r = Ref(s)
    r.skip_ws()
    try:
        v = r.value(0)
    except Reject:
        return None
    except RecursionError as e:
        raise HarnessError("reference decider ran out of stack") from e
    if jdepth(v) > DEPTH_LIMIT:
        return None
    return (v, r.i)


def any_value_prefix(s):
    """The weaker EXISTENTIAL question C1/C5 ask: is SOME prefix grammatical?

    The only source of prefix ambiguity in this grammar is the number token (`1.2.3` has the
    grammatical prefixes `1` and `1.2`). Structural values are delimiter-terminated and so are
    unambiguous. Hence: SOME prefix is grammatical iff the maximal-munch parse succeeds — with
    one exception we must check explicitly, namely that a *shorter* number prefix could be
    grammatical where the maximal one is not. That cannot happen: the number scanner never
    fails after consuming ≥1 mantissa digit. So the two coincide, which is why C1 and C2 stand
    or fall together here. Verified empirically by hunt.py.
    """
    return parse_doc(s) is not None
