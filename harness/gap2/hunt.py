#!/usr/bin/env python3
"""GAP-2 Phase 2 — try to KILL the soundness theorem before proving anything.

Hunts for a witness of:

    SOUNDNESS violation      parseDoc s = some v   but   ¬ Spec.Accepts s
    VALUE violation          both accept, but the values disagree      (kills C2, not C1)
    COMPLETENESS violation   Spec accepts s        but   parseDoc s = none

The Lean binary is the parser under test. `spec_ref.py` decides the grammar. A disagreement in
EITHER direction is a finding; we do not get to pick which side is wrong until we look.

Corpora: exhaustive short inputs over a structurally-relevant alphabet; JSONTestSuite (pinned);
the v1.0.1 fuzz seeds; and targeted attacks on every parser branch.
"""
import subprocess, sys, os, glob, itertools, random, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from spec_ref import parse_doc

LEAN = os.path.abspath("./lean/.lake/build/bin/cjson")

SOUND, VALUE, COMPL = [], [], []
N = 0


def run(data):
    p = subprocess.run([LEAN], input=data, capture_output=True, timeout=20)
    return p.returncode, p.stdout


def check(s):
    """One input. Returns a finding tag or None."""
    global N
    N += 1
    le, lo = run(s)
    spec = parse_doc(s)

    if le == 0 and spec is None:
        SOUND.append((s, lo))                       # parser accepted; grammar does not
        return "SOUNDNESS"
    if le != 0 and spec is not None:
        COMPL.append((s, spec[0]))                  # grammar accepts; parser rejected
        return "COMPLETENESS"
    if le == 0 and spec is not None:
        # both accept: do the VALUES agree? Re-read the parser's own output with the reference
        # decider (its output is a document in the same language) and compare structurally.
        out = parse_doc(lo)
        if out is None:
            VALUE.append((s, lo, "parser output is not in the spec language"))
            return "VALUE"
        if out[0] != spec[0]:
            VALUE.append((s, lo, f"spec={spec[0]!r} parser={out[0]!r}"))
            return "VALUE"
    return None


# ---------------------------------------------------------------- corpora
def exhaustive():
    """Exhaustive over a structurally-relevant alphabet. Every parser branch is reachable."""
    A = bytes([0x22, 0x5C, 0x2F, 0x75, 0x30, 0x31, 0x39, 0x2E, 0x2B, 0x2D, 0x65, 0x45,
               0x5B, 0x5D, 0x7B, 0x7D, 0x2C, 0x3A, 0x20, 0x00, 0x6E, 0x74, 0x66, 0x80])
    for n in range(0, 4):
        for t in itertools.product(A, repeat=n):
            yield bytes(t)
    # length 4 over a smaller, number/escape-focused alphabet
    B = bytes([0x30, 0x31, 0x2E, 0x2D, 0x2B, 0x65, 0x22, 0x5C, 0x75, 0x5B, 0x5D, 0x2C])
    for t in itertools.product(B, repeat=4):
        yield bytes(t)


def targeted():
    return [
        # --- numbers: every branch of the strtod-prefix rule
        b"1", b"-1", b"0", b"-0", b"007", b"1.", b"-.5", b".5", b"+1", b"1.2.3", b"1e", b"1e+",
        b"1e-", b"1E5", b"1e5", b"1e+5", b"1e-5", b"-", b"-.", b".", b"1.e5", b"0.e1",
        b"1e400", b"1e-400", b"1e99999999999999999999", b"-1e400", b"00.0", b"0.0e0",
        b"1..2", b"--1", b"1-2", b"1+2", b"0x1", b"1e1e1", b"1.2e3.4",
        # --- escapes
        b'"\\uZZZZ"', b'"\\u00"', b'"\\u"', b'"\\ud800"', b'"\\udc00"',
        b'"\\ud800\\udc00"', b'"\\ud800\\ud800"', b'"\\ud800x"', b'"\\x"', b'"\\"',
        b'"\\/"', b'"\\u0000"', b'"\\u0041"',
        # --- raw bytes in strings
        b'"\x00"', b'"\x01"', b'"\x1f"', b'"\x7f"', b'"\x80"', b'"\xff"', b'"\xc3\x28"',
        b'"a\x00b"',
        # --- trailing garbage (SPEC S5.1)
        b"1x", b"[1]x", b"nullx", b"truex", b"falsex", b"{}x", b'"a"x', b"1 2",
        b"null null", b"[1] [2]",
        # --- structure
        b"[]", b"{}", b"[,]", b"[1,]", b"{,}", b'{"a":1,}', b'{"a"}', b'{a:1}', b"[1 2]",
        b'{"a":1,"a":2}', b"[[]]", b"[{}]", b'{"":""}',
        # --- whitespace (any byte <= 32)
        b"\x01\x021\x03", b"\x001", b"[\x011\x01]", b"\t\n\r 1",
        # --- BOM
        b"\xef\xbb\xbf1", b"\xef\xbb\xbf", b"\xef\xbb", b"\xef\xbb\xbf\xef\xbb\xbf1",
        # --- literals
        b"nul", b"nulll", b"tru", b"fals", b"NULL", b"True",
        # --- empty
        b"", b" ", b"\x00",
    ]


def nesting():
    out = []
    for d in (1, 2, 998, 999, 1000, 1001, 1002):
        out.append(b"[" * d + b"]" * d)
        out.append(b'{"a":' * d + b"1" + b"}" * d)
    return out


def corpora():
    yield from targeted()
    yield from nesting()
    for p in sorted(glob.glob("harness/JSONTestSuite/test_parsing/*.json")):
        yield open(p, "rb").read()
    yield from exhaustive()
    rnd = random.Random(4242)
    seeds = [open(p, "rb").read()
             for p in sorted(glob.glob("harness/JSONTestSuite/test_parsing/y_*.json"))]
    for i in range(20000):                            # property-based mutation
        d = bytearray(rnd.choice(seeds))
        for _ in range(rnd.randint(1, 3)):
            if not d:
                break
            j = rnd.randrange(len(d))
            op = rnd.randint(0, 3)
            if op == 0:   d[j] = rnd.randrange(256)
            elif op == 1: d.insert(j, rnd.choice(b'0123456789.eE+-"\\u[]{},: \x00'))
            elif op == 2: del d[j]
            else:         d = d[:j]
        yield bytes(d)


if __name__ == "__main__":
    sys.setrecursionlimit(20000)
    for k, s in enumerate(corpora()):
        try:
            check(s)
        except subprocess.TimeoutExpired:
            print(f"TIMEOUT on {s[:40]!r}")
        if (k + 1) % 20000 == 0:
            print(f"  {k+1} inputs ... sound={len(SOUND)} value={len(VALUE)} compl={len(COMPL)}",
                  flush=True)

    print(f"\n=== GAP-2 soundness hunt: {N} inputs ===")
    print(f"  SOUNDNESS violations (parser accepts, grammar rejects) : {len(SOUND)}")
    print(f"  VALUE violations     (both accept, values disagree)    : {len(VALUE)}")
    print(f"  COMPLETENESS viol.   (grammar accepts, parser rejects) : {len(COMPL)}")
    for tag, lst in (("SOUNDNESS", SOUND), ("VALUE", VALUE), ("COMPLETENESS", COMPL)):
        for item in lst[:12]:
            print(f"  [{tag}] {item[0][:60]!r}  ->  {str(item[1])[:70]}")
    json.dump({"n": N,
               "soundness": [[s.hex(), str(o)] for s, o in SOUND[:200]],
               "value": [[s.hex(), o.hex() if isinstance(o, bytes) else str(o), str(m)]
                         for s, o, m in VALUE[:200]],
               "completeness": [[s.hex(), str(v)] for s, v in COMPL[:200]]},
              open("harness/gap2/hunt_results.json", "w"), indent=1)
