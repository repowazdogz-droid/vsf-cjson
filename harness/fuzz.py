#!/usr/bin/env python3
"""Phase 3b: differential fuzzing, oracle (C) vs Lean port.

Corpus: byte-level mutations of valid seeds (the y_ files) + pure random bytes.

The classifier is deliberately CONSERVATIVE. It recognises only the divergence classes
established in Phase 1 / 3a; anything else is reported as UNKNOWN. UNKNOWNs are the only
interesting output -- a clean run means the fuzzer found no divergence outside the
classes we already decided about on purpose.
"""
import subprocess, random, sys, os, glob, json, re
from decimal import Decimal
from concurrent.futures import ProcessPoolExecutor
from collections import Counter

ORACLE = os.path.abspath("./oracle/cjson_oracle")
LEAN = os.path.abspath("./lean/.lake/build/bin/cjson")
N = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
SEED = 20260714


def run(binary, data):
    try:
        p = subprocess.run([binary], input=data, capture_output=True, timeout=20)
        return p.returncode, p.stdout
    except subprocess.TimeoutExpired:
        return 99, b"<TIMEOUT>"


# ---------- classification ----------

HEXD = b"0123456789abcdefABCDEF"
NUL_ESC = b"\\u0000"


PARSE_FAIL = object()   # sentinel: NOT None. json.loads(b"null") legitimately returns
                        # None, and conflating the two mis-classified 22 real D-NUM
                        # divergences as UNKNOWN on the first 120k run. See REPORT.md.


def norm_json(b):
    """Parse output into a comparable structure with EXACT decimal numbers.
    Returns PARSE_FAIL if the output is not valid JSON -- which would itself be a
    finding, since both binaries are supposed to emit valid JSON."""
    try:
        return json.loads(b.decode("utf-8", "surrogateescape"),
                          parse_float=Decimal, parse_int=Decimal)
    except Exception:
        return PARSE_FAIL


def has_bad_u_escape(inp):
    for m in re.finditer(rb"\\u", inp):
        tail = inp[m.end():m.end() + 4]
        if len(tail) < 4 or not all(c in HEXD for c in tail):
            return True
    return False


def has_nul_semantics(inp, lean_out):
    """cJSON stores strings as NUL-terminated C strings, so it truncates at any NUL."""
    return (NUL_ESC in lean_out) or (NUL_ESC in inp) or (0 in inp)


def classify(inp, oe, oo, le, lo):
    if oe == le and oo == lo:
        return None                                 # agreement
    if oe != le:
        if oe == 0 and le == 1 and has_bad_u_escape(inp):
            return "D-STR-1"                        # oracle takes invalid \\u as U+0000
        if oe == 0 and le == 1 and has_nul_semantics(inp, lo):
            return "D-STR-2"
        return "UNKNOWN-exit"
    if oe != 0:
        return None                                 # both rejected
    if has_nul_semantics(inp, lo):
        return "D-STR-2"                            # oracle truncated at a NUL
    ov, lv = norm_json(oo), norm_json(lo)
    if ov is PARSE_FAIL or lv is PARSE_FAIL:
        return "UNKNOWN-unparseable"
    if ov == lv:
        return "D-FMT"                              # same value, different spelling
    return "D-NUM"                                  # oracle's double pipeline lost it


# ---------- corpus ----------

def load_seeds():
    seeds = [open(p, "rb").read()
             for p in sorted(glob.glob("harness/JSONTestSuite/test_parsing/y_*.json"))]
    seeds += [b'{"a":[1,2,{"b":null}],"c":true}', b'[1.5e-3,-0,0.1]',
              b'"\\ud83d\\ude00"', b'[1e400,0.30000000000000004]']
    return seeds


SEEDS = load_seeds()
ALPHABET = bytes([0x7b, 0x7d, 0x5b, 0x5d, 0x22, 0x2c, 0x3a, 0x30, 0x31, 0x39, 0x2e,
                  0x65, 0x45, 0x2b, 0x2d, 0x74, 0x72, 0x75, 0x66, 0x61, 0x6c, 0x73,
                  0x6e, 0x5c, 0x2f, 0x20, 0x09, 0x0a, 0x00, 0xff, 0x80, 0x75])


def mutate(rnd, data):
    d = bytearray(data)
    for _ in range(rnd.randint(1, 4)):
        if not d:
            d = bytearray(rnd.choice(SEEDS))
            continue
        op = rnd.randint(0, 5)
        i = rnd.randrange(len(d))
        if op == 0:
            d[i] = rnd.randrange(256)
        elif op == 1:
            d[i] = rnd.choice(ALPHABET)
        elif op == 2:
            d.insert(i, rnd.choice(ALPHABET))
        elif op == 3:
            del d[i]
        elif op == 4:
            d[i:i] = rnd.choice(SEEDS)[:rnd.randint(1, 8)]
        else:
            d = d[:i]
    return bytes(d)


def gen(i):
    rnd = random.Random(SEED + i)
    if i % 5 == 0:
        return bytes(rnd.randrange(256) for _ in range(rnd.randint(0, 40)))
    return mutate(rnd, rnd.choice(SEEDS))


def work(i):
    inp = gen(i)
    oe, oo = run(ORACLE, inp)
    le, lo = run(LEAN, inp)
    c = classify(inp, oe, oo, le, lo)
    if c is None:
        return None
    return dict(cls=c, inp=inp.hex(), oe=oe, oo=oo.hex(), le=le, lo=lo.hex())


if __name__ == "__main__":
    counts = Counter()
    findings = []
    with ProcessPoolExecutor(max_workers=8) as ex:
        for k, res in enumerate(ex.map(work, range(N), chunksize=200)):
            if res:
                counts[res["cls"]] += 1
                if res["cls"].startswith("UNKNOWN") or counts[res["cls"]] <= 3:
                    findings.append(res)
            if (k + 1) % 20000 == 0:
                print(f"  {k+1}/{N} ...", flush=True)
    counts["AGREE"] = N - sum(counts.values())
    json.dump(dict(n=N, counts=dict(counts), findings=findings),
              open("harness/fuzz_results.json", "w"), indent=1)
    print(f"\n=== {N} inputs ===")
    for k, v in sorted(counts.items(), key=lambda x: -x[1]):
        print(f"  {k:22s} {v}")
    unk = [f for f in findings if f["cls"].startswith("UNKNOWN")]
    print(f"\nUNKNOWN divergences: {len(unk)}")
    for f in unk[:25]:
        print(f'  {f["cls"]}  in={bytes.fromhex(f["inp"])[:60]!r}')
        print(f'      oracle[{f["oe"]}]={bytes.fromhex(f["oo"])[:60]!r}')
        print(f'      lean  [{f["le"]}]={bytes.fromhex(f["lo"])[:60]!r}')
