#!/usr/bin/env python3
"""B1 — the real axiom verifier.

Replaces the v1.0.0 check, which was a dead path: it ran
    grep -qv -E "propext|Classical.choice|Quot.sound|depends on axioms"
over the whole output. Every line contains the substring "depends on axioms", so the
inverted match could never fire. A custom axiom — and even `sorryAx` — passed.

This verifier:
  * reads the attested declaration set from release/manifest.json;
  * cross-checks it against the `-- @attested <name>` markers in the Lean source, in BOTH
    directions, so the attested set cannot shrink with the source and a new claimed
    theorem cannot go unattested;
  * runs `#print axioms` for every attested declaration;
  * PARSES the output with a narrow regex and compares the axiom SET against an
    allow-list;
  * FAILS CLOSED — on a missing declaration, a missing line, unparseable output, or a
    non-zero exit from Lean.

It does not use source grep as the primary check. `sorryAx` is caught here, structurally,
because Lean reports it as an axiom.
"""
import json, re, subprocess, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
MAN = json.load(open(ROOT / "release/manifest.json"))
ALLOWED = set(MAN["allowed_axioms"])
ATTESTED = list(MAN["attested_declarations"])

FAILURES = []


def fail(msg):
    FAILURES.append(msg)
    print(f"  FAIL  {msg}")


def ok(msg):
    print(f"  ok    {msg}")


# ---------------------------------------------------------------- manifest <-> source
src_marked = set()
for f in (ROOT / "lean" / "Cjson").rglob("*.lean"):
    for m in re.finditer(r"^--\s*@attested\s+(\S+)\s*$", f.read_text(), re.M):
        src_marked.add("Cjson." + m.group(1))

man_set = set(ATTESTED)
if len(ATTESTED) != len(man_set):
    fail("manifest attested_declarations contains duplicates")

missing_in_manifest = src_marked - man_set          # a new claimed theorem, unattested
missing_in_source = man_set - src_marked            # an attested theorem that vanished
if missing_in_manifest:
    fail(f"declarations marked @attested in source but NOT in manifest: "
         f"{sorted(missing_in_manifest)}")
if missing_in_source:
    fail(f"declarations in manifest but NOT marked @attested in source: "
         f"{sorted(missing_in_source)}")
if not FAILURES:
    ok(f"manifest and source agree on {len(man_set)} attested declarations")

# ---------------------------------------------------------------- rebuild first
# CRITICAL: `lake env lean` elaborates against the .olean files. If they are STALE, this
# check reports the axioms of the PREVIOUS build and a mutated proof sails through. The
# mutation suite caught exactly that. So we rebuild here and FAIL CLOSED on a build error;
# this check is therefore self-contained and cannot be defeated by running it out of order.
b = subprocess.run(["lake", "build"], cwd=ROOT / "lean", capture_output=True, text=True)
if b.returncode != 0:
    fail(f"`lake build` failed ({b.returncode}) — cannot attest axioms. FAILING CLOSED.")
    print("\n*** AXIOM VERIFICATION FAILED ***")
    sys.exit(1)
# Lean renders this with BACKTICKS: "declaration uses `sorry`". Match either quoting.
SORRY_WARN = re.compile(r"declaration uses .?sorry.?")
for ln in (b.stdout + b.stderr).splitlines():
    if SORRY_WARN.search(ln):
        fail(f"build warning: {ln.strip()}")
ok("lake build up to date (oleans are current, so the axiom report below is not stale)")

# ---------------------------------------------------------------- #print axioms
probe = "import Cjson\nopen Cjson\n" + "".join(f"#print axioms {d.split('.', 1)[1]}\n"
                                               for d in ATTESTED)
probe_path = ROOT / "lean" / ".vsf_axiom_probe.lean"
probe_path.write_text(probe)
try:
    r = subprocess.run(["lake", "env", "lean", str(probe_path)],
                       cwd=ROOT / "lean", capture_output=True, text=True)
finally:
    probe_path.unlink(missing_ok=True)

if r.returncode != 0:
    fail(f"`lake env lean` exited {r.returncode} — FAILING CLOSED. stderr:\n{r.stderr[:800]}")
    print("\n*** AXIOM VERIFICATION FAILED ***")
    sys.exit(1)

out = r.stdout

# 'Cjson.foo' depends on axioms: [a, b, c]   |   'Cjson.foo' does not depend on any axioms
LINE = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))\s*$",
                  re.M)
seen = {}
for m in LINE.finditer(out):
    name = m.group(1)
    axioms = set() if m.group(3) else {a.strip() for a in m.group(2).split(",") if a.strip()}
    seen[name] = axioms

# every line of output must have parsed — fail closed on anything unrecognised
for line in out.splitlines():
    if line.strip() and not LINE.match(line):
        fail(f"unparseable line from `#print axioms` (failing closed): {line!r}")

for decl in ATTESTED:
    if decl not in seen:
        fail(f"{decl}: NO `#print axioms` output — declaration missing or renamed (fail closed)")
        continue
    extra = seen[decl] - ALLOWED
    if extra:
        fail(f"{decl}: DISALLOWED AXIOM(S) {sorted(extra)}  (allowed: {sorted(ALLOWED)})")
    else:
        ok(f"{decl}: {sorted(seen[decl]) or 'no axioms'}")

if FAILURES:
    print(f"\n*** AXIOM VERIFICATION FAILED — {len(FAILURES)} problem(s) ***")
    sys.exit(1)
print(f"\nAll {len(ATTESTED)} attested declarations depend only on {sorted(ALLOWED)}.")
