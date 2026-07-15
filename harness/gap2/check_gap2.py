#!/usr/bin/env python3
"""GAP-2 adequacy gate — the mechanical check that C2, C4 and adequacy are real, unchanged,
and axiom-clean. Independent of the v1.0.1 gate (harness/check_axioms.py); it verifies the
Cjson.Spec chain, which the released root deliberately does not import.

FAILS CLOSED on any of:
  * a `-- @attested-gap2 <name>` marker in lean/Cjson/Spec that is absent from the manifest,
    or a manifest declaration with no marker in source (attested set cannot drift);
  * `lake build <check_module>` failing, or emitting a `sorry` warning (Cjson.Spec.Checks is
    the statement-pin module: if a theorem is weakened/restated it stops compiling);
  * any attested declaration depending on an axiom outside allowed_axioms (catches sorryAx and
    custom axioms structurally), or missing/unparseable `#print axioms` output;
  * the frozen Grammar Prop text (the C1-C5 candidates + SDoc/DepthOk) changing hash;
  * the Spec theorem count drifting from the manifest;
  * any released artifact file differing from tag v1.0.1 (byte-identity of the released parser).

Usage:
  python3 harness/gap2/check_gap2.py               # verify (CI/verify.sh)
  python3 harness/gap2/check_gap2.py --update-grammar-pin   # recompute grammar_prop_pin.sha256
"""
import json, re, subprocess, sys, hashlib, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
MANP = ROOT / "release/gap2_manifest.json"
MAN = json.load(open(MANP))
ALLOWED = set(MAN["allowed_axioms"])
ATTESTED = list(MAN["attested_declarations"])
UPDATE_PIN = "--update-grammar-pin" in sys.argv

FAIL = []
def fail(m): FAIL.append(m); print(f"  FAIL  {m}")
def ok(m):   print(f"  ok    {m}")


def grammar_prop_bytes():
    pin = MAN["grammar_prop_pin"]
    text = (ROOT / pin["file"]).read_text()
    s = text.find(pin["start_marker"])
    e = text.find(pin["end_marker"])
    if s < 0 or e < 0:
        fail("grammar_prop_pin start/end marker not found in Grammar.lean"); return None
    eol = text.find("\n", e)
    eol = len(text) if eol < 0 else eol
    return text[s:eol].encode("utf-8")


# ---- optional: recompute the grammar pin and rewrite the manifest, then exit
if UPDATE_PIN:
    b = grammar_prop_bytes()
    if b is None: sys.exit(1)
    h = hashlib.sha256(b).hexdigest()
    MAN["grammar_prop_pin"]["sha256"] = h
    MANP.write_text(json.dumps(MAN, indent=2, ensure_ascii=False) + "\n")
    print(f"grammar_prop_pin.sha256 updated -> {h}")
    sys.exit(0)

# ---------------------------------------------------------------- markers <-> manifest
rx = re.compile(r"^--\s*@attested-gap2\s+(\S+)\s*$", re.M)
src_marked = set()
for f in (ROOT / "lean/Cjson/Spec").rglob("*.lean"):
    for m in rx.finditer(f.read_text()):
        src_marked.add(m.group(1))

man_set = set(ATTESTED)
if len(ATTESTED) != len(man_set):
    fail("manifest attested_declarations contains duplicates")
if src_marked - man_set:
    fail(f"@attested-gap2 in source but NOT in manifest: {sorted(src_marked - man_set)}")
if man_set - src_marked:
    fail(f"in manifest but NOT marked @attested-gap2 in source: {sorted(man_set - src_marked)}")
if not FAIL:
    ok(f"manifest and source agree on {len(man_set)} attested GAP-2 declarations")

# ---------------------------------------------------------------- rebuild (fail closed)
CHECK = MAN["check_module"]
b = subprocess.run(["lake", "build", CHECK], cwd=ROOT / "lean",
                   capture_output=True, text=True)
if b.returncode != 0:
    fail(f"`lake build {CHECK}` failed ({b.returncode}) — FAILING CLOSED.\n{b.stdout[-1500:]}{b.stderr[-1500:]}")
    print("\n*** GAP-2 VERIFICATION FAILED ***"); sys.exit(1)
SORRY = re.compile(r"declaration uses .?sorry.?")
for ln in (b.stdout + b.stderr).splitlines():
    if SORRY.search(ln):
        fail(f"build warning: {ln.strip()}")
ok(f"lake build {CHECK} clean (statement-pin module compiled ⇒ statements unchanged)")

# ---------------------------------------------------------------- #print axioms
def short(d): return d.split("Cjson.Spec.", 1)[1]
probe = ("import Cjson.Spec\nopen Cjson Cjson.Spec\n"
         + "".join(f"#print axioms {short(d)}\n" for d in ATTESTED))
pp = ROOT / "lean" / ".vsf_gap2_axiom_probe.lean"
pp.write_text(probe)
try:
    r = subprocess.run(["lake", "env", "lean", str(pp)], cwd=ROOT / "lean",
                       capture_output=True, text=True)
finally:
    pp.unlink(missing_ok=True)
if r.returncode != 0:
    fail(f"`lake env lean` exited {r.returncode} — FAILING CLOSED. stderr:\n{r.stderr[:800]}")
    print("\n*** GAP-2 VERIFICATION FAILED ***"); sys.exit(1)

# NB greedy `.+`: some names end in a prime (e.g. parseStrBody_sound'), so the name's own
# closing quote abuts Lean's — `[^']+` would stop short. Greedy `.+` anchors on `' depends`.
LINE = re.compile(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))\s*$", re.M)
seen = {}
for m in LINE.finditer(r.stdout):
    seen[m.group(1)] = set() if m.group(3) else {a.strip() for a in m.group(2).split(",") if a.strip()}
for line in r.stdout.splitlines():
    if line.strip() and not LINE.match(line):
        fail(f"unparseable `#print axioms` line (fail closed): {line!r}")
for d in ATTESTED:
    if d not in seen:
        fail(f"{d}: no `#print axioms` output — missing or renamed (fail closed)"); continue
    extra = seen[d] - ALLOWED
    if extra: fail(f"{d}: DISALLOWED AXIOM(S) {sorted(extra)} (allowed {sorted(ALLOWED)})")
    else:     ok(f"{d}: {sorted(seen[d]) or 'no axioms'}")

# ---------------------------------------------------------------- grammar Prop pin
b2 = grammar_prop_bytes()
if b2 is not None:
    got = hashlib.sha256(b2).hexdigest()
    want = MAN["grammar_prop_pin"]["sha256"]
    if want == "PENDING":
        fail("grammar_prop_pin.sha256 is PENDING — run --update-grammar-pin once, then commit")
    elif got != want:
        fail(f"frozen Grammar Props CHANGED: sha256 {got[:16]}… != pin {want[:16]}…")
    else:
        ok(f"frozen Grammar Props unchanged (sha256 {got[:16]}…)")

# ---------------------------------------------------------------- Spec theorem count
tc = sum(1 for f in sorted((ROOT / "lean/Cjson/Spec").glob("*.lean"))
           for ln in open(f)
           if ln.startswith("theorem ") or ln.startswith("@[simp] theorem "))
exp = MAN["expected_spec_theorem_count"]
if tc == exp: ok(f"Spec theorem count {tc} == manifest {exp}")
else:         fail(f"Spec theorem count {tc} != manifest {exp} (update deliberately)")

# ---------------------------------------------------------------- proof modules reachable
def imports_of(mod):
    p = ROOT / "lean" / (mod.replace(".", "/") + ".lean")
    if not p.exists(): return None
    return re.findall(r"^import\s+(\S+)", p.read_text(), re.M)
reach, stack = set(), [CHECK]
while stack:
    m = stack.pop()
    if m in reach: continue
    reach.add(m)
    imps = imports_of(m)
    if imps is None: continue
    stack.extend(i for i in imps if i.startswith("Cjson.Spec"))
for m in MAN["proof_modules"]:
    if m in reach: ok(f"proof module reachable from {CHECK}: {m}")
    else:          fail(f"proof module NOT reachable from {CHECK}: {m}")

# ---------------------------------------------------------------- released artifact untouched
ra = MAN["released_artifact_untouched"]
tag = ra["git_tag"]
for rel in ra["files"]:
    cur = subprocess.run(["git", "hash-object", rel], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    tagged = subprocess.run(["git", "rev-parse", f"{tag}:{rel}"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    if cur and cur == tagged: ok(f"released file byte-identical to {tag}: {rel}")
    else:                     fail(f"released file DIFFERS from {tag} (or missing): {rel}")

if FAIL:
    print(f"\n*** GAP-2 VERIFICATION FAILED — {len(FAIL)} problem(s) ***"); sys.exit(1)
print(f"\nGAP-2 adequacy verified: {len(ATTESTED)} declarations, axioms ⊆ {sorted(ALLOWED)}, "
      f"statements pinned, Grammar frozen, released artifact = {tag}.")
