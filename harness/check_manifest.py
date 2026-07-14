#!/usr/bin/env python3
"""Coverage manifest check — stops the attested set shrinking with the source.

Fails if:
  * a proof module listed in the manifest is not imported by the default build target
    (in v1.0.0 the proof modules were NOT in the default target: `lake build` was checking
    zero theorems while showing green);
  * the theorem count drifts from the manifest;
  * a pinned input's hash/commit does not match;
  * the Lean toolchain or package set drifts;
  * a canonical result file or a declared figure is missing.

The manifest<->source agreement for ATTESTED DECLARATIONS is enforced in check_axioms.py
(both directions), where the `#print axioms` evidence lives.
"""
import json, glob, hashlib, subprocess, sys, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parent.parent
MAN = json.load(open(ROOT / "release/manifest.json"))
failures = []


def chk(cond, msg):
    print(("  ok    " if cond else "  FAIL  ") + msg)
    if not cond:
        failures.append(msg)


# 1. every proof module is imported by the default build target (transitively via Cjson.lean)
root_imports = set(re.findall(r"^import\s+(\S+)", (ROOT / "lean/Cjson.lean").read_text(), re.M))
main_imports = set(re.findall(r"^import\s+(\S+)", (ROOT / "lean/Main.lean").read_text(), re.M))
chk("Cjson" in main_imports, "Main.lean imports Cjson (so `lake build` reaches the library)")
for m in MAN["proof_modules"]:
    chk(m in root_imports, f"proof module in default build target: {m}")

# 2. theorem count
lean_files = sorted(glob.glob(str(ROOT / "lean/Cjson/**/*.lean"), recursive=True)) + \
             [str(ROOT / "lean/Main.lean")]
tc = sum(1 for f in lean_files for ln in open(f)
         if ln.startswith("theorem ") or ln.startswith("@[simp] theorem "))
chk(tc == MAN["expected_theorem_count"],
    f"theorem count {tc} == manifest {MAN['expected_theorem_count']}")

# 3. pinned inputs
for rel, want in MAN["pinned_inputs"]["oracle"]["files"].items():
    got = hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
    chk(got == want, f"oracle {rel} sha256 matches pin")

corpus = ROOT / "harness/JSONTestSuite"
want_c = MAN["pinned_inputs"]["jsontestsuite"]["commit"]
if not corpus.exists():
    chk(False, "JSONTestSuite corpus present (fail closed)")
else:
    got_c = subprocess.run(["git", "rev-parse", "HEAD"], cwd=corpus,
                           capture_output=True, text=True).stdout.strip()
    chk(got_c == want_c, f"JSONTestSuite checked out at pinned commit {want_c[:12]}… (got {got_c[:12]}…)")

# 4. toolchain + packages
tc_file = (ROOT / "lean/lean-toolchain").read_text().strip()
chk(tc_file == MAN["lean_toolchain"], f"lean-toolchain == {MAN['lean_toolchain']}")
pkgs = json.load(open(ROOT / "lean/lake-manifest.json")).get("packages", [])
chk(pkgs == MAN["lean_packages"], f"lake packages == {MAN['lean_packages']} (no undeclared deps)")

# 5. declared artefacts exist
for rel in MAN["canonical_results"] + MAN["figures"] + MAN["documented_claim_files"]:
    chk((ROOT / rel).exists(), f"declared artefact present: {rel}")

if failures:
    print(f"\n*** MANIFEST CHECK FAILED — {len(failures)} problem(s) ***")
    sys.exit(1)
print("\nManifest and artifact agree.")
