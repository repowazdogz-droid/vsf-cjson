#!/usr/bin/env python3
"""Divergence classification — shared by run_suite.py and fuzz.py.

SECOND-ORDER DEFECT FIX. In v1.0.0 the public claim "zero divergences where the Lean port
is wrong" was *inferred* from a `UNKNOWN-exit` counter that no classifier ever emitted.
There was no PORT_WRONG counter. The claim rested on the absence of an absence.

Now every differential case receives EXACTLY ONE label from this enum, and the public claim
derives directly from the PORT_WRONG counter.

  AGREE                      identical exit code and identical bytes
  PORT_WRONG                 the Lean port is at fault
  TARGET_WRONG_OR_DIFFERENT  cJSON is at fault (its IEEE-double pipeline)
  INTENTIONAL_SEMANTIC_CHANGE a divergence we chose in SPEC §S6 and approved in Phase 1
  HARNESS_ERROR              this comparator could not decide (a defect in US, not in either binary)
  UNCLASSIFIED               no rule matched — treated as a FINDING, never as a pass

HONESTY NOTE — read before quoting any number from this file.
This classification is AUTOMATIC (rule-based), but the RULES ENCODE HUMAN JUDGEMENT: they
were written by the author from the Phase-1 analysis in SPEC.md and DIVERGENCES.md. They are
not an independent oracle. Specifically, `INTENTIONAL_SEMANTIC_CHANGE` and
`TARGET_WRONG_OR_DIFFERENT` are recognised by *signatures we chose*, so a Lean bug that
happened to wear one of those signatures would be misfiled. The mitigations are:
  (1) UNCLASSIFIED is a failure-shaped outcome, not a silent bucket;
  (2) the raw (input, exit, bytes) x2 tuples are dumped so anyone can reclassify;
  (3) `PORT_WRONG` is decided by rules that do NOT depend on any such signature
      (invalid JSON out; or accepting what the oracle rejects).
This is stated in RESULTS.md and CLAIMS.md and must not be dropped.
"""
import json, re, math
from decimal import Decimal, InvalidOperation

AGREE = "AGREE"
PORT_WRONG = "PORT_WRONG"
TARGET_WRONG = "TARGET_WRONG_OR_DIFFERENT"
INTENTIONAL = "INTENTIONAL_SEMANTIC_CHANGE"
HARNESS_ERROR = "HARNESS_ERROR"
UNCLASSIFIED = "UNCLASSIFIED"

LABELS = [AGREE, PORT_WRONG, TARGET_WRONG, INTENTIONAL, HARNESS_ERROR, UNCLASSIFIED]

HEXD = b"0123456789abcdefABCDEF"
NUL_ESC = b"\\u0000"


def _syntax_ok(b):
    """Is this valid JSON *syntax*? Uses default float parsing, so it cannot raise on
    huge exponents (that is what broke the v1.0.0 classifier)."""
    try:
        json.loads(b.decode("utf-8", "surrogateescape"))
        return True
    except Exception:
        return False


def _exact(b):
    """Exact (Decimal) value tree, or None if Decimal cannot represent it."""
    try:
        return json.loads(b.decode("utf-8", "surrogateescape"),
                          parse_float=Decimal, parse_int=Decimal)
    except InvalidOperation:
        return None                      # exponent out of Decimal's range -> harness limit
    except Exception:
        return None


def _as_double(b):
    """Value tree with IEEE-double numbers. Used to test whether a divergence is EXACTLY
    double-precision loss on cJSON's side."""
    try:
        return json.loads(b.decode("utf-8", "surrogateescape"))
    except Exception:
        return None


def _bad_u_escape(inp):
    for m in re.finditer(rb"\\u", inp):
        tail = inp[m.end():m.end() + 4]
        if len(tail) < 4 or not all(c in HEXD for c in tail):
            return True
    return False


def _nul_semantics(inp, lean_out):
    """cJSON truncates C strings at NUL; we deliberately do not (SPEC §S6, D-STR-2)."""
    return (NUL_ESC in lean_out) or (NUL_ESC in inp) or (0 in inp)


# Relative tolerance used ONLY to recognise cJSON's own double-pipeline loss. cJSON's
# `compare_double` accepts ~1 ULP (DBL_EPSILON ~ 2.2e-16); we allow a few ULP (1e-15) so that
# e.g. 0.30000000000000004 -> 0.3 (relative error 1.85e-16) is recognised. THIS IS A TOLERANCE
# IN OUR CLASSIFIER AND IT IS DISCLOSED: a numeric divergence LARGER than this is never
# absorbed — it becomes UNCLASSIFIED, which is a finding. PORT_WRONG is decided by rules that
# do not use this tolerance at all.
TARGET_REL_TOL = 1e-15


def _target_lossy(o, l):
    """True iff `o` (cJSON's output) is exactly what cJSON's IEEE-double pipeline does to
    `l` (our exact output): a <=few-ULP rounding, an inf->null collapse, or an underflow->0."""
    if isinstance(o, bool) or isinstance(l, bool):
        return o == l
    if o is None and isinstance(l, (int, float)):
        return True                                  # cJSON printed `null` for inf (D-NUM-1)
    if isinstance(o, (int, float)) and isinstance(l, (int, float)):
        of, lf = float(o), float(l)
        if math.isinf(lf):
            return False                             # we have inf and cJSON printed a number
        if math.isinf(of):
            return False
        if lf == 0.0:
            return of == 0.0
        if of == 0.0:
            return True                              # cJSON underflowed to 0 (D-NUM-4)
        return abs(of - lf) <= TARGET_REL_TOL * abs(lf)
    if isinstance(o, list) and isinstance(l, list) and len(o) == len(l):
        return all(_target_lossy(a, b) for a, b in zip(o, l))
    if isinstance(o, dict) and isinstance(l, dict) and o.keys() == l.keys():
        return all(_target_lossy(o[k], l[k]) for k in o)
    return o == l


def classify(inp, oe, oo, le, lo):
    """Return exactly one label. Never returns None."""
    if oe == le and oo == lo:
        return AGREE

    # ---- rules that decide PORT_WRONG do NOT depend on any signature we chose ----
    if le == 0 and not _syntax_ok(lo):
        return PORT_WRONG                    # our binary emitted something that is not JSON
    if le == 0 and oe != 0:
        return PORT_WRONG                    # we accepted what the target rejected

    if oe != le:
        # target accepted, we rejected: legitimate ONLY for the two approved changes
        if oe == 0 and le != 0:
            if _bad_u_escape(inp):
                return INTENTIONAL           # D-STR-1: cJSON reads invalid \u as U+0000
            if _nul_semantics(inp, lo):
                return INTENTIONAL           # D-STR-2
            return PORT_WRONG                # we rejected something with no sanctioned reason
        return UNCLASSIFIED

    if oe != 0:
        return AGREE                         # both rejected; no output to compare

    # ---- both accepted, bytes differ ----
    if _nul_semantics(inp, lo):
        return INTENTIONAL                   # D-STR-2: cJSON truncated at a NUL

    if not _syntax_ok(oo):
        return TARGET_WRONG                  # cJSON emitted non-JSON

    ov_e, lv_e = _exact(oo), _exact(lo)
    if ov_e is None or lv_e is None:
        return HARNESS_ERROR                 # Decimal cannot represent it (see D-LEAN-1)
    if ov_e == lv_e:
        return INTENTIONAL                   # D-FMT: same exact value, different spelling

    ov_d, lv_d = _as_double(oo), _as_double(lo)
    if ov_d is not None and lv_d is not None and _target_lossy(ov_d, lv_d):
        return TARGET_WRONG                  # D-NUM: exactly cJSON's double-pipeline loss

    return UNCLASSIFIED
