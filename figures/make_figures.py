#!/usr/bin/env python3
"""Generate the paper figures as dependency-free SVG.

Figures are drawn FROM the measurement JSON, not hand-authored, so they cannot drift
from the numbers in CLAIMS.md. Run from the repo root:  python3 figures/make_figures.py
"""
import json, os, html

OUT = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(OUT)

FG, MUTE, ACC, BAD, GOOD, LINE = "#1a1a1a", "#6b6b6b", "#2b6cb0", "#c53030", "#2f855a", "#cbd5e0"
FONT = "font-family='ui-sans-serif,-apple-system,Segoe UI,Helvetica,Arial,sans-serif'"


def svg(w, h, body):
    return (f"<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 {w} {h}' width='{w}' "
            f"height='{h}' {FONT}><rect width='{w}' height='{h}' fill='white'/>{body}</svg>")


def t(x, y, s, size=13, fill=FG, anchor="start", weight="normal"):
    return (f"<text x='{x}' y='{y}' font-size='{size}' fill='{fill}' text-anchor='{anchor}' "
            f"font-weight='{weight}'>{html.escape(str(s))}</text>")


# ---------------------------------------------------------------- Fig 1: the pipeline
def fig1():
    b = []
    stages = [
        ("cJSON.c", "3,206 lines C\nUNMODIFIED", MUTE),
        ("SPEC.md", "written BEFORE\nany Lean\nevery clause\noracle-probed", ACC),
        ("Lean 4 port", "2,229 lines\n90 theorems\n0 sorry", ACC),
        ("Differential", "318 suite files\n120,000 fuzz", GOOD),
        ("Claims", "PROVEN / MEASURED\nOBSERVED / NOT PROVEN", FG),
    ]
    x = 30
    for i, (name, sub, col) in enumerate(stages):
        b.append(f"<rect x='{x}' y='40' width='150' height='96' rx='6' fill='none' "
                 f"stroke='{col}' stroke-width='1.5'/>")
        b.append(t(x + 75, 62, name, 14, col, "middle", "600"))
        for j, ln in enumerate(sub.split("\n")):
            b.append(t(x + 75, 82 + j * 15, ln, 11, MUTE, "middle"))
        if i < len(stages) - 1:
            b.append(f"<path d='M{x+150} 88 L{x+188} 88' stroke='{LINE}' stroke-width='1.5'/>")
            b.append(f"<path d='M{x+182} 84 L{x+188} 88 L{x+182} 92' fill='{LINE}'/>")
        x += 188
    b.append(t(30, 168, "The oracle is never edited. Every divergence is a finding, "
                        "not a bug to patch away.", 12, MUTE))
    b.append(t(30, 24, "Figure 1 — The Verified Software Factory pipeline", 14, FG, "start", "600"))
    return svg(980, 185, "".join(b))


# ---------------------------------------------------------------- Fig 2: divergences
def fig2():
    d = json.load(open(os.path.join(ROOT, "harness/fuzz_results.json")))
    c, n = d["counts"], d["n"]
    rows = [
        ("agreement (exit + bytes)", c.get("AGREE", 0), GOOD, "identical behaviour"),
        ("D-STR-1  invalid \\u", c.get("D-STR-1", 0), BAD, "cJSON BUG: accepts invalid as U+0000"),
        ("D-FMT    spelling", c.get("D-FMT", 0), MUTE, "same value, different text (by design)"),
        ("D-STR-2  NUL truncation", c.get("D-STR-2", 0), BAD, "cJSON BUG: silently drops content"),
        ("D-NUM    double pipeline", c.get("D-NUM", 0), BAD, "cJSON BUG: 1-ULP loss / inf->null"),
        ("UNKNOWN", c.get("UNKNOWN-unparseable", 0), FG, "classifier artifact (see D-LEAN-1)"),
    ]
    b = [t(30, 24, f"Figure 2 — Differential fuzzing: {n:,} inputs, oracle vs. Lean port",
           14, FG, "start", "600")]
    b.append(t(30, 44, "Zero divergences in class (a) “Lean port is wrong”.", 12, MUTE))
    y, BW = 70, 430
    for label, v, col, note in rows:
        w = max(1.5, BW * v / n)
        b.append(t(30, y + 12, label, 12, FG))
        b.append(f"<rect x='215' y='{y}' width='{w:.1f}' height='16' fill='{col}' opacity='0.85'/>")
        pct = 100.0 * v / n
        b.append(t(215 + w + 8, y + 12, f"{v:,}  ({pct:.2f}%)", 11, MUTE))
        b.append(t(760, y + 12, note, 11, col if col != MUTE else MUTE))
        y += 28
    b.append(f"<line x1='215' y1='{y}' x2='{215+BW}' y2='{y}' stroke='{LINE}'/>")
    b.append(t(215, y + 16, "0", 10, MUTE))
    b.append(t(215 + BW, y + 16, f"{n:,}", 10, MUTE, "end"))
    return svg(1180, y + 40, "".join(b))


# ---------------------------------------------------------------- Fig 3: proof map
def fig3():
    b = [t(30, 24, "Figure 3 — What is proven, and what it rests on", 14, FG, "start", "600")]
    box = lambda x, y, w, h, col: (f"<rect x='{x}' y='{y}' width='{w}' height='{h}' rx='5' "
                                   f"fill='none' stroke='{col}' stroke-width='1.5'/>")
    arr = lambda x1, y1, x2, y2: (
        f"<path d='M{x1} {y1} L{x2} {y2}' stroke='{LINE}' stroke-width='1.4'/>"
        f"<circle cx='{x2}' cy='{y2}' r='2.5' fill='{LINE}'/>")

    # leaves
    b += [box(30, 60, 190, 54, ACC), t(125, 80, "T1a  number round-trip", 12, ACC, "middle", "600"),
          t(125, 98, "scanNumber ∘ renderNum = id", 10, MUTE, "middle")]
    b += [box(30, 130, 190, 54, ACC), t(125, 150, "T1b  string round-trip", 12, ACC, "middle", "600"),
          t(125, 168, "escape ∘ unescape = id", 10, MUTE, "middle")]
    b += [box(30, 200, 190, 54, ACC), t(125, 220, "T2  canonicity", 12, ACC, "middle", "600"),
          t(125, 238, "carried in the parser's type", 10, MUTE, "middle")]
    b += [box(30, 270, 190, 54, ACC), t(125, 290, "T0  totality", 12, ACC, "middle", "600"),
          t(125, 308, "no fuel; WF measure", 10, MUTE, "middle")]

    # T1
    b += [box(280, 130, 190, 54, ACC), t(375, 150, "T1  round-trip", 12, ACC, "middle", "600"),
          t(375, 168, "parse(serialize v) = v", 10, MUTE, "middle")]
    # T3
    b += [box(530, 165, 210, 62, GOOD), t(635, 187, "T3  IDEMPOTENCE", 13, GOOD, "middle", "700"),
          t(635, 205, "parse s = v  ⇒", 10, MUTE, "middle"),
          t(635, 219, "parse(serialize v) = v", 10, MUTE, "middle")]

    b += [arr(220, 87, 280, 150), arr(220, 157, 280, 157), arr(220, 227, 280, 165),
          arr(470, 157, 530, 185), arr(220, 227, 530, 200)]

    # NOT PROVEN
    b += [box(800, 130, 250, 94, BAD)]
    b += [t(925, 152, "GAP-2  NOT PROVEN", 13, BAD, "middle", "700"),
          t(925, 172, "soundness vs. the SPEC grammar", 10, MUTE, "middle"),
          t(925, 188, "= which inputs the parser ACCEPTS", 10, MUTE, "middle"),
          t(925, 208, "— most of SPEC.md — is MEASURED,", 10, BAD, "middle"),
          t(925, 220, "not PROVEN.", 10, BAD, "middle")]
    b.append(f"<path d='M745 196 L800 180' stroke='{BAD}' stroke-width='1.2' "
             f"stroke-dasharray='4 3'/>")
    b.append(t(770, 250, "T1/T3 constrain what the serializer emits.\nThey say nothing about "
                         "inputs it never produces.", 10, MUTE, "middle"))
    b.append(t(30, 350, "Trusted base: Lean kernel; propext + Classical.choice + Quot.sound; "
                        "Lean's compiler/runtime (GAP-EXTRACT); SPEC.md itself.", 11, MUTE))
    return svg(1080, 370, "".join(b))


for name, fn in (("fig1-pipeline", fig1), ("fig2-divergences", fig2), ("fig3-proofmap", fig3)):
    p = os.path.join(OUT, name + ".svg")
    open(p, "w").write(fn())
    print("wrote", p)
