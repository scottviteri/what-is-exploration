"""Render the selected appendix figures from frozen summaries; no optimization.

Run from any directory with Python, NumPy, and Matplotlib. Outputs are written
alongside this renderer. Earlier editions retain their original figure files.
"""
from pathlib import Path
import json
import hashlib
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FixedLocator, FuncFormatter
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EVIDENCE = ROOT / "Paper/research/empirical_ending_checks_2026-09-23"
EXPECTED = {
    "COMPLETE_COMPARISON.json": "2f606d871c87df27f660fdd4b8ab7b0592628d09f39999d8d5cf5805c330df4a",
    "MATCHED_COMPARISON.json": "5d03059f98e6a2cdefa3fb454764513ebd9119dabdd485e73a2aa77a58dd1b34",
}
def frozen(name):
    content = (EVIDENCE / name).read_bytes()
    assert hashlib.sha256(content).hexdigest() == EXPECTED[name], name
    return json.loads(content)
d = frozen("COMPLETE_COMPARISON.json")
md = frozen("MATCHED_COMPARISON.json")
assert d["status"] == md["status"] == "passed"
cases = d["cases"]
ix = {(r["case"], r["method"]): r for r in d["points"]}
cmp = {(r["arm"], r["baseline"]): {p["case"]: p for p in r["pairs"]} for r in d["comparisons"]}
mx = {r["case"]: r for r in md["records"]}
colors = dict(information="#0072B2", brier="#D55E00", pseudo_count="#E69F00",
              uniform="#777777", weighted128="#009E73", minimax="#CC79A7",
              brier5="#333333", matched="#8c510a")
markers = dict(information="o", brier="s", pseudo_count="^", uniform="x",
               weighted128="D", minimax="P", brier5="o", matched="v")
names = dict(information="World information", brier="World-posterior Brier",
             pseudo_count="Categorical pseudo-count", uniform="Uniform actions",
             weighted128="Native mean (128 targets)", minimax="Native maximum (128 targets)")
methods = list(names)
labels = []
for i, case in enumerate(cases):
    if case.startswith("fresh"):
        _, _, seed, q, _, alpha = case.split("_")
        label = f"{q.removeprefix('q')} worlds, c={float(alpha[1:]):g}, draw {int(seed)%10+1}"
    elif case.startswith("hmm"):
        _, seed, alpha = case.split("_")
        label = f"Seed {seed}, c={float(alpha):g}"
    else:
        family, x, y = case.split("_")
        family = {"sensors": "Sensors", "delayed": "Delay", "irreversible": "Irrev."}[family]
        label = f"{family} ({float(x):g}, {float(y):g})"
    labels.append(f"{i+1:02d}  {label}")

plt.rcParams.update({"font.size": 7.5, "axes.spines.top": False,
                     "axes.spines.right": False, "pdf.fonttype": 42})
extent_reports = {}
def point(ax, lo, hi, y, method, hollow=False):
    mid = (lo + hi) / 2
    ax.errorbar(mid, y, xerr=[[mid-lo], [hi-mid]], fmt=markers[method],
                color=colors[method], markersize=2.7, capsize=1.3, elinewidth=.8,
                markerfacecolor="white" if hollow else colors[method],
                markeredgewidth=.65)

for matched in (False, True):
    name = "finite_objective_matched" if matched else "finite_objective_comparison"
    fig = plt.figure(figsize=(5.5, 6.9))
    columns = 2 if matched else 3
    gs = fig.add_gridspec(1, columns, left=.285, right=.985, top=.765, bottom=.175,
                         width_ratios=[1, 1] if matched else [1.05, 1, 1], wspace=.26)
    axes = [fig.add_subplot(gs[0,k]) for k in range(columns)]
    if matched:
        b, c = axes
    else:
        a, b, c = axes
    for i, case in enumerate(cases):
        if not matched:
            for j, method in enumerate(methods):
                r = ix[case, method]
                point(a, r["lower"], r["upper"], i+(j-2.5)*.13, method)
        if matched:
            r = mx[case]
            point(b, r["difference_lower"], r["difference_upper"], i, "weighted128")
            values = [
                ("weighted128", r["native_sacrifice"], r["native_sacrifice"]),
                ("matched", r["control_sacrifice"], r["control_sacrifice"]),
                ("minimax", ix[case,"minimax"]["brier_sacrifice_min"],
                 ix[case,"minimax"]["brier_sacrifice_max"])]
        else:
            for j, method in enumerate(("weighted128", "minimax")):
                r = cmp[method, "face_brier_0.05"][case]
                point(b, r["lower"], r["upper"], i+(j-.5)*.22, method)
            values = [(m, ix[case,k]["brier_sacrifice_min"], ix[case,k]["brier_sacrifice_max"])
                      for m,k in [("weighted128","weighted128"),("minimax","minimax"),("brier5","face_brier_0.05")]]
        for j, (m, lo, hi) in enumerate(values):
            if lo is not None:
                point(c, max(0,lo)*100, max(0,hi)*100, i+(j-1)*.2, m, hollow=m in ("brier5","matched"))
            elif j == 0:
                c.text(24, i, "constant", ha="center", va="center", fontsize=7)
        for ax in axes:
            if i % 2 == 0:
                ax.axhspan(i-.5, i+.5, color="#f3f3f3", zorder=0)
    for ax in axes:
        ax.set_ylim(21.6, -.6)
        ax.set_yticks(range(22))
        ax.tick_params(axis="y", length=0)
        ax.tick_params(axis="x", labelsize=7, length=2)
        ax.grid(axis="x", alpha=.16)
        ax.axhline(9.5, color="#888888", lw=.6)
    axes[0].set_yticklabels(labels, fontsize=7.3)
    for ax in axes[1:]:
        ax.set_yticklabels([])
    if not matched:
        a.set_xlim(-.015,.575)
        a.set_xticks([0,.25,.5])
    b.axvline(0,color="#666666",lw=.7)
    if matched:
        low=min(r["difference_lower"] for r in md["records"])
        high=max(r["difference_upper"] for r in md["records"])
        b.set_xlim(low-.004,high+.004)
        b.set_xticks([-.04,0,.04])
    else:
        b.set_xlim(-.058,.105)
        b.set_xticks([-.05,0,.05,.1])
    b.xaxis.set_major_formatter(FuncFormatter(lambda x,pos:"0" if x==0 else f"{x:.2f}".lstrip("0").replace("-0.","-.")))
    c.set_xlim(-2,51)
    c.set_xticks([0,25,50])
    if not matched:
        c.axvline(5,color="#777777",ls=":",lw=.7)
    if not matched:
        a.set_title("(a) Audit error", fontsize=8, loc="left", pad=10, weight="bold")
        a.set_xlabel("$A_{3,4}$\nlower is better", fontsize=7.5, labelpad=5)
    b.set_title("(a) Audit difference" if matched else "(b) Audit difference",
                fontsize=8, loc="left", pad=10, weight="bold")
    c.set_title("(b) Brier sacrifice" if matched else "(c) Brier sacrifice",
                fontsize=8, loc="left", pad=10, weight="bold")
    b.set_xlabel("control − native\npositive favors native", fontsize=7.2, labelpad=5)
    c.set_xlabel("% of return range\nconstant: undefined", fontsize=7.2, labelpad=5)
    fig.text(.035,.976,"Different finite objectives select different evidence",fontsize=9.5,weight="bold",va="top")
    fig.text(.035,.944,"22 world classes; 3 collected interactions; all depth-4 targets audited.",fontsize=7.6)
    fig.text(.035,.921,"Both native objectives select policies using only depth-3 targets.",fontsize=7.6)
    legend_methods = ["weighted128", "minimax"] if matched else methods
    handles=[Line2D([0],[0],marker=markers[m],color=colors[m],ls="",markersize=3.4,label=names[m]) for m in legend_methods]
    control_marker = "matched" if matched else "brier5"
    handles.append(Line2D([0],[0],marker=markers[control_marker],color=colors[control_marker],markerfacecolor="white",ls="",markersize=3.4,label="Reward-matched control" if matched else "5%-Brier control (b,c)"))
    fig.legend(handles=handles,ncol=2,frameon=False,loc="upper left",
               bbox_to_anchor=(.025,.909),fontsize=7.5,columnspacing=1.2,
               handletextpad=.4,labelspacing=.35)
    if matched:
        control="Matched control minimizes M₃ with the reference's Brier return floor."
        footer="Native mean vs matched control: 6 wins / 1 tie / 15 losses."
        marker="matched"
    else:
        control="Control in (b): minimize M₃ with a 5%-Brier return allowance."
        footer="Mean: 16 wins / 6 losses. Maximum: 18 wins / 1 tie / 2 losses / 1 mixed."
        marker="brier5"
    fig.text(.035,.071,control,fontsize=7.1)
    fig.text(.035,.039,footer,fontsize=7.3)
    fig.text(.035,.014,"Post-design; saved-policy envelopes and numerical bounds, not all-optima intervals.",fontsize=6.8)
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    texts = [t for t in fig.findobj(matplotlib.text.Text) if t.get_visible() and t.get_text()]
    outside=[]
    for t in texts:
        bb=t.get_window_extent(renderer)
        if bb.x0 < -1 or bb.y0 < -1 or bb.x1 > fig.bbox.width+1 or bb.y1 > fig.bbox.height+1:
            outside.append(t.get_text())
    assert not outside, outside
    extent_reports[name]=dict(width_inches=5.5,height_inches=6.9,
                             row_label_points=7.3,body_label_points=7.5,
                             minimum_note_points=6.7,text_outside_canvas=outside,
                             cases=len(cases),matched=matched,panels=columns)
    for ext in ("pdf",):
        fig.savefig(HERE / f"{name}.{ext}", dpi=180, facecolor="white",
                    metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)

# The budget comparison selects new policies and holds three-step references fixed.
BUDGET = ROOT / "Paper/research/simulation_time_integration_2026-09-24/RESULTS.json"
BUDGET_SHA256 = "c46d876ba1f25b3c83c2d1918013e27e257b498104e6a61874d94087389ce25e"
budget_content = BUDGET.read_bytes()
assert hashlib.sha256(budget_content).hexdigest() == BUDGET_SHA256, str(BUDGET)
r = json.loads(budget_content)
assert r["cases"] == cases and r["methods"] == methods
by = {(x["case"], x["method"], x["t"]): x for x in r["records"]}
compatibility = {x["id"]: x for x in r["compatibility"]}

def reference_error(case, method, budget, target):
    return next(a for a in by[case, method, budget]["audits"]
                if a["reference"] == target)

fig = plt.figure(figsize=(5.5, 3.0))
fig.text(.035, .985, "Return cost of reproducing a reference",
         fontsize=9, weight="bold", va="top")
handles = [Line2D([0], [0], marker=markers[m], color=colors[m], ls="",
                 markersize=3.4, label=names[m]) for m in ("brier", "information")]
fig.legend(handles=handles, ncol=2, frameon=False, loc="upper left",
           bbox_to_anchor=(.025, .936), fontsize=7.5, columnspacing=1.2,
           handletextpad=.4, labelspacing=.35)
fig.text(.035, .815, "Fresh policy at each budget; fixed three-step Brier reference in each class.",
         fontsize=7.3)
grid = fig.add_gridspec(1, 2, left=.095, right=.982, top=.690, bottom=.245,
                        wspace=.4)
g, h = axes = [fig.add_subplot(grid[0, k]) for k in range(2)]
for ax, case, method, target, title in [
        (g, "delayed_0.1_0.1", "brier", "brier", "(a) Delay (.1, .1)"),
        (h, "irreversible_0.1_0.1", "information", "brier", "(b) Irrev. (.1, .1)")]:
    values = [reference_error(case, method, t, target) for t in [3, 4, 5]]
    ax.plot([3, 4, 5], [v["upper"] for v in values], color=colors[method],
            marker=markers[method], linewidth=1, markersize=3)
    ax.axhline(.02, color="#777", linestyle=":", linewidth=.7)
    ax.set_ylim(-.008, .26)
    ax.set_yticks([0, .1, .2])
    ax.set_title(title, fontsize=7.6, loc="left", weight="bold", pad=8)
    ax.set_ylabel("Reference error", fontsize=7.2, labelpad=1)
    ax.text(.04, .94, "Brier → Brier" if method == "brier" else "Information → Brier",
            transform=ax.transAxes, fontsize=6.9, va="top")
q = compatibility["case_01__t4__brier__to_brier"]
g.plot(4, q["cap_upper"], marker="*", color="#222", markersize=6, linestyle="")
q = compatibility["case_02__t5__information__to_brier"]
h.plot(5, q["cap_upper"], marker="*", color="#222", markersize=6, linestyle="")
for ax in axes:
    ax.set_xticks([3, 4, 5])
    ax.set_xlabel("Collection budget", fontsize=7.2, labelpad=2)
    ax.tick_params(labelsize=7, length=2)
    ax.grid(alpha=.14)
fig.text(.035, .097, "Dotted line: error tolerance .02. Stars: separate reference-aware alternatives.",
         fontsize=7.1)
fig.text(.035, .049, "★ Brier loss: 0.47% of maximum gain. Information loss: numerically zero.",
         fontsize=7.1)
fig.canvas.draw()
renderer = fig.canvas.get_renderer()
outside = []
for text in fig.findobj(matplotlib.text.Text):
    if not text.get_visible() or not text.get_text():
        continue
    bounds = text.get_window_extent(renderer)
    if (bounds.x0 < -1 or bounds.y0 < -1 or bounds.x1 > fig.bbox.width + 1
            or bounds.y1 > fig.bbox.height + 1):
        outside.append(text.get_text())
assert not outside, outside
extent_reports["finite_objective_budget_summary"] = dict(
    width_inches=5.5, height_inches=3.0, minimum_note_points=6.9,
    text_outside_canvas=outside, cases=2, panels=2, fresh_policy_at_each_budget=True)
fig.savefig(HERE / "finite_objective_budget_summary.pdf", facecolor="white",
            metadata={"CreationDate": None, "ModDate": None})
plt.close(fig)

(HERE/"finite_objective_layout_check.json").write_text(json.dumps(dict(
    status="passed",source_sha256={**EXPECTED, str(BUDGET.relative_to(ROOT)): BUDGET_SHA256},basis="Current iclr2027 style textwidth 5.5 true in",
    figures=extent_reports,scope="Canvas bounds and declared physical typography; human visual inspection also required."),indent=2)+"\n")
