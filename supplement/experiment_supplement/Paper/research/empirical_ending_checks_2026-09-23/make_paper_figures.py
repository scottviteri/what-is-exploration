"""Render research candidates at the current manuscript's actual 5.5-inch width."""
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FixedLocator, FuncFormatter
import numpy as np

HERE = Path(__file__).resolve().parent
d = json.loads((HERE / "COMPLETE_COMPARISON.json").read_text())
md = json.loads((HERE / "MATCHED_COMPARISON.json").read_text())
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
             weighted128="Weighted native (128)", minimax="Finite minimax")
methods = list(names)
labels = []
for i, case in enumerate(cases):
    if case.startswith("fresh"):
        _, _, seed, q, _, alpha = case.split("_")
        label = f"{q.upper()}, α={float(alpha[1:]):g}, draw {int(seed)%10+1}"
    elif case.startswith("hmm"):
        _, seed, alpha = case.split("_")
        label = f"HMM {seed}, α={float(alpha):g}"
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
    name = "CANDIDATE_22_MATCHED_PAPER" if matched else "CANDIDATE_22_PAPER"
    fig = plt.figure(figsize=(5.5, 7.6))
    gs = fig.add_gridspec(1, 3, left=.285, right=.985, top=.765, bottom=.16,
                         width_ratios=[1.05, 1, 1], wspace=.26)
    a, b, c = axes = [fig.add_subplot(gs[0,k]) for k in range(3)]
    for i, case in enumerate(cases):
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
    a.set_yticklabels(labels, fontsize=7.3)
    for ax in (b,c):
        ax.set_yticklabels([])
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
    a.set_title("(a) Audit error", fontsize=8, loc="left", pad=10, weight="bold")
    b.set_title("(b) Audit difference", fontsize=8, loc="left", pad=10, weight="bold")
    c.set_title("(c) Brier sacrifice", fontsize=8, loc="left", pad=10, weight="bold")
    a.set_xlabel("$A_{3,4}$\nlower is better", fontsize=7.5, labelpad=5)
    b.set_xlabel("control − native\npositive favors native", fontsize=7.2, labelpad=5)
    c.set_xlabel("% of reward range\nconstant: undefined", fontsize=7.2, labelpad=5)
    fig.text(.035,.976,"Different finite objectives select different evidence",fontsize=9.5,weight="bold",va="top")
    fig.text(.035,.944,"22 model classes; 3 collected interactions; all depth-4 targets audited.",fontsize=7.6)
    fig.text(.035,.921,"Both native objectives select policies using only depth-3 targets.",fontsize=7.6)
    handles=[Line2D([0],[0],marker=markers[m],color=colors[m],ls="",markersize=3.4,label=names[m]) for m in methods]
    control_marker = "matched" if matched else "brier5"
    handles.append(Line2D([0],[0],marker=markers[control_marker],color=colors[control_marker],markerfacecolor="white",ls="",markersize=3.4,label="Constrained control (b,c)"))
    fig.legend(handles=handles,ncol=2,frameon=False,loc="upper left",
               bbox_to_anchor=(.025,.909),fontsize=7.5,columnspacing=1.2,
               handletextpad=.4,labelspacing=.35)
    if matched:
        control="Matched control: native minimax with the reference's Brier reward floor."
        footer="Weighted native vs matched control: 6 wins / 1 numerical tie / 15 losses."
        marker="matched"
    else:
        control="Control in (b): native minimax with a 5%-Brier reward allowance."
        footer="Vs control: weighted 16 wins / 6 losses; minimax 18 / 1 tie / 2 / 1 mixed."
        marker="brier5"
    fig.text(.035,.064,control,fontsize=7.3)
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
    extent_reports[name]=dict(width_inches=5.5,height_inches=7.6,
                             row_label_points=7.3,body_label_points=7.5,
                             minimum_note_points=6.7,text_outside_canvas=outside,
                             cases=len(cases),matched=matched)
    for ext in ("pdf","png"):
        fig.savefig(HERE / f"{name}.{ext}", dpi=180,facecolor="white")
    plt.close(fig)
(HERE/"FIGURE_LAYOUT_CHECK.json").write_text(json.dumps(dict(
    status="passed",basis="Current iclr2027 style textwidth 5.5 true in",
    figures=extent_reports,scope="Canvas bounds and declared physical typography; human visual inspection also required."),indent=2)+"\n")
