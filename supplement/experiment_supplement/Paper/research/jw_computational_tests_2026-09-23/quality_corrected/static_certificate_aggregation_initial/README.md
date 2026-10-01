# Static in-budget certificate aggregation

The exported checkpoint attaches the lower bound available when its best incumbent was first found. The stopping rule can use a stronger later lower bound for the same unchanged objective. Thus a large exported gap alone does not show that the static solver failed to converge.

This post-design calculation aggregates all already checked, fully audited rounds available by each original budget for all eight static methods. It performs no optimization and changes no policy, reward face, budget, target, numerical witness or comparison. Adaptive moving-weight methods are excluded. Original exported gaps are retained.

Record hashes are bound through the original FILES manifest in the frozen audit queue, and the passing independent PLANNING_CHECK covers their LP bounds. This is aggregation of previously checked numerical evidence, not new exact arithmetic or a new numerical LP replay. Both original and combined evidence-availability times remain visible.

| Method | Budget | Count | Largest exported gap | Largest aggregated gap |
| --- | ---: | ---: | ---: | ---: |
| brier_face0 | 2 | 12 | 0.28588407 | 0.25459819 |
| brier_face0 | 10 | 12 | 0.28588407 | 1.4107898e-10 |
| brier_face0 | 40 | 12 | 0.28588407 | 1.4107898e-10 |
| brier_face1 | 2 | 12 | 0.10281034 | 0.005124022 |
| brier_face1 | 10 | 12 | 0.10281034 | 3.0132452e-11 |
| brier_face1 | 40 | 12 | 0.10281034 | 3.0132452e-11 |
| brier_face5 | 2 | 12 | 0.31008277 | 0.31008277 |
| brier_face5 | 10 | 12 | 0.001752953 | 4.8413902e-06 |
| brier_face5 | 40 | 12 | 0.001752953 | 7.4235438e-07 |
| fixed | 2 | 12 | 0.31159757 | 0.31130391 |
| fixed | 10 | 12 | 0.0097712178 | 0.0097712178 |
| fixed | 40 | 12 | 8.092636e-07 | 8.092636e-07 |
| information_face0 | 2 | 12 | 0.31174078 | 0.31174078 |
| information_face0 | 10 | 12 | 0.15007173 | 2.1756667e-10 |
| information_face0 | 40 | 12 | 0.15007173 | 2.1756667e-10 |
| information_face1 | 2 | 12 | 0.30809715 | 0.30809715 |
| information_face1 | 10 | 12 | 1.7843276e-05 | 1.4991342e-12 |
| information_face1 | 40 | 12 | 1.7843276e-05 | 1.4991342e-12 |
| information_face5 | 2 | 12 | 0.31234287 | 0.31234287 |
| information_face5 | 10 | 12 | 0.00051325237 | 0.00051325237 |
| information_face5 | 40 | 12 | 0.00012958916 | 4.6893132e-07 |
| minimax | 2 | 12 | 0.44227335 | 0.44227335 |
| minimax | 10 | 12 | 0.012924691 | 0.012924691 |
| minimax | 40 | 12 | 8.0353977e-07 | 8.0353977e-07 |

These are numerical upper bounds on finite training-objective regret. Small gap does not characterize every optimizer or guarantee eventual exploration. No bound is backdated to the earlier incumbent-availability time.
