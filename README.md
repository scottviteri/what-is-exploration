# When Do Intrinsic Rewards Lead to Exploration?

Scott W Viteri, Laura Gomezjurado Gonzalez, and Clark Barrett — Stanford University.
Contact: scottviteri@gmail.com.

This is the companion artifact for the current rebuttal revision, published on
the dated snapshot branch
[rebuttal-2026-11-17](https://github.com/scottviteri/what-is-exploration/tree/rebuttal-2026-11-17).
It contains the anonymous ICLR PDF and supplement ZIP, the named-author preprint,
selected Lean proofs, experiment code and retained evidence. Publishing this snapshot does not submit a revised paper
to ICLR or arXiv. The original [arxiv-v1 snapshot](https://github.com/scottviteri/what-is-exploration/tree/arxiv-v1)
remains fixed.

The paper compares intrinsic rewards by the counterfactual evidence acquired by
their maximizing policies. This revision uses deterministic startup and paired
observations in the alarm example, full observation blocks for empowerment, and
the specified Bayesian prediction-gain comparison. The proof package distinguishes
these results from historical constructions and supporting lemmas.

The 22-class study uses supplied-model planning. A separate two-bit pilot trains
collector, decoder and target-generator probability tables using labelled reset
samples. Its finite numerical results do not establish a convergence, scalability
or eventual native-score approximation guarantee. Favorable controls, adverse
findings, decoder limitations and data-access assumptions are retained.

## Read and reproduce

- **ICLR upload files:** [anonymous paper PDF](iclr-rebuttal/paper.pdf) and
  [anonymous supplement ZIP and reconstruction instructions](iclr-rebuttal/README.md).
  The ZIP is stored in verified parts because the publication connector limits
  individual transfers. Upload the PDF and reconstructed ZIP directly to the review system. This GitHub repository identifies the
  authors, so its URL is not an anonymous review link.
- [Named-author preprint and mathematical appendices](paper/paper.pdf).
- [Standalone manuscript source](paper/arxiv-source.zip): compile `paper.tex`
  with pdfLaTeX; the bibliography output is included.
- [Lean instructions](supplement/lean_supplement/README.md): pinned toolchain,
  selected claim records, dependencies and build commands.
- [Experiment instructions](supplement/experiment_supplement/README.md): run
  `python3 materialize.py` there to restore duplicate data paths, install the
  pinned CPU requirements, and run `python3 Experiments/supplement_smoke.py`.
  The separate learning pilot requires the documented PyTorch dependency.
- [Combined supplement scope](supplement/README.md) and [file hashes](RELEASE_MANIFEST.json).

The Lean claims retain their exact hypotheses. Numerical experiments remain
numerical evidence, apart from the explicitly identified rational-table proof.
Exhaustive four-step decoder banks, large native-planning certificates and raw
learning-pilot decoder banks require regeneration. Compact summaries, source
code, configurations and independent audit records are included.

The source package is selected by proof dependency and experiment study, so some
supporting code and research notes remain. The ICLR files have been checked for known author identifiers, identifying
links and supported metadata; two saved checkout paths were made relative.
The named preprint and its source archive retain author information. Private repository history, curriculum, conversations, literature
PDFs and unrelated research are not part of this public snapshot.

The source bytes are checked against the tested Lean package, and the extracted
experiment smoke checks and learning-pilot mechanics are checked for this release.
These checks establish their stated build, integrity and bounded-test results;
they are not a rerun of the numerical campaigns or a proof of training convergence.

## Acknowledgements and licensing

This work was supported in part by the Stanford Center for Automated Reasoning.
Scott W Viteri also acknowledges support through Manifund for earlier exploratory
research that helped shape the ideas in this paper.

The authors have not selected an additional reuse license for this artifact.
The manuscript's arXiv license is a separate decision. Third-party dependencies
retain their own licenses and are obtained through their package managers.
