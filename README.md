# When Do Intrinsic Rewards Lead to Exploration?

Scott W Viteri, Laura Gomezjurado Gonzalez, and Clark Barrett — Stanford University.
Contact: scottviteri@gmail.com.

Repository: [what-is-exploration](https://github.com/scottviteri/what-is-exploration).
Evidence snapshot: [arxiv-v1](https://github.com/scottviteri/what-is-exploration/tree/arxiv-v1).
The tag identifies the companion snapshot prepared for the first arXiv submission;
it does not assert that arXiv has announced the paper. Later paper versions will
have their own tags in this same repository.

The manuscript and source ZIP on `main` include the 1 October 2026 layout
correction: appendix figures and captions fit within the page, the history
formula is displayed, and the final paragraph flows into the acknowledgements
without a nearly empty page. This reduces the PDF from 46 to 45 pages. Scientific
content and the code/data supplement are unchanged. The already-published
`arxiv-v1` tag retains its original manuscript and source ZIP.

This companion artifact contains the manuscript, the Lean sources selected for
its claims and their dependencies, and the experiment code and selected evidence.
The paper compares intrinsic rewards by the counterfactual information acquired
by their optimal policies. The finite study evaluates selected policies under
supplied response laws; it does not train agents from sampled experience.

## Read and reproduce

- [Paper with mathematical appendices](paper/paper.pdf).
- [Self-contained manuscript sources](paper/arxiv-source.zip): compile `paper.tex`
  with pdfLaTeX. The bibliography output is included.
- [Lean instructions](supplement/lean_supplement/README.md): the pinned toolchain,
  selected claim records, module dependencies, and build commands are included.
- [Experiment instructions](supplement/experiment_supplement/README.md): restore
  duplicate data paths with `python3 materialize.py`, install the pinned CPU
  requirements, and run `python3 Experiments/supplement_smoke.py` from that folder.
- [Combined supplement scope](supplement/README.md) and
  [file hashes](RELEASE_MANIFEST.json).

The scientific supplement is the frozen anonymous-review export, preserved byte
for byte. Its internal references to anonymity describe that packaging step.
The public manuscript supplies the authorship and acknowledgements. Selection is
by proof-module dependency closure and experiment study, so some supporting code
and research notes remain. The working repository's curriculum, conversation
catalog, literature PDF collection, and unrelated explorations are not included.

The package retains claim qualifications and unfavorable results. Its numerical
certificates are not Lean proofs. Exhaustive four-step target decoder banks and
large native-planning master/decomposition certificates require regeneration or
separately supplied bulk outputs. The Lean supplement has not received an
independent clean build. Hash verification establishes artifact integrity, not
scientific correctness or complete end-to-end reproduction.

## Acknowledgements and licensing

This work was supported in part by the Stanford Center for Automated Reasoning.
Scott W Viteri also acknowledges support through Manifund for earlier exploratory
research that helped shape the ideas in this paper.

The authors have not yet selected an additional reuse license for this artifact.
The manuscript's arXiv license is a separate decision. Third-party dependencies
retain their own licenses and are obtained through their package managers.
The public arXiv article link will be added after announcement.
