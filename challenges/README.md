# Challenges in the openai-math format

Each folder here is a self-contained Lean task in the format of the
[openai-math Lean environments](https://huggingface.co/datasets/FineEnvs/openai-math), which package
results from OpenAI's [openai/math](https://github.com/openai/math) release for automatic grading:

| File | Role |
|---|---|
| `Challenge.lean` | the statement, with `sorry` where the proof goes |
| `Submission.lean` | a complete proof: the same file with every `sorry` filled in |
| `config.json` | what the grader checks: theorem names and permitted axioms |
| `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` | the grading environment: Lean 4.34.1, Mathlib `d13f23b` |

A submission scores 1 only if the theorem keeps exactly the challenge's statement, every definition the
statement uses is unchanged, the proof uses only `propext`, `Quot.sound` and `Classical.choice`, and the
Lean kernel accepts it. The official checker is [Comparator](https://github.com/leanprover/comparator),
from the Lean FRO.

## The tasks

| Folder | Source | What it says | Status |
|---|---|---|---|
| [`openai-math-honeycomb-free-energy`](openai-math-honeycomb-free-energy/) | openai-math, family 237 | For self-avoiding walks on the honeycomb lattice with an exponential tilt in the displacement, `(1/n) log Zₙ` converges, to the free energy. Splitting a walk of length `n + m` gives `Z_{n+m} ≤ Zₙ · Z_m` up to the sublattice; translation invariance reduces to two base vertices; Fekete's lemma gives the limit for the maximum over them, and a one-step comparison squeezes both. | proved |
| [`openai-math-plane-coloring`](openai-math-plane-coloring/) | openai-math, family 158 | The plane can be colored with 7 colors so that points at distance 1 always differ. [Note](../notes/plane-coloring.md) | proved |
| [`openai-math-hadamard-cube-fiber`](openai-math-hadamard-cube-fiber/) | openai-math, family 266 | A lemma on complex Hadamard matrices of order 6 whose entrywise square is also Hadamard: on the rows `i ≠ j`, if every ratio `H i k · conj(H j k)` cubes to `a` or `b`, the ratios with cube `a` sum to zero. Orthogonality gives `Σ r = 0` and `Σ r² = 0`; since `r² = r³ · conj r`, the second sum is `a · conj A + b · conj B`, which forces `A = 0`. | proved |
| [`openai-math-truffet-counterexample`](openai-math-truffet-counterexample/) | openai-math, family 104 | An explicit run of a tropical (max-plus) elimination procedure on a two-variable system: two forced steps, then it stops at a feasible point of cost 1, while another feasible point has cost 0. So the procedure's output is not optimal. | proved |
| [`pi-p-closed-form`](pi-p-closed-form/) | my master's thesis | `π_p = 2π / (p sin(π/p))` and `π_2 = π`, the constant of the one-dimensional p-Laplacian. The proof is the one in [`Portfolio/PLaplacian`](../Portfolio/PLaplacian/). | proved, offered as a task |

OpenAI's reference proofs are public; they were not consulted for any proof here.
The statements come from the release unchanged; `Challenge.lean` in each folder is byte-identical to
the dataset's copy.

## How the proofs are checked

[`check.sh`](check.sh) runs, for one folder, the checks that Comparator makes before it accepts a proof:

1. `Challenge` and `Submission` build as separate modules with the pinned Lean and Mathlib.
2. Every theorem in `config.json` depends only on the permitted axioms.
3. Every declaration of the `Challenge` module (statements of theorems, statements and bodies of
   definitions) is printed with `pp.all` from both modules, and the two printouts must be identical.
   Every implicit argument and instance is visible in that printout.

```bash
bash challenges/check.sh challenges/openai-math-plane-coloring
```

The script was also tested on failures: a `sorry` left in a proof is rejected as the axiom `sorryAx`, and
a definition rewritten from `dist x y = 1` to `1 = dist x y` is reported as a difference.

GitHub Actions runs it on every change to this folder
([`challenges.yml`](../.github/workflows/challenges.yml)). Comparator itself also replays the exported
environment through the kernel inside a sandbox. That official run has not been done yet; the script
reproduces what can be checked with Lean alone.

The statements of the openai-math tasks are © OpenAI, Apache 2.0, copied unchanged; see [`NOTICE`](NOTICE).
