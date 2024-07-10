# QuickSub: Efficient Iso-Recursive Subtyping

The supplementary material for the paper "QuickSub: Efficient Iso-Recursive Subtyping"
includes two parts: the Coq proof and the OCaml implementation.
Our proofs are verified in Coq version **Coq 8.13.1** and the implementation is 
tested on OCaml version **4.12.0**.


## Building Instructions

To fully test the artifact, we recommend installing Coq and OCaml via `OPAM`. 
Refer to [here](https://coq.inria.fr/opam-using.html) for detailed steps of installing Coq.
Or one could download the pre-built packages of Coq for Windows and MacOS via
[here](https://github.com/coq/coq/releases/tag/V8.13.2) and just test the proof part. 
Choose a suitable installer according to your platform.

To install Coq via `OPAM`:
```
# create a local switch for this artifact
opam switch create quicksub 4.12.0 
# update the shell environment
eval $(opam env)
# pin the Coq version to 8.13.1 and install
opam pin add coq 8.13.1
```

Our implementation relies on the `dune` build system.
```
# install dune
opam install dune
```

After testing the artifact, remove this local switch:
```
# remove the local switch
opam switch remove quicksub
```


## The Coq Proof

There are two directories in this artifact. The `linear_coq` directory contains the proofs for the main system presented in Section 3 of the paper. The `linear_coq_rcd` directory contains the proofs for the main system extended with record types in Section 4 of the paper.

The `linear_coq` and `linear_coq_rcd` share the same structure, in which all the proof files have a sequential dependency, as can be found in `_CoqProject` file of each directory. To test all the proofs, simply run `make` in the corresponding directory.

```
# test the proofs for the main system
cd linear_coq
make
```



### Key Definitions in the Paper

| Definition | File | Notation in Paper | Name in Coq
| ----- | ------- | ------ | ------
| Fig. 2. QuickSub subtyping | Rules.v | $\Psi \vdash_{\oplus} A \lessapprox B$ | `Sub` |
| Fig. 3. Weakly positive restriction                                             | PosVar.v | $\alpha \in_{\oplus} A \le B $ | `posvar` |
| Fig. 3. Weakly positive subtyping                                       | Equiv.v | $\Gamma \vdash_p A \le B $ | `sub_amber2` |
| Fig. 4. Typing           | Rules.v | $\Gamma \vdash e : A $ | `typing` |
| Fig. 4. Reduction                                    | Rules.v | $e \hookrightarrow e' $ | `step` |

Note that there are a few differences in the formalization compared to the paper:
- For the subtyping relation, in the paper we use one symbol to $\lessapprox := < | \approx_S$ to indicate both the subtyping result and the equality variable set, while in our formalization we separate them into two parameters in the `Sub` relation, and in the `Lt` case, the equality variable set is empty.
- In the formalization for the convenience of proof the `Sub` relation includes the well-formedness condition in base cases, while in the paper (as well as the implementation), we assume the well-formedness condition is satisfied and remove it from the rules.

To justify the two changes above, we formalize another relation, which has the precise correspondence to the paper version of the rules, as  `Sub2` in `AltRules.v`, and prove it to be equivalent to the `Sub` relation (assuming types and environments are well-formed) in `AltRules.v`

The weakly positive restriction and subtyping relations in `linear_coq` are directly adapted from [Zhou et al. 2022]'s [formalization](https://github.com/juda/Iso-Recursive-Subtyping/blob/3ca34c6f0c157ba085d873952d8babdbfe6b0f61/Journal/src/AmberBase.v#L77-L129). In the `linear_coq_rcd` proof we drop the subtyping relation, and extend the weakly positive restriction to consider equivalent types up to record permutation.


### Paper to Proof Table


The paper to proof contains the proofs for the main system presented in Section 3 the paper.


| Theorem | File | Name in Coq |
| ------- | ----- | ----------- |
| Theorem 3.1 Relation to weakly positive restrictions (strict subtyping)                        | PosVar.v | `soundness_posvar` |
| Theorem 3.2(1-2) Relation to weakly positive restrictions (equivalence)                     | PosVar.v | `soundness_posvar` |
| Theorem 3.2(3-4) Relation to weakly positive restrictions (equivalence) | PosVar.v | `posvar_false` |
| Theorem 3.3 Relation to weakly positive restrictions (fresh variables)      | PosVar.v | `soundness_posvar_fresh` |
| Theorem 3.4 Soundness of QuickSub to Weakly Positive Subtyping      | Equiv.v | `pos_esa_sound` |
| Theorem 3.5 QuickSub equivalence implies equality    | Variance.v | `Msub_refl_inv` |
| Theorem 3.6 Completeness of QuickSub                 | Equiv.v | `pos_esa_complete_final` |
| Lemma 3.8 Generalized completeness of QuickSub                   | Equiv.v | `pos_esa_complete` |
| Theorem 3.9 Unfolding lemma (strict subtype)   | Equiv.v | `unfolding_lemma` |
| Theorem 3.9 Unfolding lemma (equality)  | Equiv.v | `unfolding_lemma_eq` |
| Lemma 3.10 Generalized unfolding lemma        | LinearRule.v | `generalized_unfolding_lemma` |
| Theorem 3.11 Reflexivity        | LinearRule.v | `Msub_refl` |
| Theorem 3.12 Transitivity        | Transitivity.v | `trans_aux2` |
| Theorem 3.13 Progress                                         | Progress.v | `progress` |
| Theorem 3.14 Preservation                                     | Preservation.v | `preservation` |

For the system with records, the definitions and proofs can be found in a similar position as the main system.


## The OCaml Implementation

We provide the OCaml implementation for QuickSub and other algorithms 
being compared in the paper.

We also prepare several recursive type pattern generators for testing the
performance of the algorithms so that the experiments in Section 5 
can be reproduced.


### Structure of the artifact

```
./quicksub_eval
├── bin
│   ├── dune
│   └── main.ml         # The main function (requires `Cmdliner` library for command line interface)
|
└── lib
    ├── defs.ml         # Common definition of types and utility functions
    |
    ├── amberSub.ml     # The Amber Rules Implementation
    ├── completeSub.ml  # The Ligatti's Complete Subtyping Implementation
    ├── equiSub.ml      # The equi-recurive subtyping implementation
    ├── linearSubExt.ml # The direct implementation QuickSub{} algorithm, which uses functional sets
    ├── linearSubOpt.ml # The slightly optimized QuickSub{} algorithm, which uses imperative boolean arrays for equality variable sets
    ├── nominalSub.ml   # The nominal subtyping implementation
    ├── nominalSub2.ml  # The slightly optimized nominal subtyping implementation that avoids substitution on positive variables
    |
    ├── testGen.ml      # The recursive type pattern generators
    └── tests.ml        # Scripts for testing
```

### Running the evaluation

To run the implementation, first install `dune` and `cmdliner` via `OPAM`:
```
opam install dune cmdliner
```

Then, build the project:
```
dune build
```

All the algorithms and their performance can be tested by running the following command,
which basically follows the evaluation setup in Section 5 of the paper:
```
# Table 1: Time (seconds) taken for benchmarks with depth 5000 for (1) to (7) and 500 for (8).
dune exec quicksub_eval -- table1

# Figure 8: Comparison of different works across multiple tests
dune exec quicksub_eval -- plot1

# Table 2. Runtime results (seconds) for subtyping record types (depth = 100, width = 1000).
dune exec quicksub_eval -- table2

# Table 3. Runtime results (seconds) for different algorithms with varying benchmark sizes in depth and width.
dune exec quicksub_eval -- table3
```

For the commands above we set a default depth and timeout value to be smaller that what we used in the paper,
so that the tests can be finished in a reasonable time, since some ill-performing algorithms may take too 
long to finish. 

The actual evaluation in Section 5 can be run by executing the artifact with the following command line options:
```
# Table 1: Time (seconds) taken for benchmarks with depth 5000 for (1) to (7) and 500 for (8).
dune exec quicksub_eval -- table1 --depth1 5000 --max-time 100

# Figure 8: Comparison of different works across multiple tests
dune exec quicksub_eval -- plot1 --depth1 5000 --max-time 100

# Table 2. Runtime results (seconds) for subtyping record types (depth = 100, width = 1000).
dune exec quicksub_eval -- table2 --depth2 100 --width 1000 --max-time 100

# Table 3. Runtime results (seconds) for different algorithms with varying benchmark sizes in depth and width.
dune exec quicksub_eval -- table3 --max-time 100
```
