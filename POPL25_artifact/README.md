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