# QuickSub: Efficient Iso-Recursive Subtyping

The artifact accompanying the paper *QuickSub: Efficient Iso-Recursive Subtyping* includes two parts:
1. The mechanized **Coq proof** for the QuickSub subtyping algorithm.
2. The **OCaml implementation** for the QuickSub algorithm and evaluations comparing other subtyping algorithms.

## List of Claims

- **Claim 1.** All the theorem statements in Sections 3 and 4 of the paper are mechanized and proved in Coq. The proofs will be evaluated in Step 1 and 2 of the evaluation instructions.
- **Claim 2.** In Table 1 and Figure 11 of Section 5, we test the asymptotic performance of QuickSub against other subtyping algorithms and claim that QuickSub *generally performs the best across most scenarios* except for reflexive subtyping cases and *demonstrates a linear complexity*. This will be evaluated in Step 3 of the evaluation instructions.
- **Claim 3.** In Table 2 of Section 5, we evaluate QuickSub on practical record subtyping scenarios and claim that with large widths and moderate depths, QuickSub *outperforms other algorithms*. We further vary the depth and width in Figure 12 to show that QuickSub *scales well* with increasing record sizes and recursive depths. This will be evaluated in Step 3.


## Download, Installation, and Sanity Testing

### Using Virtual Machine Image

We provide a virtual machine image with the artifact pre-installed. The VM image (`ova` file) can be downloaded from [Zenodo](https://zenodo.org/records/13906402). The VM is based on Ubuntu 20.04 and is tested on VirtualBox 7.1.2 on old (Intel) Mac machines.

Open the `ova` image using VirtualBox and use the default settings to import the VM. The VM is configured with 2 CPU cores and 4 GB of RAM. The password for the user `vboxuser` is `changeme`.

The artifact can be found on the desktop of the VM. You can jump to the *Sanity Testing* section to verify the installation. In addition, a `coqide` is pre-installed on the VM. By running `coqide` in the terminal, you can open the Coq proofs and interactively check the proofs.

> Note that the README file on Zenodo is outdated. Please refer to this README file for the most recent instructions. However, the contents in `quicksub_coq` and `quicksub_eval` directories are the same as in this repository. We recommend using the source code in this repository for the most up-to-date version of the artifact in case of any future discrepancies.

### Prerequisites

To build and test this artifact, you will need:
- For Coq proofs:
  - **Coq 8.13.1** (install via [OPAM](https://opam.ocaml.org/doc/Install.html) or from [here](https://github.com/coq/coq/releases/tag/V8.13.1))
  - Metalib Coq library (install from [here](https://github.com/plclub/metalib/releases/tag/coq8.10)) for formalizing the locally nameless representation of variables and binders.
- For OCaml implementation:
  - **OCaml 4.12.0** (install via OPAM)
  - **Dune** build system (install via OPAM)
  - OCaml **Cmdliner** library for command-line interface (install via OPAM)



### Installation Steps (from source)

The following steps will guide you through setting up the artifact from source. Alternatively, we have provided a pre-build version of the artifact in a virtual machine image. Please refer to the next section for instructions on using the VM.


1. **Install OCaml and Coq via Opam:** Please ensure you have [opam](https://opam.ocaml.org/doc/Install.html) installed. Then, run the following commands to install OCaml and Coq on a local switch:
   ```bash
   opam switch create quicksub 4.12.0
   eval $(opam env)
   opam pin add coq 8.13.1
   opam install dune cmdliner
   ```

2. **Install Metalib Coq library:** In a suitable directory, clone the Metalib library for Coq 8.10, which is compatible with Coq 8.13.1 and install it to the local switch:
   ```bash
   git clone --depth 1 --branch coq8.10 https://github.com/plclub/metalib.git
   cd metalib/Metalib
   make install
   ```

3. **Building Coq proofs:**
   In the `quicksub_coq/quick_coq` or `quicksub_coq/quick_coq_rcd` directory, run the `make` command to build the proofs.
   ```bash
   cd quicksub_coq/quick_coq
   make
   ```

4. **Building OCaml implementation:**
   In the `quicksub_eval` directory, run the `dune build` command to build the OCaml implementation.
   ```bash
   cd quicksub_eval
   dune build
   ```

5. After the evaluation, you can uninstall the local switch:
   ```bash
   opam switch remove quicksub
   ```


### Sanity Testing

For Coq proofs, run the `make` command in the `quick_coq` or `quick_coq_rcd` directory. The proofs should build without any errors. The command line output is as follows:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQC Rules.v
COQC Infra.v
COQC Variance.v
COQC PosVar.v
COQC LinearRule.v
COQC Transitivity.v
COQC Typesafety.v
```

For the OCaml implementation, by running the `dune build` command in the `quicksub_eval` directory, no output errors should be displayed. To test if the implementation is working correctly, you can run the provided test scripts as described in the evaluation instructions. For example, a quick test (with a small size of type) to generate Table 1 results can be done as follows:
```bash
dune exec quicksub_eval -- table1 --depth1 100 --max-time 1
```


## Evaluation Instructions

### Step 1: Evaluate All Coq Proofs

The proofs for the system are organized into two directories:
- `quick_coq`: Proofs for the main system (Section 3).
- `quick_coq_rcd`: Proofs for the extended system with records (Section 4).


We list the *key definitions* and the *paper-to-proof correspondence*, and describe the differences between the formalization and the paper in the **Additional Information** section below for reference. To evaluate the proofs, ensure all intermediate files are cleaned before running `make`.
```bash
# Main system proofs:
cd quick_coq
make clean
make

# Extended system proofs:
cd quick_coq_rcd
make clean
make
```

> Important Note for VM Users:
> The pre-built VM includes proofs that have been pre-compiled for faster access in `coqide`. To recompile the proofs and perform full sanity checks, execute `make clean` before running `make`.

### Step 2: Checking Axioms and Assumptions of Coq Proofs


To verify the axioms that our proofs rely on, you can use `Print Assumptions theorem_name` in Coq, by replacing `theorem_name` with the name of the theorem you want to check in the paper-to-proof table.

For example, by adding `Print Assumptions progress.` to the end of `Typesafety.v` and re-running `make`, you will see:

```coq
COQC Typesafety.v
Axioms:
JMeq_eq : forall (A : Type) (x y : A), x ~= y -> x = y
```

It should be the only axiom that the `progress` theorem relies on, which is introduced by the use of `dependent induction`.

---

To check that no axioms are introduced across the whole proof, you may run `grep -Ir "Axiom" .` under `quicksub_coq`, and nothing should be returned.

To check that all proofs have been completed, you may run `grep -Ir "Admitted\." .` under `quicksub_coq`, and nothing should be returned.

---

Alternatively, you may run `coqchk -R . Top Top.filename -o -silent` under `quick_coq` or `quick_coq_rcd` to check all the axioms we introduced in the proofs.


```
coqchk -R . Top Top.Typesafety -o -silent

CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms:
    Metalib.MetatheoryAtom.AtomSetImpl.union_3
    ...
    ...
    ...
    ...
    ...
    Metalib.MetatheoryAtom.AtomSetImpl.singleton
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
```


Except those introduced by `Lia` (the `Coq.micromega` series) or `Metalib`, the axioms we introduced from the Coq standard library are:


- `functional_extensionality_dep`
- `proof_irrelevance`
- `eq_rect_eq`
- `JMeq_eq`

These axioms are imported by `Coq.Program.Equality` for the `dependent induction` Coq tactic. The `JMeq_eq` is a corollary of `eq_rect_eq` and `eq_rect_eq` is a corollary of `proof_irrelevance`. They are mainly used for reasoning about equality of locally nameless terms and do not affect our claims.



### Step 3: OCaml Implementation Evaluation

The evaluation covers performance experiments described in Section 5 of the paper. We provide the OCaml implementation for QuickSub and other algorithms being compared in the paper in the `quicksub_eval` directory.

We also prepare several recursive type pattern generators (described in the Appendix of the paper) for testing the performance of the algorithms so that the experiments in Section 5 can be reproduced.

The structure of the OCaml implementation can be found in the **Additional Information** section below.

To evaluate the implementation and reproduce the results in the paper, you can run the following commands in the `quicksub_eval` directory:

```bash
# Full-scale Table 1 benchmark with depth 5000:
dune exec quicksub_eval -- table1 --depth1 5000 --max-time 100

# Full-scale Figure 11 comparison:
dune exec quicksub_eval -- plot1 --depth1 5000 --max-time 100

# Full-scale Table 2 runtime results for record types:
dune exec quicksub_eval -- table2 --depth2 100 --width 1000 --max-time 100

# Full-scale Figure 12 benchmark with varying sizes:
# The command also tests equi-recursive subtyping, whose results are presented in Figure 9
dune exec quicksub_eval -- table3 --max-time 100
```

**Memory and Timeout Adjustments for Benchmarks:**

The performance of computationally intensive benchmarks (e.g., Table 1 and Table 2) can vary significantly depending on the machine configuration. Here a few tips for running the benchmarks:


- **Handling Stack Overflow**: For the worst case testing scenario (e.g., Table 1, case (8)), it is possible to encounter a stack overflow error for the equi-recursive subtyping algorithm, as the algorithm is implemented by recursion and also involves a large number of type substitutions. To avoid this, we recommend running the evaluation on a local machine with a larger memory configuration, or adjust the timeout parameter to stop the recursion early, as described below.

- **Timeout Adjustments**: If a benchmark causes a stack overflow, or you do not want to wait for the full runtime, please reduce the `--max-time` parameter to a smaller value (e.g., `10` seconds). For example:
   ```bash
   dune exec quicksub_eval -- table2 --depth2 100 --width 1000 --max-time 10
   ```
   This adjustment will still produce results consistent with the claims in the paper, as the performance trend is not affected by the timeout parameter.

- **Memory Recommendations**:
  - For VirtualBox: Allocate at least **12GB of RAM** to the VM to handle large benchmarks.
  - For local machines: A system with **16GB RAM** or more is recommended for full-scale tests. For benchmarks with larger parameters (e.g., `--depth1 5000`), we **recommend running the evaluation on a local machine** to avoid VM-related slowdowns.
  
- **Type Size Adjustment**: If your machine cannot handle the full-scale benchmarks, you can reduce the depth and width of the types in the benchmarks. It should still be possible to observe a similar performance trend as described in the paper. For example, you can reduce the depth to 50 and width to 100 for Table 2:
   ```bash
   dune exec quicksub_eval -- table2 --depth2 50 --width 100 --max-time 100
   ```

Note that the overall runtime can vary depending on the machine, and the performance on the virtual machine should be slower than the data presented in the paper. It might be helpful to adopt the above strategies to obtain the results within a VM in a reasonable time frame, or alternatively, run the evaluation on a local machine for a more accurate comparison. 

The results in the paper were obtained on a MacBook Pro with a 2 GHz Quad-Core Intel Core i5 processor and 16 GB RAM using the pre-set depth and width values above.


## Additional Information

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
- In the formalization, for the convenience of proof we include the well-formedness condition in base cases of the `Sub` relation, while in the paper (as well as the implementation), we assume the well-formedness condition is satisfied and remove it from the rules.

To justify the two changes above, we formalize another relation, which has the precise correspondence to the paper version of the rules, as  `Sub2` in `AltRules.v`, and prove it to be equivalent to the `Sub` relation (assuming types and environments are well-formed) in `AltRules.v`

The weakly positive restriction and subtyping relations in `quick_coq` are directly adapted from [Zhou et al. 2022]'s [formalization](https://github.com/juda/Iso-Recursive-Subtyping/blob/3ca34c6f0c157ba085d873952d8babdbfe6b0f61/Journal/src/AmberBase.v#L77-L129). Note that the formalization is presented differently from the paper for convenience of proof, but the definitions are equivalent. A detailed justification can be found in Section 7.3 of the prior work ([Revisiting Iso-Recursive Subtyping TOPLAS'22](https://dl.acm.org/doi/10.1145/3549537)) that presents the weakly positive rule.

In the `quick_coq_rcd` proof we drop the subtyping relation, and extend the weakly positive restriction to consider equivalent types up to record permutation.


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
| Theorem 3.9 Unfolding lemma (strict subtype)   | LinearRule.v.v | `unfolding_lemma` |
| Theorem 3.9 Unfolding lemma (equality)  | LinearRule.v.v | `unfolding_lemma_eq` |
| Lemma 3.10 Generalized unfolding lemma        | LinearRule.v | `generalized_unfolding_lemma` |
| Theorem 3.11 Reflexivity        | LinearRule.v | `Msub_refl` |
| Theorem 3.12 Transitivity        | Transitivity.v | `trans_aux2` |
| Theorem 3.13 Progress                                         | TypeSafety.v | `progress` |
| Theorem 3.14 Preservation                                     | TypeSafety.v | `preservation` |

For the system with records, the definitions and proofs can be found in a similar position as the main system.




### Structure of the OCaml Implementation
The OCaml implementation is structured as follows:

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
    ├── equiSub.ml      # The equi-recursive subtyping implementation
    ├── quickSubExt.ml # The direct implementation QuickSub{} algorithm, which uses functional sets
    ├── quickSubOpt.ml # The slightly optimized QuickSub{} algorithm, which uses imperative boolean arrays for equality variable sets
    ├── nominalSub.ml   # The nominal subtyping implementation
    ├── nominalSub2.ml  # The slightly optimized nominal subtyping implementation that avoids substitution on positive variables
    |
    ├── testGen.ml      # The recursive type pattern generators
    └── tests.ml        # Scripts for testing
```


## Reusability Notes

### Licensing

This artifact is released under the MIT License. This license allows for open-source usage, modification, and distribution of the provided source code. For detailed terms, see the LICENSE file included in this repository.

The MIT License permits:

- Use of the artifact for both personal and commercial purposes.
- Modification and redistribution under the same license.
- Attribution to the original authors when redistributing.

If you have questions regarding the licensing or require additional permissions, please contact the authors.


### Code Extensibility

The OCaml implementation in `quicksub_eval` is structured for extensibility, allowing researchers to adapt and extend the subtyping algorithms provided. Key components include:

- `defs.ml`: Definitions of types and utility functions used across the implementation.
- Modular subtyping implementations (e.g., `quickSubOpt.ml`, `amberSub.ml`).
- Test generators (`testGen.ml`) to evaluate the performance under various recursive type patterns.
- You can experiment with the algorithm interactively using `dune utop`. Load the modules listed above, and test the subtyping algorithms with your own defined types. Use the constructors provided in the `Defs` module to construct these types.

For a detailed description of each module, please refer to the in-code comments.

We also encourage researchers to extend the Coq proofs in `quicksub_coq` to cover additional subtyping algorithms or extensions to the `QuickSub` algorithm. Our formalization shares a similar infrastructure with the following projects:

- Revisiting Iso-Recursive Subtyping: [GitHub](https://github.com/juda/Iso-Recursive-Subtyping)
- A Calculus with Recursive Types, Record Concatenation and Subtyping: [Zenodo](https://doi.org/10.5281/zenodo.7003284)
- Recursive Subtyping for All: [GitHub](https://github.com/juda/Recursive-Subtyping-for-All)
- Full Iso-Recursive Types: [GitHub](https://github.com/ltzone/Full-Iso-Recursive-Types)