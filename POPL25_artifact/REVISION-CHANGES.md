## REVISIONS

Dear reviewers, we have done several revisions, based on the changes
that we have proposed, as well as some further requests. We document
all the main changes below.

We have also fixed several typos, and addressed several smaller
comments in the reviews.

In addition to the revised pdf, we also submit a pdf with the
differences to the submitted version to help you in the revision.

### PROPOSED CHANGES

The changes we have proposed are the following:


> 1. **Clarification of Type Soundness Proofs:** We will explicitly state both 
>   the direct and indirect proofs for type soundness in the introduction and 
>   Section 3.3. We will clarify the advantages of the direct proof, emphasizing 
>   its simplicity and extensibility, to address the concerns of Reviewers A and C.

We have included the figure that illustrates the type soundness proof
framework in our reply to the beginning of Section 3.3, and added
several paragraphs there to clarify the significance of a direct type
soundness proof. We have also explained in the revision that the
direct type soundness proof does not rely on weakly positive
subtyping, but just the weakly positive restriction, and can be
developed on its own.


> 2. **Enhancing Benchmark Evaluation:** We will expand the evaluation section with 
>   more detailed results and explanations. This includes rerunning benchmarks 
>   multiple times to ensure reliability, updating the results accordingly, 
>   and providing detailed hardware and software configurations used in the tests. 
>   We will also present the benchmark results in graphical formats for better 
>   clarity, as suggested by Reviewer A. Additionally, we will include an expanded 
>   discussion on the implementation details of QuickSub, particularly how freshening 
>   of variables and set unions are handled efficiently using imperative boolean arrays, 
>   addressing Reviewer C's comments.

To improve the evaluation section, we have made the following changes:

- We have expanded the beginning of Section 5 to become a
comprehensive description of our OCaml implementation, including a
functional presentation of the implementation, as well as how the
imperative boolean arrays are used to handle set unions efficiently,
as suggested by Reviewer C.

- Next, we added another paragraph after listing the comparison
algorithms to include the hardware and software configurations used in
the tests. We also make it clear that the times are the average of 10
runs excluding maximum and minimum times, as suggested by Reviewer A.

- Besides, in several places in the evaluation section, we revised the
text to make the motivation of each benchmark clearer. For example, we
highlight the significance of evaluating record types that extend in
both widths and depths at the beginning of Section 5.2, to address
Reviewer C's concerns.

- We have rerun the benchmarks and updated the tables with the new
results.

- We have changed Table 3 to graphical form, and conducted more
experiments for the curves in the new Figure 12.

> 3. **Refining Comparison with Equi-Recursive Subtyping:** We will clarify our 
>   comparison between iso-recursive and equi-recursive subtyping algorithms 
>   in the introduction, to avoid any confusion regarding the fact that equi-recursive
>   subtyping, despite being complex and less efficient than iso-recursive subtyping,
>   has been well-studied, while less attention has been given to iso-recursive subtyping,
>   addressing Reviewer B's concerns.

- We have moved the discussion on algorithmic equi-recursive subtyping
in the related work section to the introduction and expanded it to
highlight that equi-recursive subtyping has been well-studied, while
iso-recursive subtyping has received less attention.

- Furthermore, to better illustrate that the time complexity of
equi-recursive subtyping O(n^2) was measured in the number of
recursive calls by Gapeyev et al., instead of the number of
meta-operations as what we do for the rest of this paper, we have
added another Figure 9 to the discussion of the evaluation results in
Section 5.1. This figure shows that the complexity of equi-recursive
subtyping is essentially exponential in terms of meta-operations.

> 4. **Reduction of Repetition and Streamlining Content:** We will review the paper 
>   to eliminate repetition and streamline the presentation, as suggested by Reviewer A.
>   This will allow us to allocate more space to expand on the evaluation section and 
>   other key points raised in the reviews.

We have made a pass through the paper to eliminate repetition and
streamline the presentation to ensure that all the contents after the
changes above keep the paper within the page limit.


### SOME OTHER COMMENTS/CHANGES

#### Reviewer A

> In addition, from line 717, one reads ``However, it is also useful to have a
> direct proof of type soundness for QuickSub, so that developing more advanced
> features for QuickSub in the future will not depend on the development of other
> rules.'' By other rules, I expect *subtyping* rules, not typing rules.

This sentence has been replaced by several paragraphs in our first
change above, so that it is now clear that we are referring to other
iso-recursive subtyping rules.


> Real as a supertype of nat. I understand that you were looking for a base type,
> any type, that is in the subting relation with nat, in order to make the
> subtyping relation a little richer. Harper, in ``Practical Foundations for
> Programming Languages'', argues against this choice, and for good reasons.

We have added a note at the beginning of Section 5 to clarify that the
use of `Real` is specifically for benchmarking purposes and to
highlight that it is not integral to the main system.

> Benchmarking. It was not clear to me exactly which types were put to test.
> Types of depth 5000 and of depth 500, according to Table 1. But which? Reading
> Appendix A, it seems that the variety of tests is quite limited. There are 8 tests only;
> only the depth varies. Are the times given for 1 test only? Which depth? Perhaps an
> average of 8 of 10 runs (outliers excised). 

We have adopted the suggestion to rerun the benchmarks multiple times
and update the results accordingly.

> Given that the algorithm is named QuickSub,
> I was expecting testing via QuickCheck, where pairs of types would be generated from
> known laws of subtyping and the congruence rules.

We have clarified in the revised evaluation section that our testing are
generated manually instead of using tools like QuickCheck, since the
testing is more focused on evaluating the performance of the algorithm.

> l 171. ``Including reflexive subtyping'', should it be equivalent
> subtyping, as introduced in l 167?

Thank you for pointing this out. We have fixed the terminology
"reflexive subtyping" to "equivalent subtyping" here and in other
places in the revision to avoid confusion.


> l 339. ``the set of negative recursive variables in A'' and B, I suppose.

We have fixed this typo in the revision.


#### Reviewer B


> Figure 2. Notation suggestion: Instead of using \oplus and \overbar{\oplus} did you consider using \pm and \mp?

We would like to keep the current notation as $\oplus$ is meant to be
a meta-variable that can be both $+$ and $-$ modes, and
$\overline{\oplus}$ to be the negation of $\oplus$. Notations like
$\pm$ and $\mp$ can be misleading in this context, as they are usually
used for addition and subtraction, not for the modes of the subtyping
relation.

> line 481. I want to know one thing more at this point: are you
> saying that if one side is < and the other is ≈ then necessarily the
> set on ≈ will be empty? Or are you saying that it might be
> non-empty, but in that case the rule fails? [Aha, I see the next
> paragraph clarifies, but it would be nice if you rephrased this
> paragraph to clarify.]

We have rephrased the paragraph to strengthen the link between the two paragraphs.


> line 698—699. “where⊕′+⊕isthe exclusive or result of ⊕′ and ⊕.” I guess you have in mind here that + corresponds to true and - to false. Please make that clear. (Just possibly you mean the opposite, that + corresponds to false and - to true.)

We have corrected this sentence to a more explicit sentence that
explains $\oplus' + \oplus$ is $+$ when two modes are the same and $-$
when they are different.


> line 1088—1103. Table 3. Put the names of the algorithms in roman (not bold), so the listings look comparable to the other tables. (Here QuickSub looks the odd man out, because it is typeset in a monospaced font.)

The table 3 has been changed to a graphical form in the revision, so
this issue is no longer relevant.


#### Reviewer C

>   - I have one presentational comment that would *greatly* help
>     me: when presenting the QuickSub rules, it may be best to
>     present them in a more "functional" form, for example:
>       \Psi |-\sqplus T1 ? T2 ~~> \rho
>     Where the result \rho is given by: 
>       \rho ::= \bot | < | =_S
>     (where \bot means "not a subtype")
>     The reason is that in several examples you present a negative derivation
>     with a conclusion "</" which may be hard to understand. I know it is not
>     usual to include the negative cases in an inductive relation, but here
>     since this is an algorithm it might actually be helpful.
>
>   - The paper alludes to some discussion about how the freshening of
>     variables and set union happens efficiently through imperative boolean 
>     arrays, but I am not sure I located this discussion. 


We have adopted this suggestion and added a functional description of
the QuickSub algorithm in the evaluation section to better aid
explaining the algorithm and the imperative boolean array optimization
used for set unions. The missing discussion pointed out by reviewer C
has been added to the beginning evaluation section as well.

