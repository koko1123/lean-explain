# `GapCVP.Comparator.finitePNormGapCVPIsNPHard`

**Statement.** Let $p$ be a rational number with $p\ge 1$. Then the comparator finite $p$-norm GapCVP promise problem $\Pi_p^{\mathrm{cmp}}$ (`GapCVP.Comparator.finitePGapCVPPromise`) is NP-hard (`GapCVP.Comparator.IsNPHardPromise`), meaning: every language $A\subseteq\{0,1\}^*$ in NP admits a promise reduction to $\Pi_p^{\mathrm{cmp}}$ — a polynomial-time computable map $f$ on bit strings such that $x\in A$ implies $\Pi_p^{\mathrm{cmp}}.\mathrm{yes}(f(x))=\mathrm{true}$ and $x\notin A$ implies $\Pi_p^{\mathrm{cmp}}.\mathrm{no}(f(x))=\mathrm{true}$. Here the yes-instances of $\Pi_p^{\mathrm{cmp}}$ are the bit strings encoding a well-formed comparator instance $J$ — positive dimension, basis matrix of nonzero determinant, positive radius $r(J)$ — for which some integer vector $v$ satisfies $d_p(J,v)\le r(J)$, and its no-instances are those encoding a well-formed $J$ for which the gap factor of $J$ satisfies $\gamma_p(J)\,r(J) < d_p(J,v)$ for every integer vector $v$ (the two predicates are disjoint, which is part of the definition).

**Proof idea.** The proof transfers NP-hardness across the bookkeeping change of representation that passes from the original finite $p$-norm GapCVP problem $\Pi_p$ to the comparator version $\Pi_p^{\mathrm{cmp}}$. The two agreement lemmas show that, bit string by bit string, the comparator's yes- and no-predicates coincide with the original ones; since NP-hardness is a property of the yes/no behaviour of a promise problem, the paper's unconditional NP-hardness theorem for $\Pi_p$ (valid for every rational $p\ge 1$) carries over verbatim to $\Pi_p^{\mathrm{cmp}}$. Note that the disjointness of the comparator's yes- and no-sets, which makes it a promise problem at all, is discharged inside the definition of $\Pi_p^{\mathrm{cmp}}$, not in this proof.

1. Apply the transfer principle `isNPHardPromise_of_original`, which states that if a promise problem $Q$ has, for every bit string, the same yes-predicate and the same no-predicate as a promise problem $P$, then NP-hardness of $P$ implies NP-hardness of $Q$. The two hypotheses identifying the predicates of $\Pi_p^{\mathrm{cmp}}$ with those of the original finite $p$-norm GapCVP problem $\Pi_p$ are the yes-agreement `finiteP_yes_iff_original` (for each bit string, the comparator accepts it as a yes-instance exactly when $\Pi_p$ does, i.e. exactly when it encodes a well-formed instance $I$ with positive dimension, nonzero-determinant basis and positive radius admitting $z$ with $d_p^{\mathrm{orig}}(I,z)\le r(I)$) and the no-agreement `finiteP_no_iff_original` (the two no-languages coincide). *(lines 130418-130420)*

   <details><summary>Lean and goal state</summary>

   ```lean
     isNPHardPromise_of_original
       (finiteP_yes_iff_original p hp)
       (finiteP_no_iff_original p hp)
   ```

   </details>

2. Supply the remaining hypothesis of the transfer principle, namely NP-hardness of $\Pi_p$ itself for the given rational $p\ge 1$, which is the paper's unconditional variable-arity result `GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise`. Combined with the previous step this yields NP-hardness of $\Pi_p^{\mathrm{cmp}}$. *(lines 130421-130422)*

   <details><summary>Lean and goal state</summary>

   ```lean
       (GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise
         p hp)
   ```

   </details>

## Lemmas it uses, explained

### `GapCVP.Comparator.finiteP_no_iff_original`

**Statement.** Let $p$ be a rational number with $1\le p$ and let $\mathrm{bits}$ be a finite bit string. The comparator finite $p$-norm GapCVP promise problem $\Pi_p^{\mathrm{cmp}}$ and the original finite $p$-norm GapCVP promise problem $\Pi_p$ have the same no-language: $\mathrm{bits}$ satisfies the no-condition for $\Pi_p^{\mathrm{cmp}}$ if and only if it satisfies the no-condition for $\Pi_p$.

**Proof idea.** Both promise problems express the same no-condition, one for comparator instances and one for GapCVP instances. The map $O$ from comparator instances to GapCVP instances is surjective because $C$ is a section of it, so the original existential can be reindexed along $O$. For each comparator instance $J$, the comparator encoding and the original encoding of $O(J)$ agree, and all numeric data and conditions are copied verbatim, so the two no-conditions are equivalent.

1. Unfold the two promise problems, the two well-formedness predicates (`wellFormed` and `gapCVPWellFormed`), and rewrite `decide ... = true` as the proposition it decides. This leaves an existential over comparator instances $J$ whose comparator encoding is $\mathrm{bits}$, with $0<\dim J$, $\det B_J\ne0$, $0<r(J)$, and $\dim(J)^{(200p)^{-1}}r(J)<d_p(J,v)$ for every integer vector $v$, equivalent to an existential over GapCVP instances $I$ whose original GapCVP encoding is $\mathrm{bits}$, with $0<\dim I$, $\det B_I\ne0$, $0<r(I)$, and the same gap-factor inequality for $d_p^{\mathrm{orig}}(I,z)$ for every $z$. The `change` on line 130367 only repackages the goal as an equivalence of two explicit existential statements. *(lines 130364-130367)*

   <details><summary>Lean and goal state</summary>

   ```lean
     simp only [finitePGapCVPPromise, wellFormed,
       GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise,
       GapCVP.gapCVPWellFormed, decide_eq_true_eq]
     change (∃ _, _) ↔ ∃ _, _
   ```

   Goal before this step:

   ```
   p : ℚ
   hp : 1 ≤ p
   bits : List Bool
   ⊢ (finitePGapCVPPromise p hp).no bits = true ↔ (Factor400FinitePNormCorollary.finitePGapCVPPromise p hp).no bits = true
   ```

   </details>

2. The lemma `toOriginal_ofOriginal` states $O(C(I))=I$ for every GapCVP instance $I$, so $O$ is surjective, with $C$ as a right inverse. Applying `Function.RightInverse.surjective` and then `Function.Surjective.exists` rewrites the original-instance existential on the right as an existential over comparator instances $J$ with the original instance replaced by $O(J)$. The goal is now the comparator no-condition for $J$ if and only if the original no-condition for $O(J)$, both quantified over the same comparator instances $J$. *(lines 130368-130368)*

   <details><summary>Lean and goal state</summary>

   ```lean
     rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
   ```

   Goal before this step:

   ```
   p : ℚ
   hp : 1 ≤ p
   bits : List Bool
   ⊢ (∃ x,
         encodeInstance x = bits ∧
           (0 < x.dimension ∧ x.basis.det ≠ 0 ∧ 0 < x.radius) ∧
             ∀ (vector : Fin x.dimension → ℤ), finitePGapFactor p x * ↑x.radius < finitePLatticeDistance p x vector) ↔
       ∃ x,
         (binaryFinEncoding GapCVPInstance).encode x = bits ∧
           (0 < x.dimension ∧ x.basis.det ≠ 0 ∧ 0 < x.radius) ∧
             ∀ (z : Fin x.dimension → ℤ),
               Factor400FinitePNormCorollary.finitePGapFactor p x * ↑x.radius <
                 Factor400FinitePNormCorollary.finitePLatticeDistance p x z
   ```

   </details>

3. For a fixed comparator instance $J$, identify the two encodings: `GapCVP.binaryFinEncoding_gapCVPInstance_encode` writes the original GapCVP encoding as `BinaryEncoding.encodeGapCVPInstance`, and `encodeInstance_eq_original` identifies `BinaryEncoding.encodeGapCVPInstance (O J)` with the comparator encoding of $J$. Since $O$ copies the dimension, basis, target and radius, the remaining well-formedness, radius, gap-factor, distance, and universal-quantifier conditions are definitionally identical; `rfl` closes this pointwise equivalence. `exists_congr` then upgrades it to the equivalence of the two existential no-conditions. *(lines 130369-130372)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact exists_congr fun _ => by
       simp only [GapCVP.binaryFinEncoding_gapCVPInstance_encode,
         encodeInstance_eq_original]
       rfl
   ```

   Goal before this step:

   ```
   p : ℚ
   hp : 1 ≤ p
   bits : List Bool
   ⊢ (∃ x,
         encodeInstance x = bits ∧
           (0 < x.dimension ∧ x.basis.det ≠ 0 ∧ 0 < x.radius) ∧
             ∀ (vector : Fin x.dimension → ℤ), finitePGapFactor p x * ↑x.radius < finitePLatticeDistance p x vector) ↔
       ∃ x,
         (binaryFinEncoding GapCVPInstance).encode (toOriginal x) = bits ∧
           (0 < (toOriginal x).dimension ∧ (toOriginal x).basis.det ≠ 0 ∧ 0 < (toOriginal x).radius) ∧
             ∀ (z : Fin (toOriginal x).dimension → ℤ),
               Factor400FinitePNormCorollary.finitePGapFactor p (toOriginal x) * ↑(toOriginal x).radius <
                 Factor400FinitePNormCorollary.finitePLatticeDistance p (toOriginal x) z
   ```

   </details>

### `GapCVP.Comparator.isNPHardPromise_of_original`

**Statement.** Let $P$ be a GapCVP promise problem and $Q$ a comparator promise problem whose yes- and no-predicates agree pointwise with those of $P$, i.e. $Q.\mathrm{yes}(x)=\mathrm{true}$ iff $P.\mathrm{yes}(x)=\mathrm{true}$, and $Q.\mathrm{no}(x)=\mathrm{true}$ iff $P.\mathrm{no}(x)=\mathrm{true}$, for every bit string $x$. If $P$ is NP-hard, then $Q$ is NP-hard. Here a promise problem is a pair of Boolean predicates $\mathrm{yes},\mathrm{no}$ on bit strings (`GapCVP.PromiseProblem`, `GapCVP.Comparator.PromiseProblem`), NP-hardness of $P$ (`GapCVP.NPHardPromise`) means that every language $A\subseteq\{0,1\}^*$ in NP admits a promise reduction to $P$, and a promise reduction (`GapCVP.PromiseReduction`, `GapCVP.Comparator.PromiseReduction`) is a map $f$ on bit strings together with a polynomial-time Turing machine computing it (`Nonempty (BitTM f)`), such that $x\in A$ implies $P.\mathrm{yes}(f(x))=\mathrm{true}$ (completeness) and $x\notin A$ implies $P.\mathrm{no}(f(x))=\mathrm{true}$ (soundness). NP itself (`GapCVP.IsNP`) is the Boolean assertion that the language has a polynomial-time verifier with a polynomial bound on certificate length.

**Proof idea.** The proof is a direct transport of reductions along equivalences of promise conditions. Unfolding the `decide`-valued definition of NP-hardness turns `NPHardPromise original = true` into the statement that every NP language reduces to the original problem, and turns the goal into the corresponding statement for the comparator problem. Given an NP language $A$, the hardness of the original problem supplies a reduction $R$ from $A$ to it; the same map and the same polynomial-time machine give a reduction to the comparator problem, because its yes- and no-predicates agree pointwise with those of the original, so $R$'s completeness and soundness carry over verbatim through those equivalences.

1. Unfold the Boolean-valued definition of NP-hardness: since `GapCVP.Comparator.IsNPHardPromise` is `decide` of a proposition, the hypothesis `IsNPHardPromise problem = true` is converted into that proposition, namely that every bit language $A$ with `IsNP` admits a promise reduction to $Q$ (the rewriting is done by `decide_eq_true_eq`). Then fix an arbitrary language $A$ and assume it is in NP. *(lines 130380-130381)*

   <details><summary>Lean and goal state</summary>

   ```lean
     simp only [IsNPHardPromise, decide_eq_true_eq]
     intro language hnp
   ```

   Goal before this step:

   ```
   problem : PromiseProblem
   original : GapCVP.PromiseProblem
   hyes : ∀ (bits : List Bool), problem.yes bits = true ↔ original.yes bits = true
   hno : ∀ (bits : List Bool), problem.no bits = true ↔ original.no bits = true
   hard : NPHardPromise original = true
   ⊢ IsNPHardPromise problem = true
   ```

   </details>

2. Record the NP hypothesis on $A$ under the name `original_hnp`, and convert the hypothesis `hard : NPHardPromise original = true` into its propositional content: every bit language in NP admits a promise reduction to the original problem $P$. This is again the unfolding of a `decide`-valued definition by `decide_eq_true_eq`. *(lines 130382-130387)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have original_hnp : GapCVP.IsNP language := hnp
     have original_hard :
         ∀ language : GapCVP.BitLanguage,
           GapCVP.IsNP language →
             Nonempty (GapCVP.PromiseReduction language original) := by
       simpa only [GapCVP.NPHardPromise, decide_eq_true_eq] using hard
   ```

   Goal before this step:

   ```
   problem : PromiseProblem
   original : GapCVP.PromiseProblem
   hyes : ∀ (bits : List Bool), problem.yes bits = true ↔ original.yes bits = true
   hno : ∀ (bits : List Bool), problem.no bits = true ↔ original.no bits = true
   hard : NPHardPromise original = true
   language : BitLanguage
   hnp : IsNP language = true
   ⊢ Nonempty (PromiseReduction language problem)
   ```

   </details>

3. Apply the hardness of $P$ to the language $A$ and its NP hypothesis, obtaining a promise reduction $R$ from $A$ to $P$, with its underlying map, its polynomial-time witness, its completeness and its soundness conditions. *(lines 130388-130388)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨reduction⟩ := original_hard language original_hnp
   ```

   Goal before this step:

   ```
   problem : PromiseProblem
   original : GapCVP.PromiseProblem
   hyes : ∀ (bits : List Bool), problem.yes bits = true ↔ original.yes bits = true
   hno : ∀ (bits : List Bool), problem.no bits = true ↔ original.no bits = true
   hard : NPHardPromise original = true
   language : BitLanguage
   hnp original_hnp : IsNP language = true
   original_hard : ∀ (language : BitLanguage), IsNP language = true → Nonempty (GapCVP.PromiseReduction language original)
   ⊢ Nonempty (PromiseReduction language problem)
   ```

   </details>

4. Build a promise reduction from $A$ to $Q$ out of $R$: keep the same map and the same polynomial-time Turing machine witness, and transfer the two promise conditions across the pointwise equivalences of the predicates. Completeness: if $x\in A$ then $P.\mathrm{yes}(R(x))=\mathrm{true}$ by $R$'s completeness, and the equivalence for $\mathrm{yes}$ turns this into $Q.\mathrm{yes}(R(x))=\mathrm{true}$. Soundness: if $x\notin A$ then $P.\mathrm{no}(R(x))=\mathrm{true}$ by $R$'s soundness, and the equivalence for $\mathrm{no}$ turns this into $Q.\mathrm{no}(R(x))=\mathrm{true}$. Packaging this as an element of the (nonempty) type of promise reductions closes the goal for the arbitrary $A$, hence $Q$ is NP-hard. *(lines 130389-130396)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact ⟨{
       map := reduction.map
       polynomial_time := reduction.polynomial_time
       completeness := fun input hinput =>
         (hyes _).mpr (reduction.completeness input hinput)
       soundness := fun input hinput =>
         (hno _).mpr (reduction.soundness input hinput)
     }⟩
   ```

   Goal before this step:

   ```
   problem : PromiseProblem
   original : GapCVP.PromiseProblem
   hyes : ∀ (bits : List Bool), problem.yes bits = true ↔ original.yes bits = true
   hno : ∀ (bits : List Bool), problem.no bits = true ↔ original.no bits = true
   hard : NPHardPromise original = true
   language : BitLanguage
   hnp original_hnp : IsNP language = true
   original_hard : ∀ (language : BitLanguage), IsNP language = true → Nonempty (GapCVP.PromiseReduction language original)
   reduction : GapCVP.PromiseReduction language original
   ⊢ Nonempty (PromiseReduction language problem)
   ```

   </details>

### `GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise`

**Statement.** For every rational $p \ge 1$, the finite $p$-norm GapCVP promise problem $\Pi_p$ is NP-hard: the Boolean-valued predicate `GapCVP.NPHardPromise` holds of $\Pi_p$, that is, every NP bit language $A$ admits a promise reduction to $\Pi_p$ (a reduction that maps yes-instances of $A$ to yes-instances of $\Pi_p$ and no-instances to no-instances, and is allowed to be arbitrary on strings that are neither). Here $\Pi_p$ is the promise problem whose yes-instances are the binary encodings of well-formed GapCVP instances $I$ for which some integer vector $z$ satisfies $d_p^{\mathrm{orig}}(I,z) \le r(I)$, and whose no-instances are the encodings of well-formed $I$ with $\gamma_p(I)\,r(I) < d_p^{\mathrm{orig}}(I,z)$ for every integer vector $z$.

**Proof idea.** The proof is a direct instantiation: the project has already shown that NP-hardness of $\Pi_p$ follows from the existence of a polynomial-time machine computing the source map $f_p$, and it has separately constructed such a machine by routing the output of the canonical physical matrix computation and identifying it with $f_p$. Applying the former to the latter gives, for each rational $p \ge 1$, the NP-hardness of the finite $p$-norm GapCVP promise problem.

1. Apply the reduction theorem `paperVariableArityFiniteP_nphard_of_sourceMachine`: for a rational $p \ge 1$, any Turing machine computing the source map $f_p$ (which sends a bit string to the binary encoding of the finite $p$-norm GapCVP instance built from it) in polynomial time in the length of the binary encoding of its input yields NP-hardness of $\Pi_p$. This supplies the parameters $p$ and $p \ge 1$ and leaves the required machine as the remaining obligation. *(lines 128633-128633)*

   <details><summary>Lean and goal state</summary>

   ```lean
     paperVariableArityFiniteP_nphard_of_sourceMachine p hp
   ```

   </details>

2. Discharge that obligation with the machine `paperVariableArityFinitePSourceMapMachine p hp`. It is the Turing machine obtained from the machine computing the routed output of the canonical physical matrix shape, transported along the pointwise equality asserting that this routed output agrees with the source map $f_p$; hence it computes $f_p$. *(lines 128634-128634)*

   <details><summary>Lean and goal state</summary>

   ```lean
       (paperVariableArityFinitePSourceMapMachine p hp)
   ```

   </details>

### `GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFiniteP_nphard_of_sourceMachine`

**Statement.** Let $p \ge 1$ be a rational number, and let $M$ be a Turing machine that computes, in polynomial time with respect to the binary encoding of bit strings, the map $f_p$ (Lean: `GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFinitePSourceMap`) that sends an input string $x$ to the binary encoding of the finite $p$-norm GapCVP instance built from $x$. Then the finite $p$-norm GapCVP promise problem $\Pi_p$ (Lean: `GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise`) is NP-hard: $\Pi_p$ is a promise problem whose yes-instances are the encodings of well-formed GapCVP instances $I$ admitting an integer vector $z$ with $d_p^{\mathrm{orig}}(I,z) \le r(I)$, and whose no-instances are the encodings of well-formed $I$ with $\gamma_p(I)\, r(I) < d_p^{\mathrm{orig}}(I,z)$ for every integer vector $z$; NP-hardness means that every NP language reduces to it by a promise reduction.

**Proof idea.** This is a purely combinatory step: the work was done elsewhere. The paper's source map $f_p$ from 3SAT to the finite $p$-norm GapCVP promise problem $\Pi_p$ is certified polynomial-time by the given machine $M$, and its completeness and soundness have already been proved; feeding the NP-hardness of original 3SAT, this promise reduction, and closure of polynomial time under composition into the transfer lemma yields NP-hardness of $\Pi_p$. No instance-level argument occurs in this proof; it records that all hypotheses of the transfer lemma are discharged.

1. Apply the general transfer lemma `GapCVP.nphardPromise_of_nphard_of_promiseReduction`, which states: if a bit language $A$ is NP-hard, if there is a promise reduction from $A$ to a promise problem $P$, and if polynomial-time computable functions are closed under composition, then $P$ is NP-hard. Take $A$ to be the original 3SAT language (the bit strings encoding a 3CNF formula that has a satisfying assignment), which is NP-hard by `paperOriginalThreeSATIsNPHard`; take $P = \Pi_p$; take the closure hypothesis from `polynomialTimeClosedUnderComposition`. The reduction supplied is the one assembled by `paperVariableArityFinitePSourceReductionOfMachine` from the given machine: its underlying map is $f_p$, its polynomial-time witness is the machine $M$ itself, and its completeness and soundness components are the previously established lemmas `paperVariableArityFinitePSourceMap_completeness` and `paperVariableArityFinitePSourceMap_soundness`. The conclusion is the Boolean-valued NP-hardness assertion for $\Pi_p$. *(lines 128275-128278)*

   <details><summary>Lean and goal state</summary>

   ```lean
     nphardPromise_of_nphard_of_promiseReduction
       paperOriginalThreeSATIsNPHard
       (paperVariableArityFinitePSourceReductionOfMachine p hp machine)
       polynomialTimeClosedUnderComposition
   ```

   </details>

### `GapCVP.Comparator.finiteP_yes_iff_original`

**Statement.** Let $p$ be a rational with $p \ge 1$. For every bit string $bits$, the comparator finite-$p$-norm GapCVP promise problem accepts $bits$ exactly when the original finite-$p$-norm GapCVP promise problem accepts $bits$. A yes instance on either side consists of an instance (a comparator instance $J$ on the left, a GapCVP instance $I$ on the right) whose encoding is $bits$, whose dimension is positive, whose basis matrix has nonzero determinant, and whose radius is positive, together with an integer vector whose finite $p$-norm distance to the target is at most the radius.

**Proof idea.** The proof is a reindexing argument: the comparator problem is the original problem transported across the data-copying map from comparator instances to GapCVP instances. Since $O$ is surjective with section $C$, quantifying over original instances is the same as quantifying over comparator instances of the transported predicate. After unfolding the definitions, that transported predicate is definitionally identical, so the two yes-sets coincide.

1. Unfold both promise problems and both well-formedness predicates, and replace each Boolean test `yes bits = true` by the proposition it decides using `decide_eq_true_eq`; the `change` reshapes the result into an equivalence of two existential statements. The left existential ranges over comparator instances $J$ and uses the comparator encoding, the three well-formedness conditions $0<\dim J$, $\det B_J\ne0$, $0<r_J$, and $\exists v,\ d_p(J,v)\le r_J$. The right existential ranges over GapCVP instances $I$ and has the analogous data with the original encoding and $d_p^{\mathrm{orig}}(I,z)\le r_I$. *(lines 130350-130353)*

   <details><summary>Lean and goal state</summary>

   ```lean
     simp only [finitePGapCVPPromise, wellFormed,
       GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise,
       GapCVP.gapCVPWellFormed, decide_eq_true_eq]
     change (∃ _, _) ↔ ∃ _, _
   ```

   Goal before this step:

   ```
   p : ℚ
   hp : 1 ≤ p
   bits : List Bool
   ⊢ (finitePGapCVPPromise p hp).yes bits = true ↔
       (Factor400FinitePNormCorollary.finitePGapCVPPromise p hp).yes bits = true
   ```

   </details>

2. Since $O(C(I))=I$ for every GapCVP instance $I$ (the lemma `toOriginal_ofOriginal`), the map $O$ is surjective by `Function.RightInverse.surjective`. Rewrite the right-hand existential over GapCVP instances as an existential over comparator instances: every original instance has the form $O(J)$. The goal now has the same existential quantifier type on both sides, with the right-hand predicate transported along $O$. *(lines 130354-130354)*

   <details><summary>Lean and goal state</summary>

   ```lean
     rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
   ```

   Goal before this step:

   ```
   p : ℚ
   hp : 1 ≤ p
   bits : List Bool
   ⊢ (∃ x,
         encodeInstance x = bits ∧
           (0 < x.dimension ∧ x.basis.det ≠ 0 ∧ 0 < x.radius) ∧ ∃ vector, finitePLatticeDistance p x vector ≤ ↑x.radius) ↔
       ∃ x,
         (binaryFinEncoding GapCVPInstance).encode x = bits ∧
           (0 < x.dimension ∧ x.basis.det ≠ 0 ∧ 0 < x.radius) ∧
             ∃ z, Factor400FinitePNormCorollary.finitePLatticeDistance p x z ≤ ↑x.radius
   ```

   </details>

3. Apply `exists_congr` to reduce to a pointwise equivalence for a fixed comparator instance $J$. The encoding lemmas `GapCVP.binaryFinEncoding_gapCVPInstance_encode` and `encodeInstance_eq_original` rewrite both encoding equations to the same original binary encoding of $O(J)$. Because $O$ copies dimension, basis, target and radius, the well-formedness conditions and the two finite-$p$-norm distances become definitionally the same, so the remaining equivalence is closed by `rfl`. *(lines 130355-130358)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact exists_congr fun _ => by
       simp only [GapCVP.binaryFinEncoding_gapCVPInstance_encode,
         encodeInstance_eq_original]
       rfl
   ```

   Goal before this step:

   ```
   p : ℚ
   hp : 1 ≤ p
   bits : List Bool
   ⊢ (∃ x,
         encodeInstance x = bits ∧
           (0 < x.dimension ∧ x.basis.det ≠ 0 ∧ 0 < x.radius) ∧ ∃ vector, finitePLatticeDistance p x vector ≤ ↑x.radius) ↔
       ∃ x,
         (binaryFinEncoding GapCVPInstance).encode (toOriginal x) = bits ∧
           (0 < (toOriginal x).dimension ∧ (toOriginal x).basis.det ≠ 0 ∧ 0 < (toOriginal x).radius) ∧
             ∃ z, Factor400FinitePNormCorollary.finitePLatticeDistance p (toOriginal x) z ≤ ↑(toOriginal x).radius
   ```

   </details>

### `GapCVP.Comparator.toOriginal_ofOriginal`

**Statement.** For every GapCVP instance $I$, given by its four pieces of data (dimension, basis, target and radius), the comparator instance $C(I)$ (`GapCVP.Comparator.ofOriginal`) obtained by copying that data, converted back by $O$ (`GapCVP.Comparator.toOriginal`), is $I$ itself.

**Proof idea.** The two conversions between a GapCVP instance and a comparator instance are both field-by-field copies of the same four data, so converting to the comparator representation and back is the identity by definitional equality, discharged by reflexivity.

1. The proof is by reflexivity: both the comparator instance $C(I)$ (`GapCVP.Comparator.ofOriginal`) and the converted-back instance $O(J)$ (`GapCVP.Comparator.toOriginal`) are defined by copying the same four fields (dimension, basis, target, radius), one in each direction, so the composite $O\circ C$ returns literally the same term it started from and the two sides of the equation are definitionally equal. No case analysis or rewriting is needed. *(lines 130222-130223)*

   <details><summary>Lean and goal state</summary>

   ```lean
   @[simp] theorem toOriginal_ofOriginal (I : GapCVP.GapCVPInstance) :
       toOriginal (ofOriginal I) = I := rfl
   ```

   </details>

## Results cited without proof

- `GapCVP.Comparator.finitePGapCVPPromise`: `(p : ℚ) → 1 ≤ p → GapCVP.Comparator.PromiseProblem`
- `GapCVP.PromiseProblem.yes`: `GapCVP.PromiseProblem → GapCVP.BitLanguage`
- `GapCVP.GapCVPInstance.radius`: `GapCVP.GapCVPInstance → ℚ`
- `GapCVP.instEncodableGapCVPInstance`: `Encodable GapCVP.GapCVPInstance`
- `GapCVP.Comparator.ofOriginal`: `GapCVP.GapCVPInstance → GapCVP.Comparator.Instance`
- `GapCVP.GapCVPInstance`: `Type`
- `GapCVP.Comparator.toOriginal`: `GapCVP.Comparator.Instance → GapCVP.GapCVPInstance`
- `GapCVP.Comparator.Instance.dimension`: `GapCVP.Comparator.Instance → ℕ`
- `GapCVP.GapCVPInstance.dimension`: `GapCVP.GapCVPInstance → ℕ`
- `GapCVP.Comparator.Instance`: `Type`
- `GapCVP.Factor400FinitePNormCorollary.finitePLatticeDistance`: `ℚ → (I : GapCVP.GapCVPInstance) → (Fin I.dimension → ℤ) → ℝ`
- `GapCVP.instBinaryBitCodecGapCVPInstance`: `GapCVP.BinaryBitCodec GapCVP.GapCVPInstance`
- `GapCVP.Comparator.finitePLatticeDistance`: `ℚ → (I : GapCVP.Comparator.Instance) → (Fin I.dimension → ℤ) → ℝ`
- `GapCVP.Comparator.encodeInstance`: `GapCVP.Comparator.Instance → List Bool`
- `GapCVP.GapCVPInstance.basis`: `(self : GapCVP.GapCVPInstance) → Matrix (Fin self.dimension) (Fin self.dimension) ℤ`
- `GapCVP.Comparator.Instance.basis`: `(self : GapCVP.Comparator.Instance) → Matrix (Fin self.dimension) (Fin self.dimension) ℤ`
- `GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise`: `(p : ℚ) → 1 ≤ p → GapCVP.PromiseProblem`
- `GapCVP.Comparator.wellFormed`: `GapCVP.Comparator.Instance → Bool`
- `GapCVP.BinaryEncoding.encodeGapCVPInstance`: `GapCVP.GapCVPInstance → List Bool`
- `GapCVP.Comparator.Instance.radius`: `GapCVP.Comparator.Instance → ℚ`
- `GapCVP.gapCVPWellFormed`: `GapCVP.GapCVPInstance → Bool`
- `GapCVP.binaryFinEncoding`: `(α : Type u_1) → [Encodable α] → [GapCVP.BinaryBitCodec α] → Computability.Encoding α Bool`
- `GapCVP.Comparator.PromiseProblem.yes`: `GapCVP.Comparator.PromiseProblem → GapCVP.BitLanguage`
- `GapCVP.NPHardPromise`: `GapCVP.PromiseProblem → Bool`
- `GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePSourceMapMachine`: `(p : ℚ) → (hp : 1 ≤ p) → GapCVP.BitTM (GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFinitePSourceMap p hp)`
- `GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATIsNPHard`: `GapCVP.NPHard GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage = true`
- `GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFinitePSourceReductionOfMachine`: `(p : ℚ) → (hp : 1 ≤ p) → GapCVP.BitTM (GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFinitePSourceMap p hp) → GapCVP.PromiseReduction GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage (GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise p hp)`
- `GapCVP.BitTM`: `(List Bool → List Bool) → Type 1`
- `GapCVP.polynomialTimeClosedUnderComposition`: `GapCVP.PolynomialTimeClosedUnderComposition = true`
- `GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage`: `List Bool → Bool`
- `GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFinitePSourceMap`: `(p : ℚ) → 1 ≤ p → List Bool → List Bool`
- `GapCVP.nphardPromise_of_nphard_of_promiseReduction`: `∀ {A : GapCVP.BitLanguage} {P : GapCVP.PromiseProblem}, GapCVP.NPHard A = true → ∀ (reduction : GapCVP.PromiseReduction A P), GapCVP.PolynomialTimeClosedUnderComposition = true → GapCVP.NPHardPromise P = true`
- `GapCVP.PromiseReduction.map`: `{A : GapCVP.BitLanguage} → {P : GapCVP.PromiseProblem} → GapCVP.PromiseReduction A P → List Bool → List Bool`
- `GapCVP.IsNP`: `GapCVP.BitLanguage → Bool`
- `GapCVP.Comparator.PromiseReduction`: `GapCVP.BitLanguage → GapCVP.Comparator.PromiseProblem → Type`
- `GapCVP.Comparator.PromiseReduction.mk`: `{language : GapCVP.BitLanguage} → {problem : GapCVP.Comparator.PromiseProblem} → (map : List Bool → List Bool) → Nonempty (GapCVP.BitTM map) → (∀ (input : List Bool), language input = true → problem.yes (map input) = true) → (∀ (input : List Bool), ¬language input = true → problem.no (map input) = true) → GapCVP.Comparator.PromiseReduction language problem`
- `GapCVP.PromiseReduction.soundness`: `∀ {A : GapCVP.BitLanguage} {P : GapCVP.PromiseProblem} (self : GapCVP.PromiseReduction A P) (x : List Bool), ¬A x = true → P.no (self.map x) = true`
- `GapCVP.Comparator.PromiseProblem.no`: `GapCVP.Comparator.PromiseProblem → GapCVP.BitLanguage`
- `GapCVP.PromiseProblem`: `Type`
- `GapCVP.PromiseProblem.no`: `GapCVP.PromiseProblem → GapCVP.BitLanguage`
- `GapCVP.PromiseReduction.polynomial_time`: `∀ {A : GapCVP.BitLanguage} {P : GapCVP.PromiseProblem} (self : GapCVP.PromiseReduction A P), Nonempty (GapCVP.BitTM self.map)`
- `GapCVP.Comparator.PromiseProblem`: `Type`
- `GapCVP.BitLanguage`: `Type`
- `GapCVP.Comparator.IsNPHardPromise`: `GapCVP.Comparator.PromiseProblem → Bool`
- `GapCVP.PromiseReduction.completeness`: `∀ {A : GapCVP.BitLanguage} {P : GapCVP.PromiseProblem} (self : GapCVP.PromiseReduction A P) (x : List Bool), A x = true → P.yes (self.map x) = true`
- `GapCVP.PromiseReduction`: `GapCVP.BitLanguage → GapCVP.PromiseProblem → Type`
- `GapCVP.Comparator.finitePGapFactor`: `ℚ → GapCVP.Comparator.Instance → ℝ`
- `GapCVP.Factor400FinitePNormCorollary.finitePGapFactor`: `ℚ → GapCVP.GapCVPInstance → ℝ`
