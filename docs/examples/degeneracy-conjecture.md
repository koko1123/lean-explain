# `TwoDegenerateGraphs.not_erdos_146`

**Statement.** The degeneracy conjecture of Erdős is false. The conjecture (`TwoDegenerateGraphs.DegeneracyConjectureStatement`) asserts that for every real $r>0$, every $q$, and every simple graph $H$ on $q$ vertices that is bipartite and $r$-degenerate, the extremal number satisfies $\operatorname{ex}(n,H) = O\bigl(n^{\,2-1/r}\bigr)$ as $n\to\infty$, where $\operatorname{ex}(n,H)$ is the largest number of edges of an $H$-free graph on $n$ vertices. The theorem proves the negation of that assertion.

**Proof idea.** Assume the degeneracy conjecture. The project's counterexample produces a bipartite 2-degenerate graph $H$ with $\operatorname{ex}(n,H)\ge c\,n^{3/2+\varepsilon}$ for large $n$, while the conjecture with $r=2$ gives $\operatorname{ex}(n,H)\le C\,n^{3/2}$. Combined with the elementary fact that $C+1\le c\,n^{\varepsilon}$ eventually, this means that for large $n$ both $(C+1)\,n^{3/2}\le c\,n^{\varepsilon}\,n^{3/2} = c\,n^{3/2+\varepsilon}$ and $c\,n^{\varepsilon}\,n^{3/2}\le C\,n^{3/2}$ hold, which is impossible because $n^{3/2}>0$. Hence the conjecture fails.

1. Argue by contradiction: assume the degeneracy conjecture and aim for a contradiction. *(lines 18545-18545)*

   <details><summary>Lean and goal state</summary>

   ```lean
     intro hconjecture
   ```

   Goal before this step:

   ```
   ⊢ ¬DegeneracyConjectureStatement
   ```

   </details>

2. Invoke the project's counterexample result `TwoDegenerateGraphs.twoDegenerateExtremalCounterexample`: it supplies a natural number $q$ and a graph $H$ on $q$ vertices that is connected, bipartite and 2-degenerate, together with real constants $c>0$ and $\varepsilon>0$ such that $c\,n^{3/2+\varepsilon}\le \operatorname{ex}(n,H)$ for all sufficiently large $n$. (The result also carries a condition on the degrees in each colour class of every 2-colouring of $H$; it is not used here.) *(lines 18546-18547)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨q, H, _hconnected, hbipartite, hdegenerate, _hdegree,
       c, ε, hc, hε, hlower⟩ := twoDegenerateExtremalCounterexample
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   ⊢ False
   ```

   </details>

3. Apply the conjectured statement to this $H$ with $r=2$ (the side condition $0<2$ is discharged by `norm_num`). Since $H$ is bipartite and 2-degenerate, this gives $\operatorname{ex}(n,H) = O\bigl(n^{\,2-1/2}\bigr)$. *(lines 18548-18549)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hbigO := hconjecture 2 q H (by norm_num)
       hbipartite hdegenerate
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   q : ℕ
   H : SimpleGraph (Fin q)
   _hconnected : H.Connected
   hbipartite : H.IsBipartite
   hdegenerate : IsTwoDegenerate H
   _hdegree :
     ∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex
   c ε : ℝ
   hc : 0 < c
   hε : 0 < ε
   hlower : ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   ⊢ False
   ```

   </details>

4. Unpack the big-O assertion `Asymptotics.isBigO_iff`: there is a constant $C$ with $|\operatorname{ex}(n,H)|\le C\,\bigl|n^{\,2-1/2}\bigr|$ for all sufficiently large $n$. *(lines 18550-18550)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨C, hupper⟩ := Asymptotics.isBigO_iff.mp hbigO
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   q : ℕ
   H : SimpleGraph (Fin q)
   _hconnected : H.Connected
   hbipartite : H.IsBipartite
   hdegenerate : IsTwoDegenerate H
   _hdegree :
     ∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex
   c ε : ℝ
   hc : 0 < c
   hε : 0 < ε
   hlower : ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   hbigO : (fun n => ↑(extremalNumber n H)) =O[atTop] fun n => ↑n ^ (↑2 - 1 / ↑2)
   ⊢ False
   ```

   </details>

5. Turn this into a norm-free eventual bound: for all sufficiently large $n$, $\operatorname{ex}(n,H)\le C\,n^{3/2}$. Both sides are nonnegative (an extremal number and a nonnegative real power of $n$), so the absolute values can be dropped, and the exponent $2-1/2$ is replaced by $3/2$ (`norm_num`). *(lines 18551-18566)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hupper' :
         ∀ᶠ n : ℕ in Filter.atTop,
           (SimpleGraph.extremalNumber n H : ℝ) ≤
             C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
       filter_upwards [hupper] with n hn
       have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
       have hextremal_nonneg :
           (0 : ℝ) ≤ (SimpleGraph.extremalNumber n H : ℝ) :=
         Nat.cast_nonneg _
       have hnormalized :
           (SimpleGraph.extremalNumber n H : ℝ) ≤
             C * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) := by
         simpa only [Real.norm_eq_abs, abs_of_nonneg hextremal_nonneg,
           abs_of_nonneg (Real.rpow_nonneg hnnonneg _), Nat.cast_ofNat] using hn
       convert hnormalized using 1
       norm_num
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   q : ℕ
   H : SimpleGraph (Fin q)
   _hconnected : H.Connected
   hbipartite : H.IsBipartite
   hdegenerate : IsTwoDegenerate H
   _hdegree :
     ∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex
   c ε : ℝ
   hc : 0 < c
   hε : 0 < ε
   hlower : ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   hbigO : (fun n => ↑(extremalNumber n H)) =O[atTop] fun n => ↑n ^ (↑2 - 1 / ↑2)
   C : ℝ
   hupper : ∀ᶠ (x : ℕ) in atTop, ‖↑(extremalNumber x H)‖ ≤ C * ‖↑x ^ (↑2 - 1 / ↑2)‖
   ⊢ False
   ```

   </details>

6. Apply the auxiliary lemma `CompactnessConjecture.eventually_constant_le_positive_nat_rpow` (for $a,e>0$ one has $b\le a\,n^{e}$ for all large $n$) with constants $C+1$, $c$ and $\varepsilon$: eventually $C+1\le c\,n^{\varepsilon}$. *(lines 18567-18569)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hlarge :=
       CompactnessConjecture.eventually_constant_le_positive_nat_rpow
         (C + 1) c ε hc hε
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   q : ℕ
   H : SimpleGraph (Fin q)
   _hconnected : H.Connected
   hbipartite : H.IsBipartite
   hdegenerate : IsTwoDegenerate H
   _hdegree :
     ∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex
   c ε : ℝ
   hc : 0 < c
   hε : 0 < ε
   hlower : ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   hbigO : (fun n => ↑(extremalNumber n H)) =O[atTop] fun n => ↑n ^ (↑2 - 1 / ↑2)
   C : ℝ
   hupper : ∀ᶠ (x : ℕ) in atTop, ‖↑(extremalNumber x H)‖ ≤ C * ‖↑x ^ (↑2 - 1 / ↑2)‖
   hupper' : ∀ᶠ (n : ℕ) in atTop, ↑(extremalNumber n H) ≤ C * ↑n ^ (3 / 2)
   ⊢ False
   ```

   </details>

7. Show that falsity holds eventually by intersecting the four eventual statements: the lower bound $c\,n^{3/2+\varepsilon}\le\operatorname{ex}(n,H)$, the upper bound $\operatorname{ex}(n,H)\le C\,n^{3/2}$, the bound $C+1\le c\,n^{\varepsilon}$, and $n>0$. For such an $n$, the number $n^{3/2}$ is positive, the identity $c\,n^{3/2+\varepsilon} = (c\,n^{\varepsilon})\,n^{3/2}$ holds by $n^{x+y}=n^{x}n^{y}$ for positive $n$, and multiplying $C+1\le c\,n^{\varepsilon}$ by the nonnegative factor $n^{3/2}$ gives $(C+1)\,n^{3/2}\le (c\,n^{\varepsilon})\,n^{3/2}$. *(lines 18570-18582)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have himpossible : ∀ᶠ n : ℕ in Filter.atTop, False := by
       filter_upwards [hlower, hupper', hlarge,
         Filter.eventually_gt_atTop 0] with n hlow hupp hlarge_n hn
       have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
       have hscale : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) :=
         Real.rpow_pos_of_pos hnreal _
       have hdecompose :
           c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) =
             (c * (n : ℝ) ^ ε) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
         rw [Real.rpow_add hnreal]
         ring
       rw [hdecompose] at hlow
       have hscaled := mul_le_mul_of_nonneg_right hlarge_n hscale.le
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   q : ℕ
   H : SimpleGraph (Fin q)
   _hconnected : H.Connected
   hbipartite : H.IsBipartite
   hdegenerate : IsTwoDegenerate H
   _hdegree :
     ∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex
   c ε : ℝ
   hc : 0 < c
   hε : 0 < ε
   hlower : ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   hbigO : (fun n => ↑(extremalNumber n H)) =O[atTop] fun n => ↑n ^ (↑2 - 1 / ↑2)
   C : ℝ
   hupper : ∀ᶠ (x : ℕ) in atTop, ‖↑(extremalNumber x H)‖ ≤ C * ‖↑x ^ (↑2 - 1 / ↑2)‖
   hupper' : ∀ᶠ (n : ℕ) in atTop, ↑(extremalNumber n H) ≤ C * ↑n ^ (3 / 2)
   hlarge : ∀ᶠ (n : ℕ) in atTop, C + 1 ≤ c * ↑n ^ ε
   ⊢ False
   ```

   </details>

8. Combine the chain $c\,n^{\varepsilon}n^{3/2}\le \operatorname{ex}(n,H)\le C\,n^{3/2}$ with $(C+1)\,n^{3/2}\le c\,n^{\varepsilon}n^{3/2}$; linear arithmetic in the quantities involved yields the contradiction. *(lines 18583-18583)*

   <details><summary>Lean and goal state</summary>

   ```lean
       nlinarith
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   q : ℕ
   H : SimpleGraph (Fin q)
   _hconnected : H.Connected
   hbipartite : H.IsBipartite
   hdegenerate : IsTwoDegenerate H
   _hdegree :
     ∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex
   c ε : ℝ
   hc : 0 < c
   hε : 0 < ε
   hlower : ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   hbigO : (fun n => ↑(extremalNumber n H)) =O[atTop] fun n => ↑n ^ (↑2 - 1 / ↑2)
   C : ℝ
   hupper : ∀ᶠ (x : ℕ) in atTop, ‖↑(extremalNumber x H)‖ ≤ C * ‖↑x ^ (↑2 - 1 / ↑2)‖
   hupper' : ∀ᶠ (n : ℕ) in atTop, ↑(extremalNumber n H) ≤ C * ↑n ^ (3 / 2)
   hlarge : ∀ᶠ (n : ℕ) in atTop, C + 1 ≤ c * ↑n ^ ε
   n : ℕ
   hlow : c * ↑n ^ ε * ↑n ^ (3 / 2) ≤ ↑(extremalNumber n H)
   hupp : ↑(extremalNumber n H) ≤ C * ↑n ^ (3 / 2)
   hlarge_n : C + 1 ≤ c * ↑n ^ ε
   hn : 0 < n
   hnreal : 0 < ↑n
   hscale : 0 < ↑n ^ (3 / 2)
   hdecompose : c * ↑n ^ (3 / 2 + ε) = c * ↑n ^ ε * ↑n ^ (3 / 2)
   hscaled : (C + 1) * ↑n ^ (3 / 2) ≤ c * ↑n ^ ε * ↑n ^ (3 / 2)
   ⊢ False
   ```

   </details>

9. An event that holds eventually and is never true forces a contradiction: a filter that is eventually `False` contains the empty set, so `False` follows. *(lines 18584-18584)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact himpossible.exists.elim (fun _ h => h)
   ```

   Goal before this step:

   ```
   hconjecture : DegeneracyConjectureStatement
   q : ℕ
   H : SimpleGraph (Fin q)
   _hconnected : H.Connected
   hbipartite : H.IsBipartite
   hdegenerate : IsTwoDegenerate H
   _hdegree :
     ∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex
   c ε : ℝ
   hc : 0 < c
   hε : 0 < ε
   hlower : ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   hbigO : (fun n => ↑(extremalNumber n H)) =O[atTop] fun n => ↑n ^ (↑2 - 1 / ↑2)
   C : ℝ
   hupper : ∀ᶠ (x : ℕ) in atTop, ‖↑(extremalNumber x H)‖ ≤ C * ‖↑x ^ (↑2 - 1 / ↑2)‖
   hupper' : ∀ᶠ (n : ℕ) in atTop, ↑(extremalNumber n H) ≤ C * ↑n ^ (3 / 2)
   hlarge : ∀ᶠ (n : ℕ) in atTop, C + 1 ≤ c * ↑n ^ ε
   himpossible : ∀ᶠ (n : ℕ) in atTop, False
   ⊢ False
   ```

   </details>

## Lemmas it uses, explained

### `TwoDegenerateGraphs.twoDegenerateExtremalCounterexample`

**Statement.** There exist a natural number $q$ and a simple graph $H$ on $\mathrm{Fin}(q)$ such that: $H$ is connected, bipartite and 2-degenerate; for every 2-colouring of $H$ (Lean's `H.Coloring (Fin 2)`, i.e. a colouring by a two-element type that is proper across edges) and for each of the two colours $s$, the supremum of the degrees of the vertices of colour $s$ is greater than $2$; and there are real constants $c>0$ and $\epsilon>0$ such that $c\,n^{3/2+\epsilon}\le\operatorname{ex}(n,H)$ for all sufficiently large $n$.

**Proof idea.** The proof converts an existing asymptotic statement into a single explicit counterexample. From it one extracts a base size $B\ge4$ and a depth $d>0$ (with $dW/2>1$) such that $\operatorname{ex}(M(n),G_{B,d})\ge M(n)^{p}$ eventually, where $p=3/2+\eta$; a detour through $U-\ell=W$, $\ell>0$, $U<1$ gives $W<1$ and hence $d>2$, supplying the hypotheses needed later. The witnesses are $q=|V_{B,d}|$ and $H=G_{B,d}$: connectivity, bipartiteness and 2-degeneracy are read off from the pair construction, and the colouring hypothesis (each colour class in any 2-colouring contains a vertex of degree at least $3$) is exactly the corresponding property of $G_{B,d}$. The remaining claim is the growth estimate with $c=2^{-p}$ and $\epsilon=\eta$: an arbitrary large $n$ is bracketed as $M(k)\le n<M(k+1)\le 2M(k)$ with $k\ge\mathit{minimum}$, so $n^{p}\le (2M(k))^{p}=2^{p}M(k)^{p}$, the factor $2^{p}$ being cancelled by $c$; monotonicity of the extremal number in the number of vertices, available because $G_{B,d}$ has no isolated vertices, upgrades $M(k)^{p}\le\operatorname{ex}(M(k),G_{B,d})$ to a bound at $n$. Thus $\operatorname{ex}(n,H)$ exceeds $n^{3/2+\eta}$ up to a constant, ruling out an $O(n^{3/2})$ bound for this connected bipartite 2-degenerate $H$.

1. Start from the asymptotic input `eventually_manuscriptVertexCount_power_le_extremalNumber`: there are natural numbers $B\ge 4$ and $d>0$ with $1<dW/2$ such that, for all sufficiently large $n$, $M(n)^{p}\le \operatorname{ex}(M(n),G_{B,d})$, where $p=3/2+\eta$ and $M(n)=\lceil 3\,r(n)2^{n}\rceil$. Fix such $B$ and $d$ for the rest of the proof. *(lines 18454-18457)*

   <details><summary>Lean and goal state</summary>

   ```lean
     classical
     obtain ⟨baseSize, depth, hbase, hdepth,
       hdepth_window, hsubsequence⟩ :=
       eventually_manuscriptVertexCount_power_le_extremalNumber
   ```

   Goal before this step:

   ```
   ⊢ ∃ q H,
       H.Connected ∧
         H.IsBipartite ∧
           IsTwoDegenerate H ∧
             (∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
                 2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex) ∧
               ∃ c ε, 0 < c ∧ 0 < ε ∧ ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   ```

   </details>

2. Since $U-\ell=W$ (`entropyWindow_eq_certifiedWindowWidth`) while $\ell>0$ and $U<1$, we have $W<1$, hence $0\le d(1-W)$. Combined with $1<dW/2$, this forces $d>2$: recorded first over the reals, then as $2<d$ and $2\le d$ for the natural number $d$. These inequalities are what the connectivity and colouring results below require. *(lines 18458-18469)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hwidth : certifiedWindowWidth < 1 := by
       rw [← entropyWindow_eq_certifiedWindowWidth]
       linarith [entropyLowerEndpoint_pos, entropyUpperEndpoint_lt_one]
     have hproduct :
         0 ≤ (depth : ℝ) * (1 - certifiedWindowWidth) :=
       mul_nonneg (Nat.cast_nonneg depth) (sub_nonneg.mpr hwidth.le)
     have hdepth_real : (2 : ℝ) < (depth : ℝ) := by
       nlinarith
     have hdepth_nat : 2 < depth := by
       exact_mod_cast hdepth_real
     have hdepth_two : 2 ≤ depth := by
       omega
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   ⊢ ∃ q H,
       H.Connected ∧
         H.IsBipartite ∧
           IsTwoDegenerate H ∧
             (∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
                 2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex) ∧
               ∃ c ε, 0 < c ∧ 0 < ε ∧ ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   ```

   </details>

3. Name the graph $G_{B,d}$ (`forbidden`), and record that it has no isolated vertices: every vertex has a neighbour, by `pairGraphOverFin_forall_exists_adj` applied with $B\ge4$ and $d>0$. *(lines 18470-18477)*

   <details><summary>Lean and goal state</summary>

   ```lean
     let forbidden :
         SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
       pairGraphOverFin baseSize depth
     have hnoisolated :
         ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
           ∃ neighbor, forbidden.Adj vertex neighbor := by
       exact pairGraphOverFin_forall_exists_adj
         baseSize depth hbase hdepth
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   ⊢ ∃ q H,
       H.Connected ∧
         H.IsBipartite ∧
           IsTwoDegenerate H ∧
             (∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
                 2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex) ∧
               ∃ c ε, 0 < c ∧ 0 < ε ∧ ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   ```

   </details>

4. Produce the witnesses: $q=|V_{B,d}|$ and $H=G_{B,d}$, together with connectivity (`pairGraphOverFin_connected`, whose side condition $0<B$ is discharged from $B\ge4$), bipartiteness (`pairGraphOverFin_isBipartite`), 2-degeneracy (`pairGraphOverFin_isTwoDegenerate`), and the constants $c=2^{-p}$ and $\epsilon=\eta$. Three obligations are left: the colouring condition, the positivity of $c$, and the eventual lower bound for $\operatorname{ex}(n,G_{B,d})$. *(lines 18478-18484)*

   <details><summary>Lean and goal state</summary>

   ```lean
     refine ⟨Fintype.card (PairVertex baseSize depth), forbidden,
       pairGraphOverFin_connected baseSize depth (by omega) hdepth,
       pairGraphOverFin_isBipartite baseSize depth,
       pairGraphOverFin_isTwoDegenerate baseSize depth,
       ?_,
       1 / (2 : ℝ) ^ manuscriptExtremalPower,
       exponentGain, ?_, exponentGain_pos, ?_⟩
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   ⊢ ∃ q H,
       H.Connected ∧
         H.IsBipartite ∧
           IsTwoDegenerate H ∧
             (∀ (coloring : H.Coloring (Fin 2)) (side : Fin 2),
                 2 < {vertex | coloring vertex = side}.sup fun vertex => H.degree vertex) ∧
               ∃ c ε, 0 < c ∧ 0 < ε ∧ ∀ᶠ (n : ℕ) in atTop, c * ↑n ^ (3 / 2 + ε) ≤ ↑(extremalNumber n H)
   ```

   </details>

5. The colouring condition follows from `pairGraphOverFin_bipartition_maximum_degree_gt_two` with $B\ge4$ and $d\ge2$: in every 2-colouring of $G_{B,d}$ and on either side, some vertex of that colour has degree greater than $2$ (at least $3$). *(lines 18485-18487)*

   <details><summary>Lean and goal state</summary>

   ```lean
     · simpa only [forbidden] using
         pairGraphOverFin_bipartition_maximum_degree_gt_two
           baseSize depth hbase hdepth_two
   ```

   Goal before this step:

   ```
   case refine_1
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   ⊢ ∀ (coloring : forbidden.Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => forbidden.degree vertex
   ```

   </details>

6. The constant is positive: $c=1/2^{p}>0$ because $2^{p}>0$. *(lines 18488-18489)*

   <details><summary>Lean and goal state</summary>

   ```lean
     · exact one_div_pos.mpr
         (Real.rpow_pos_of_pos (by norm_num) manuscriptExtremalPower)
   ```

   Goal before this step:

   ```
   case refine_2
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   ⊢ 0 < 1 / 2 ^ manuscriptExtremalPower
   ```

   </details>

7. Turn the eventual statement into an explicit threshold: `Filter.eventually_atTop` gives a number $\mathit{minimum}$ with $M(b)^{p}\le\operatorname{ex}(M(b),G_{B,d})$ for every $b\ge\mathit{minimum}$. It therefore suffices to prove $c\,n^{p}\le\operatorname{ex}(n,G_{B,d})$ for every $n\ge M(\mathit{minimum})$. *(lines 18490-18494)*

   <details><summary>Lean and goal state</summary>

   ```lean
     · obtain ⟨minimum, hminimum⟩ :=
         Filter.eventually_atTop.1 hsubsequence
       apply Filter.eventually_atTop.2
       refine ⟨manuscriptVertexCount minimum, ?_⟩
       intro n hn
   ```

   Goal before this step:

   ```
   case refine_3
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   ⊢ ∀ᶠ (n : ℕ) in atTop, 1 / 2 ^ manuscriptExtremalPower * ↑n ^ (3 / 2 + exponentGain) ≤ ↑(extremalNumber n forbidden)
   ```

   </details>

8. Bracket $n$ between two consecutive values of $M$: by `exists_manuscriptVertexCount_bracket`, applied to $\mathit{minimum}$ and $n\ge M(\mathit{minimum})$, there is a dimension $k\ge\mathit{minimum}$ with $M(k)\le n<M(k+1)$. *(lines 18495-18496)*

   <details><summary>Lean and goal state</summary>

   ```lean
       obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
         exists_manuscriptVertexCount_bracket minimum n hn
   ```

   Goal before this step:

   ```
   case refine_3
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   minimum : ℕ
   hminimum :
     ∀ (b : ℕ),
       minimum ≤ b →
         ↑(manuscriptVertexCount b) ^ manuscriptExtremalPower ≤
           ↑(extremalNumber (manuscriptVertexCount b) (pairGraphOverFin baseSize depth))
   n : ℕ
   hn : manuscriptVertexCount minimum ≤ n
   ⊢ 1 / 2 ^ manuscriptExtremalPower * ↑n ^ (3 / 2 + exponentGain) ≤ ↑(extremalNumber n forbidden)
   ```

   </details>

9. Two consequences. First, $M(k+1)\le 2M(k)$ (`manuscriptVertexCount_succ_le_two_mul`), so the bracketing gives $n\le 2M(k)$ and hence $n\le 2M(k)$ over the reals. Second, the threshold at $b=k$ (legitimate since $k\ge\mathit{minimum}$) gives $M(k)^{p}\le\operatorname{ex}(M(k),G_{B,d})$. *(lines 18497-18506)*

   <details><summary>Lean and goal state</summary>

   ```lean
       have hdouble :=
         manuscriptVertexCount_succ_le_two_mul dimension
       have hn_bound :
           n ≤ 2 * manuscriptVertexCount dimension := by
         omega
       have hn_real :
           (n : ℝ) ≤
             2 * (manuscriptVertexCount dimension : ℝ) := by
         exact_mod_cast hn_bound
       have hsubseq := hminimum dimension hdimension
   ```

   Goal before this step:

   ```
   case refine_3
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   minimum : ℕ
   hminimum :
     ∀ (b : ℕ),
       minimum ≤ b →
         ↑(manuscriptVertexCount b) ^ manuscriptExtremalPower ≤
           ↑(extremalNumber (manuscriptVertexCount b) (pairGraphOverFin baseSize depth))
   n : ℕ
   hn : manuscriptVertexCount minimum ≤ n
   dimension : ℕ
   hdimension : minimum ≤ dimension
   hbelow : manuscriptVertexCount dimension ≤ n
   habove : n < manuscriptVertexCount (dimension + 1)
   ⊢ 1 / 2 ^ manuscriptExtremalPower * ↑n ^ (3 / 2 + exponentGain) ≤ ↑(extremalNumber n forbidden)
   ```

   </details>

10. Monotonicity in the number of vertices: since $G_{B,d}$ has no isolated vertices and $M(k)\le n$, `CompactnessConjecture.extremalNumber_monotone_of_no_isolated` gives $\operatorname{ex}(M(k),G_{B,d})\le\operatorname{ex}(n,G_{B,d})$. *(lines 18507-18512)*

   <details><summary>Lean and goal state</summary>

   ```lean
       have hmonotone :
           SimpleGraph.extremalNumber
               (manuscriptVertexCount dimension) forbidden ≤
             SimpleGraph.extremalNumber n forbidden :=
         CompactnessConjecture.extremalNumber_monotone_of_no_isolated
           forbidden hnoisolated hbelow
   ```

   Goal before this step:

   ```
   case refine_3
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   minimum : ℕ
   hminimum :
     ∀ (b : ℕ),
       minimum ≤ b →
         ↑(manuscriptVertexCount b) ^ manuscriptExtremalPower ≤
           ↑(extremalNumber (manuscriptVertexCount b) (pairGraphOverFin baseSize depth))
   n : ℕ
   hn : manuscriptVertexCount minimum ≤ n
   dimension : ℕ
   hdimension : minimum ≤ dimension
   hbelow : manuscriptVertexCount dimension ≤ n
   habove : n < manuscriptVertexCount (dimension + 1)
   hdouble : manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   hn_bound : n ≤ 2 * manuscriptVertexCount dimension
   hn_real : ↑n ≤ 2 * ↑(manuscriptVertexCount dimension)
   hsubseq :
     ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
       ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   ⊢ 1 / 2 ^ manuscriptExtremalPower * ↑n ^ (3 / 2 + exponentGain) ≤ ↑(extremalNumber n forbidden)
   ```

   </details>

11. Rewrite the goal, replacing the exponent $3/2+\eta$ of the statement by the single symbol $p$ (`manuscriptExtremalPower`, definitionally $3/2+\eta$). *(lines 18513-18516)*

   <details><summary>Lean and goal state</summary>

   ```lean
       change
         (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
             (n : ℝ) ^ manuscriptExtremalPower ≤
           (SimpleGraph.extremalNumber n forbidden : ℝ)
   ```

   Goal before this step:

   ```
   case refine_3
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   minimum : ℕ
   hminimum :
     ∀ (b : ℕ),
       minimum ≤ b →
         ↑(manuscriptVertexCount b) ^ manuscriptExtremalPower ≤
           ↑(extremalNumber (manuscriptVertexCount b) (pairGraphOverFin baseSize depth))
   n : ℕ
   hn : manuscriptVertexCount minimum ≤ n
   dimension : ℕ
   hdimension : minimum ≤ dimension
   hbelow : manuscriptVertexCount dimension ≤ n
   habove : n < manuscriptVertexCount (dimension + 1)
   hdouble : manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   hn_bound : n ≤ 2 * manuscriptVertexCount dimension
   hn_real : ↑n ≤ 2 * ↑(manuscriptVertexCount dimension)
   hsubseq :
     ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
       ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hmonotone : extremalNumber (manuscriptVertexCount dimension) forbidden ≤ extremalNumber n forbidden
   ⊢ 1 / 2 ^ manuscriptExtremalPower * ↑n ^ (3 / 2 + exponentGain) ≤ ↑(extremalNumber n forbidden)
   ```

   </details>

12. First link of the chain: $c\,n^{p}\le c\,(2M(k))^{p}$, because $0\le n\le 2M(k)$ and $x\mapsto x^{p}$ is monotone on non-negative reals (`Real.rpow_le_rpow`, using $p\ge0$), multiplied by the non-negative constant $c$. *(lines 18517-18527)*

   <details><summary>Lean and goal state</summary>

   ```lean
       calc
         (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
             (n : ℝ) ^ manuscriptExtremalPower ≤
           (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
             (2 * (manuscriptVertexCount dimension : ℝ)) ^
               manuscriptExtremalPower := by
             apply mul_le_mul_of_nonneg_left
             · exact Real.rpow_le_rpow
                 (Nat.cast_nonneg n) hn_real
                 manuscriptExtremalPower_pos.le
             · positivity
   ```

   Goal before this step:

   ```
   case refine_3
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   minimum : ℕ
   hminimum :
     ∀ (b : ℕ),
       minimum ≤ b →
         ↑(manuscriptVertexCount b) ^ manuscriptExtremalPower ≤
           ↑(extremalNumber (manuscriptVertexCount b) (pairGraphOverFin baseSize depth))
   n : ℕ
   hn : manuscriptVertexCount minimum ≤ n
   dimension : ℕ
   hdimension : minimum ≤ dimension
   hbelow : manuscriptVertexCount dimension ≤ n
   habove : n < manuscriptVertexCount (dimension + 1)
   hdouble : manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   hn_bound : n ≤ 2 * manuscriptVertexCount dimension
   hn_real : ↑n ≤ 2 * ↑(manuscriptVertexCount dimension)
   hsubseq :
     ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
       ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hmonotone : extremalNumber (manuscriptVertexCount dimension) forbidden ≤ extremalNumber n forbidden
   ⊢ 1 / 2 ^ manuscriptExtremalPower * ↑n ^ manuscriptExtremalPower ≤ ↑(extremalNumber n forbidden)
   ```

   </details>

13. The constant absorbs the factor $2$: $(2M(k))^{p}=2^{p}M(k)^{p}$ (`Real.mul_rpow`), so $c\,(2M(k))^{p}=2^{-p}\cdot 2^{p}\cdot M(k)^{p}=M(k)^{p}$, using $2^{p}\ne0$. *(lines 18528-18536)*

   <details><summary>Lean and goal state</summary>

   ```lean
         _ = (manuscriptVertexCount dimension : ℝ) ^
               manuscriptExtremalPower := by
             rw [Real.mul_rpow (by norm_num)
               (Nat.cast_nonneg (manuscriptVertexCount dimension))]
             have htwo :
                 (2 : ℝ) ^ manuscriptExtremalPower ≠ 0 :=
               (Real.rpow_pos_of_pos (by norm_num)
                 manuscriptExtremalPower).ne'
             field_simp [htwo]
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   minimum : ℕ
   hminimum :
     ∀ (b : ℕ),
       minimum ≤ b →
         ↑(manuscriptVertexCount b) ^ manuscriptExtremalPower ≤
           ↑(extremalNumber (manuscriptVertexCount b) (pairGraphOverFin baseSize depth))
   n : ℕ
   hn : manuscriptVertexCount minimum ≤ n
   dimension : ℕ
   hdimension : minimum ≤ dimension
   hbelow : manuscriptVertexCount dimension ≤ n
   habove : n < manuscriptVertexCount (dimension + 1)
   hdouble : manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   hn_bound : n ≤ 2 * manuscriptVertexCount dimension
   hn_real : ↑n ≤ 2 * ↑(manuscriptVertexCount dimension)
   hsubseq :
     ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
       ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hmonotone : extremalNumber (manuscriptVertexCount dimension) forbidden ≤ extremalNumber n forbidden
   ⊢ 1 / 2 ^ manuscriptExtremalPower * (2 * ↑(manuscriptVertexCount dimension)) ^ manuscriptExtremalPower =
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower
   ```

   </details>

14. Close the chain: $M(k)^{p}\le\operatorname{ex}(M(k),G_{B,d})$ is the threshold inequality from the bracketing step, and $\operatorname{ex}(M(k),G_{B,d})\le\operatorname{ex}(n,G_{B,d})$ is the monotonicity step, read over the reals. This proves $c\,n^{p}\le\operatorname{ex}(n,H)$ for all $n\ge M(\mathit{minimum})$, i.e. the required eventual bound with $\epsilon=\eta$. *(lines 18537-18541)*

   <details><summary>Lean and goal state</summary>

   ```lean
         _ ≤ (SimpleGraph.extremalNumber
               (manuscriptVertexCount dimension) forbidden : ℝ) :=
             hsubseq
         _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by
             exact_mod_cast hmonotone
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hsubsequence :
     ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hwidth : certifiedWindowWidth < 1
   hproduct : 0 ≤ ↑depth * (1 - certifiedWindowWidth)
   hdepth_real : 2 < ↑depth
   hdepth_nat : 2 < depth
   hdepth_two : 2 ≤ depth
   forbidden : SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) := pairGraphOverFin baseSize depth
   hnoisolated : ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))), ∃ neighbor, forbidden.Adj vertex neighbor
   minimum : ℕ
   hminimum :
     ∀ (b : ℕ),
       minimum ≤ b →
         ↑(manuscriptVertexCount b) ^ manuscriptExtremalPower ≤
           ↑(extremalNumber (manuscriptVertexCount b) (pairGraphOverFin baseSize depth))
   n : ℕ
   hn : manuscriptVertexCount minimum ≤ n
   dimension : ℕ
   hdimension : minimum ≤ dimension
   hbelow : manuscriptVertexCount dimension ≤ n
   habove : n < manuscriptVertexCount (dimension + 1)
   hdouble : manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   hn_bound : n ≤ 2 * manuscriptVertexCount dimension
   hn_real : ↑n ≤ 2 * ↑(manuscriptVertexCount dimension)
   hsubseq :
     ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
       ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   hmonotone : extremalNumber (manuscriptVertexCount dimension) forbidden ≤ extremalNumber n forbidden
   ⊢ ↑(extremalNumber (manuscriptVertexCount dimension) forbidden) ≤ ↑(extremalNumber n forbidden)
   ```

   </details>

### `TwoDegenerateGraphs.manuscriptVertexCount_succ_le_two_mul`

**Statement.** Let $d$ be a natural number, let $\beta = (\ell+U)/2$ be the midpoint of the entropy endpoints, let $r(d) = \exp(-\beta d \log 2)$ be the Hamming retention probability at dimension $d$ (`hammingRetentionProbability`, written $r(d)$), and let $M(d) = \lceil 3\,r(d)\,2^{d}\rceil$ be the manuscript vertex count at dimension $d$ (`manuscriptVertexCount`, written $M(d)$). Then $M(d+1) \le 2\,M(d)$.

**Proof idea.** The vertex count $M(d)$ is governed by the product $r(d)\,2^{d}$, and `hammingRetentionProbability_mul_wordCount_eq_exp` exhibits that product in closed form as $\exp((1-\beta)d\log 2)$. Moving from dimension $d$ to $d+1$ therefore multiplies it by the constant factor $\exp((1-\beta)\log 2)$, which is at most $2$ because $\beta > 0$. Hence $3\,r(d+1)\,2^{d+1} \le 2\cdot 3\,r(d)\,2^{d} \le 2\,\lceil 3\,r(d)\,2^{d}\rceil$, and passing back through the ceiling (via `Nat.ceil_le`) yields $M(d+1) \le 2\,M(d)$.

1. Record the factor bound $\exp((1-\beta)\log 2) \le 2$. Since $\beta > 0$ (`midpointBeta_pos`) and $\log 2 > 0$ (`log_two_pos`), linear arithmetic gives $(1-\beta)\log 2 \le \log 2$; monotonicity of the exponential turns this into $\exp((1-\beta)\log 2) \le \exp(\log 2)$, and $\exp(\log 2) = 2$ since $2 > 0$. *(lines 18355-18362)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hfactor :
         Real.exp ((1 - midpointBeta) * Real.log 2) ≤ (2 : ℝ) := by
       calc
         Real.exp ((1 - midpointBeta) * Real.log 2) ≤
             Real.exp (Real.log 2) := by
           apply Real.exp_le_exp.mpr
           nlinarith [mul_pos midpointBeta_pos log_two_pos]
         _ = 2 := Real.exp_log (by norm_num)
   ```

   Goal before this step:

   ```
   dimension : ℕ
   ⊢ manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   ```

   </details>

2. Establish the exact recurrence $r(d+1)\,2^{d+1} = \exp((1-\beta)\log 2)\cdot\big(r(d)\,2^{d}\big)$. The lemma `hammingRetentionProbability_mul_wordCount_eq_exp` rewrites each product $r(n)\,2^{n}$ as $\exp\big((1-\beta)n\log 2\big)$, and the exponential addition law $\exp(a)\exp(b)=\exp(a+b)$ (used backwards) combines them; what is left is the identity $(1-\beta)(d+1)\log 2 = (1-\beta)\log 2 + (1-\beta)d\log 2$, which follows after casting $d+1$ to the reals and expanding. *(lines 18363-18374)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hrecurrence :
         hammingRetentionProbability (dimension + 1) *
             ((2 ^ (dimension + 1) : ℕ) : ℝ) =
           Real.exp ((1 - midpointBeta) * Real.log 2) *
             (hammingRetentionProbability dimension *
               ((2 ^ dimension : ℕ) : ℝ)) := by
       rw [hammingRetentionProbability_mul_wordCount_eq_exp,
         hammingRetentionProbability_mul_wordCount_eq_exp,
         ← Real.exp_add]
       congr 1
       push_cast
       ring
   ```

   Goal before this step:

   ```
   dimension : ℕ
   hfactor : Real.exp ((1 - midpointBeta) * Real.log 2) ≤ 2
   ⊢ manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   ```

   </details>

3. Unfold $M$ and remove the ceiling: for a real $x$ and a natural $n$, $\lceil x\rceil \le n$ iff $x \le n$ (`Nat.ceil_le`), so the goal becomes $3\,r(d+1)\,2^{d+1} \le 2\,\lceil 3\,r(d)\,2^{d}\rceil$, the right-hand side having been put in the form $2\cdot\lceil\cdot\rceil$ with the natural-number cast pushed inside. *(lines 18375-18377)*

   <details><summary>Lean and goal state</summary>

   ```lean
     unfold manuscriptVertexCount
     apply Nat.ceil_le.mpr
     norm_num only [Nat.cast_mul, Nat.cast_ofNat]
   ```

   Goal before this step:

   ```
   dimension : ℕ
   hfactor : Real.exp ((1 - midpointBeta) * Real.log 2) ≤ 2
   hrecurrence :
     hammingRetentionProbability (dimension + 1) * ↑(2 ^ (dimension + 1)) =
       Real.exp ((1 - midpointBeta) * Real.log 2) * (hammingRetentionProbability dimension * ↑(2 ^ dimension))
   ⊢ manuscriptVertexCount (dimension + 1) ≤ 2 * manuscriptVertexCount dimension
   ```

   </details>

4. Rewrite the left-hand side $3\,r(d+1)\,2^{d+1}$ as $\exp((1-\beta)\log 2)\cdot\big(3\,r(d)\,2^{d}\big)$: pull the factor $3$ out, apply the recurrence from the previous step, and reassociate the product. *(lines 18378-18390)*

   <details><summary>Lean and goal state</summary>

   ```lean
     calc
       3 * hammingRetentionProbability (dimension + 1) *
           ((2 ^ (dimension + 1) : ℕ) : ℝ) =
         Real.exp ((1 - midpointBeta) * Real.log 2) *
           (3 * hammingRetentionProbability dimension *
             ((2 ^ dimension : ℕ) : ℝ)) := by
           rw [show
             3 * hammingRetentionProbability (dimension + 1) *
                 ((2 ^ (dimension + 1) : ℕ) : ℝ) =
               3 * (hammingRetentionProbability (dimension + 1) *
                 ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring,
             hrecurrence]
           ring
   ```

   Goal before this step:

   ```
   dimension : ℕ
   hfactor : Real.exp ((1 - midpointBeta) * Real.log 2) ≤ 2
   hrecurrence :
     hammingRetentionProbability (dimension + 1) * ↑(2 ^ (dimension + 1)) =
       Real.exp ((1 - midpointBeta) * Real.log 2) * (hammingRetentionProbability dimension * ↑(2 ^ dimension))
   ⊢ 3 * hammingRetentionProbability (dimension + 1) * ↑(2 ^ (dimension + 1)) ≤
       2 * ↑⌈3 * hammingRetentionProbability dimension * ↑(2 ^ dimension)⌉₊
   ```

   </details>

5. Apply the factor bound: multiplying $\exp((1-\beta)\log 2) \le 2$ by the nonnegative quantity $3\,r(d)\,2^{d}$ (nonnegative because $r(d) > 0$, `hammingRetentionProbability_pos`) gives $\exp((1-\beta)\log 2)\big(3\,r(d)\,2^{d}\big) \le 2\big(3\,r(d)\,2^{d}\big)$. *(lines 18391-18394)*

   <details><summary>Lean and goal state</summary>

   ```lean
       _ ≤ 2 * (3 * hammingRetentionProbability dimension *
             ((2 ^ dimension : ℕ) : ℝ)) := by
           exact mul_le_mul_of_nonneg_right hfactor (by
             positivity [hammingRetentionProbability_pos dimension])
   ```

   Goal before this step:

   ```
   dimension : ℕ
   hfactor : Real.exp ((1 - midpointBeta) * Real.log 2) ≤ 2
   hrecurrence :
     hammingRetentionProbability (dimension + 1) * ↑(2 ^ (dimension + 1)) =
       Real.exp ((1 - midpointBeta) * Real.log 2) * (hammingRetentionProbability dimension * ↑(2 ^ dimension))
   ⊢ Real.exp ((1 - midpointBeta) * Real.log 2) * (3 * hammingRetentionProbability dimension * ↑(2 ^ dimension)) ≤
       2 * (3 * hammingRetentionProbability dimension * ↑(2 ^ dimension))
   ```

   </details>

6. Conclude with $2\big(3\,r(d)\,2^{d}\big) \le 2\,\lceil 3\,r(d)\,2^{d}\rceil$: the factor $2$ is nonnegative and $x \le \lceil x\rceil$ for real $x$ (`Nat.le_ceil`). *(lines 18395-18399)*

   <details><summary>Lean and goal state</summary>

   ```lean
       _ ≤ 2 *
             (⌈3 * hammingRetentionProbability dimension *
               ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
           gcongr
           exact Nat.le_ceil _
   ```

   Goal before this step:

   ```
   dimension : ℕ
   hfactor : Real.exp ((1 - midpointBeta) * Real.log 2) ≤ 2
   hrecurrence :
     hammingRetentionProbability (dimension + 1) * ↑(2 ^ (dimension + 1)) =
       Real.exp ((1 - midpointBeta) * Real.log 2) * (hammingRetentionProbability dimension * ↑(2 ^ dimension))
   ⊢ 2 * (3 * hammingRetentionProbability dimension * ↑(2 ^ dimension)) ≤
       2 * ↑⌈3 * hammingRetentionProbability dimension * ↑(2 ^ dimension)⌉₊
   ```

   </details>

### `TwoDegenerateGraphs.eventually_manuscriptVertexCount_power_le_extremalNumber`

**Statement.** Let $W=\frac14\log_2\!\bigl((97+56\sqrt3)/192\bigr)$ and let $\eta=W/(8(1-\beta))$ be the exponent gain, where $\beta$ is the midpoint of the entropy endpoints. For $n\in\mathbb N$, let $M(n)=\lceil 3r(n)2^n\rceil$, where $r(n)$ is the Hamming retention probability, and let $G_{B,d}$ be the graph on an index set of size $|V_{B,d}|$ obtained from the pair parent system, with $V_{B,d}$ the disjoint union of the layers $L_0=\mathrm{Fin}(B)$ and $L_{i+1}=\{S\subseteq L_i: |S|=2\}$. Then there exist natural numbers $B,d$ such that $B\ge4$, $d>0$, $1<dW/2$, and for all sufficiently large $n$,
\[ M(n)^{3/2+\eta}\le \operatorname{ex}(M(n),G_{B,d}). \]

**Proof idea.** The proof is a direct stitching of two eventual inequalities. The prior extremal-number result supplies the parameters $B,d$ and the eventual bound $E(n)/2\le \operatorname{ex}(M(n),G_{B,d})$; the other prior result supplies the eventual bound $M(n)^{3/2+\eta}\le E(n)/2$. Taking the same witnesses and chaining the two inequalities for all sufficiently large $n$ gives the claim.

1. Apply the earlier result `eventually_expectedRetainedEdge_le_extremalNumber`, which supplies natural numbers $B,d$ satisfying $B\ge4$, $d>0$, $1<dW/2$, together with the eventual inequality $E(n)/2\le \operatorname{ex}(M(n),G_{B,d})$, where $E(n)$ is the expected retained edge count at the manuscript radius $\lfloor\tau n\rfloor$. Destructure this existence statement to obtain those witnesses and hypotheses. *(lines 18321-18323)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨baseSize, depth, hbase, hdepth,
       hdepth_window, hextremal⟩ :=
       eventually_expectedRetainedEdge_le_extremalNumber
   ```

   Goal before this step:

   ```
   ⊢ ∃ baseSize depth,
       4 ≤ baseSize ∧
         0 < depth ∧
           1 < ↑depth * (certifiedWindowWidth / 2) ∧
             ∀ᶠ (dimension : ℕ) in atTop,
               ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
                 ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   ```

   </details>

2. Use the same $B$ and $d$ as the witnesses for the desired existential statement, discharging the three arithmetic and positivity conditions directly from the hypotheses just obtained. The only remaining goal is the eventual comparison between $M(n)^{3/2+\eta}$ and $\operatorname{ex}(M(n),G_{B,d})$. *(lines 18324-18324)*

   <details><summary>Lean and goal state</summary>

   ```lean
     refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hextremal :
     ∀ᶠ (dimension : ℕ) in atTop,
       hammingExpectedRetainedEdgeCount dimension (manuscriptHammingRadius dimension) / 2 ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   ⊢ ∃ baseSize depth,
       4 ≤ baseSize ∧
         0 < depth ∧
           1 < ↑depth * (certifiedWindowWidth / 2) ∧
             ∀ᶠ (dimension : ℕ) in atTop,
               ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
                 ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   ```

   </details>

3. Combine the two eventual facts. The result `eventually_manuscriptVertexCount_power_le_expectedRetainedEdge` gives that, eventually in $n$, $M(n)^{3/2+\eta}\le E(n)/2$, while the previously obtained bound gives that, eventually in $n$, $E(n)/2\le \operatorname{ex}(M(n),G_{B,d})$. Applying `filter_upwards` extracts, for each sufficiently large $n$, both inequalities, and transitivity of $\le$ yields $M(n)^{3/2+\eta}\le \operatorname{ex}(M(n),G_{B,d})$. *(lines 18325-18328)*

   <details><summary>Lean and goal state</summary>

   ```lean
     filter_upwards
       [eventually_manuscriptVertexCount_power_le_expectedRetainedEdge,
         hextremal] with dimension hpower hbound
     exact hpower.trans hbound
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hdepth_window : 1 < ↑depth * (certifiedWindowWidth / 2)
   hextremal :
     ∀ᶠ (dimension : ℕ) in atTop,
       hammingExpectedRetainedEdgeCount dimension (manuscriptHammingRadius dimension) / 2 ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   ⊢ ∀ᶠ (dimension : ℕ) in atTop,
       ↑(manuscriptVertexCount dimension) ^ manuscriptExtremalPower ≤
         ↑(extremalNumber (manuscriptVertexCount dimension) (pairGraphOverFin baseSize depth))
   ```

   </details>

### `TwoDegenerateGraphs.pairGraphOverFin_isBipartite`

**Statement.** For all natural numbers $B$ (the base size) and $d$ (the depth), the graph $G_{B,d}$ on $\mathrm{Fin}(|V_{B,d}|)$ is bipartite, where $V_{B,d}$ is the disjoint union of the layers $L_0,\dots,L_d$ with $L_0=\mathrm{Fin}(B)$ and $L_{i+1}$ the set of two-element subsets of $L_i$, and $G_{B,d}$ is the relabelling onto an initial segment of $\mathbb{N}$ of the graph of the pair parent system (in which $u$ is adjacent to $v$ exactly when $u$ is one of the two parents of $v$, i.e. $u\in$ the two-element finset that is $v$, for $v$ of level $i+1$; vertices of level $0$ have no parents).

**Proof idea.** The proof is a single application of the isomorphism-invariance of bipartiteness: the graph $G_{B,d}$ on $\mathrm{Fin}(|V_{B,d}|)$ is by construction the relabelled copy, along `pairGraphOverFinIso`, of the graph $\Gamma_{B,d}$ of the pair parent system on the layered vertex set $V_{B,d}$, and the latter is already known to be bipartite (`pairGraph_isBipartite`). Nothing about the structure of the pair construction is re-examined here; the content lies entirely in the cited bipartiteness result for the parent-system graph and in the relabelling isomorphism.

1. Apply the general fact `isBipartite_of_iso`, which states that if $e\colon G\simeq_g H$ is a graph isomorphism and $G$ is bipartite then so is $H$. The isomorphism used is the relabelling isomorphism `pairGraphOverFinIso`, an isomorphism from the graph $\Gamma_{B,d}$ of the pair parent system on $V_{B,d}$ to $G_{B,d}$; it is the instance for this parent system of the general construction that renames the vertices of a graph on a finite type by the bijection with $\mathrm{Fin}$ of the cardinality. This reduces the goal to bipartiteness of $\Gamma_{B,d}$. *(lines 12270-12270)*

   <details><summary>Lean and goal state</summary>

   ```lean
     isBipartite_of_iso (pairGraphOverFinIso baseSize depth)
   ```

   </details>

2. Supply the bipartiteness of the source graph, which is exactly the project result `pairGraph_isBipartite`: for every base size $B$ and depth $d$, the graph $\Gamma_{B,d}$ of the pair parent system on $V_{B,d}$ is bipartite. Applying the isomorphism-invariance statement to this discharges the goal. *(lines 12271-12271)*

   <details><summary>Lean and goal state</summary>

   ```lean
       (pairGraph_isBipartite baseSize depth)
   ```

   </details>

### `TwoDegenerateGraphs.manuscriptExtremalPower_pos`

**Statement.** The manuscript extremal power $3/2+\eta$ is strictly positive, where $\eta = W/\bigl(8(1-\beta)\bigr)$ is the exponent gain: $W=\frac14\log_2\bigl((97+56\sqrt3)/192\bigr)$ is the certified window width, $\beta=(\ell+U)/2$ is the midpoint of the entropy lower endpoint $\ell=\kappa+\tau\log_2 3$ and upper endpoint $U=2H(\tau)-1$, with $\tau=(\sqrt3-1)/2$ and $\kappa=3/2-(3/4)\log_2 3$. (Lean: `TwoDegenerateGraphs.manuscriptExtremalPower`.)

**Proof idea.** The manuscript extremal power is by definition $3/2$ plus the exponent gain $\eta$, and the gain is already known to be strictly positive; the proof unfolds the definition and concludes $0<3/2+\eta$ by linear arithmetic from $0<\eta$.

1. Unfold the definition of the manuscript extremal power, which is $3/2+\eta$ with $\eta$ the exponent gain `TwoDegenerateGraphs.exponentGain`, turning the goal into $0<3/2+\eta$. Since $\eta>0$ — the positivity of the exponent gain, `exponentGain_pos` — linear arithmetic gives $0<3/2+\eta$, which closes the goal. *(lines 18130-18131)*

   <details><summary>Lean and goal state</summary>

   ```lean
     unfold manuscriptExtremalPower
     linarith [exponentGain_pos]
   ```

   Goal before this step:

   ```
   ⊢ 0 < manuscriptExtremalPower
   ```

   </details>

### `TwoDegenerateGraphs.exists_manuscriptVertexCount_bracket`

**Statement.** Let $m$ and $n$ be natural numbers, and let $M(d)$ be the manuscript vertex count at dimension $d$, namely the natural ceiling of $3\,r(d)\,2^d$, where $r(d)$ is the Hamming retention probability at dimension $d$. If $M(m) ≤ n$, then there is a natural number $d$ such that $m ≤ d$, $M(d) ≤ n$, and $n < M(d+1)$. Thus the threshold $n$ is bracketed between two consecutive values of $M$ starting at or above $m$.

**Proof idea.** The proof uses divergence of the manuscript vertex count to find some dimension above $m$ where the value exceeds $n$. It then takes the least offset above $m$ at which this crossing occurs. The preceding offset is the desired dimension: it is still at least $m$, its value does not exceed $n$ by minimality, and moving one step further crosses above $n$. The explicit formula for the manuscript vertex count is not used beyond its divergence to infinity.

1. First establish that $n < M(d)$ holds for all sufficiently large $d$. The project result `manuscriptVertexCount_tendsto_atTop` says that $M(d)$ tends to infinity as $d$ tends to infinity. Applying the definition of this limit to the bound $n+1$ gives that eventually $n+1 ≤ M(d)$, hence eventually $n < M(d)$. *(lines 18408-18414)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hlarge :
         ∀ᶠ dimension : ℕ in Filter.atTop,
           n < manuscriptVertexCount dimension := by
       have hevent := Filter.tendsto_atTop.1
         manuscriptVertexCount_tendsto_atTop (n + 1)
       filter_upwards [hevent] with dimension hdimension
       omega
   ```

   Goal before this step:

   ```
   minimum n : ℕ
   hminimum : manuscriptVertexCount minimum ≤ n
   ⊢ ∃ dimension, minimum ≤ dimension ∧ manuscriptVertexCount dimension ≤ n ∧ n < manuscriptVertexCount (dimension + 1)
   ```

   </details>

2. Intersect the eventual inequality $n < M(d)$ with the eventual inequality $m ≤ d$ (`Filter.eventually_ge_atTop minimum`). Since an eventually true predicate on the natural numbers is nonempty, choose a dimension $d_0$ with $m ≤ d_0$ and $n < M(d_0)$. *(lines 18415-18416)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨dimension, hdimension, hafter⟩ :=
       (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
   ```

   Goal before this step:

   ```
   minimum n : ℕ
   hminimum : manuscriptVertexCount minimum ≤ n
   hlarge : ∀ᶠ (dimension : ℕ) in atTop, n < manuscriptVertexCount dimension
   ⊢ ∃ dimension, minimum ≤ dimension ∧ manuscriptVertexCount dimension ≤ n ∧ n < manuscriptVertexCount (dimension + 1)
   ```

   </details>

3. Rewrite the chosen dimension as $m$ plus an offset: set $k_0=d_0-m$. The inequality $m ≤ d_0$ gives $m+k_0=d_0$, so $n < M(m+k_0)$. Therefore there exists an offset $k$ with $n < M(m+k)$. *(lines 18417-18422)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hexists :
         ∃ offset : ℕ,
           n < manuscriptVertexCount (minimum + offset) := by
       refine ⟨dimension - minimum, ?_⟩
       rw [Nat.add_sub_of_le hafter]
       exact hdimension
   ```

   Goal before this step:

   ```
   minimum n : ℕ
   hminimum : manuscriptVertexCount minimum ≤ n
   hlarge : ∀ᶠ (dimension : ℕ) in atTop, n < manuscriptVertexCount dimension
   dimension : ℕ
   hdimension : n < manuscriptVertexCount dimension
   hafter : minimum ≤ dimension
   ⊢ ∃ dimension, minimum ≤ dimension ∧ manuscriptVertexCount dimension ≤ n ∧ n < manuscriptVertexCount (dimension + 1)
   ```

   </details>

4. Let $k$ be the least such offset, using `Nat.find` on the existence statement. Then `Nat.find_spec` gives the defining property of this least offset: $n < M(m+k)$. *(lines 18423-18426)*

   <details><summary>Lean and goal state</summary>

   ```lean
     let offset : ℕ := Nat.find hexists
     have hnext :
         n < manuscriptVertexCount (minimum + offset) :=
       Nat.find_spec hexists
   ```

   Goal before this step:

   ```
   minimum n : ℕ
   hminimum : manuscriptVertexCount minimum ≤ n
   hlarge : ∀ᶠ (dimension : ℕ) in atTop, n < manuscriptVertexCount dimension
   dimension : ℕ
   hdimension : n < manuscriptVertexCount dimension
   hafter : minimum ≤ dimension
   hexists : ∃ offset, n < manuscriptVertexCount (minimum + offset)
   ⊢ ∃ dimension, minimum ≤ dimension ∧ manuscriptVertexCount dimension ≤ n ∧ n < manuscriptVertexCount (dimension + 1)
   ```

   </details>

5. Show that $k$ is positive. If $k=0$, the inequality $n < M(m+k)$ becomes $n < M(m)$, contradicting the hypothesis $M(m) ≤ n$. *(lines 18427-18431)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hoffset : 0 < offset := by
       by_contra hnot
       have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
       simp [hzero] at hnext
       omega
   ```

   Goal before this step:

   ```
   minimum n : ℕ
   hminimum : manuscriptVertexCount minimum ≤ n
   hlarge : ∀ᶠ (dimension : ℕ) in atTop, n < manuscriptVertexCount dimension
   dimension : ℕ
   hdimension : n < manuscriptVertexCount dimension
   hafter : minimum ≤ dimension
   hexists : ∃ offset, n < manuscriptVertexCount (minimum + offset)
   offset : ℕ := Nat.find hexists
   hnext : n < manuscriptVertexCount (minimum + offset)
   ⊢ ∃ dimension, minimum ≤ dimension ∧ manuscriptVertexCount dimension ≤ n ∧ n < manuscriptVertexCount (dimension + 1)
   ```

   </details>

6. Take the candidate dimension $d=m+(k-1)$. Since $k>0$, we have $m ≤ d$. By minimality of $k$, `Nat.find_min` applied to $k-1<k$ gives that the property fails at $k-1$, that is, not $n < M(m+(k-1))$. Therefore $M(d) ≤ n$. *(lines 18432-18436)*

   <details><summary>Lean and goal state</summary>

   ```lean
     refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
     · have hbefore :
           ¬ n < manuscriptVertexCount (minimum + (offset - 1)) := by
         exact Nat.find_min hexists (by omega)
       exact Nat.le_of_not_gt hbefore
   ```

   Goal before this step:

   ```
   minimum n : ℕ
   hminimum : manuscriptVertexCount minimum ≤ n
   hlarge : ∀ᶠ (dimension : ℕ) in atTop, n < manuscriptVertexCount dimension
   dimension : ℕ
   hdimension : n < manuscriptVertexCount dimension
   hafter : minimum ≤ dimension
   hexists : ∃ offset, n < manuscriptVertexCount (minimum + offset)
   offset : ℕ := Nat.find hexists
   hnext : n < manuscriptVertexCount (minimum + offset)
   hoffset : 0 < offset
   ⊢ ∃ dimension, minimum ≤ dimension ∧ manuscriptVertexCount dimension ≤ n ∧ n < manuscriptVertexCount (dimension + 1)
   ```

   </details>

7. Finally $d+1=m+(k-1)+1=m+k$ because $k>0$. Rewriting with this equality turns the remaining goal into $n < M(m+k)$, which is exactly the defining property of the least offset $k$. *(lines 18437-18438)*

   <details><summary>Lean and goal state</summary>

   ```lean
     · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
       exact hnext
   ```

   Goal before this step:

   ```
   case refine_2
   minimum n : ℕ
   hminimum : manuscriptVertexCount minimum ≤ n
   hlarge : ∀ᶠ (dimension : ℕ) in atTop, n < manuscriptVertexCount dimension
   dimension : ℕ
   hdimension : n < manuscriptVertexCount dimension
   hafter : minimum ≤ dimension
   hexists : ∃ offset, n < manuscriptVertexCount (minimum + offset)
   offset : ℕ := Nat.find hexists
   hnext : n < manuscriptVertexCount (minimum + offset)
   hoffset : 0 < offset
   ⊢ n < manuscriptVertexCount (minimum + (offset - 1) + 1)
   ```

   </details>

### `TwoDegenerateGraphs.pairGraphOverFin_bipartition_maximum_degree_gt_two`

**Statement.** Let $B$ and $d$ be natural numbers with $B\ge 4$ and $d\ge 2$. Let $V_{B,d}$ be the disjoint union of the layers $L_0,\dots,L_d$, where $L_0=\mathrm{Fin}(B)$ and $L_{i+1}$ is the set of two-element subsets of $L_i$, and let $G_{B,d}$ be the simple graph on the finite vertex set $\mathrm{Fin}(|V_{B,d}|)$ obtained from the pair parent system via `.graph.overFin rfl`. Then for every 2-coloring of $G_{B,d}$ and every side $s\in\mathrm{Fin}(2)$, the supremum of the degrees of the vertices colored $s$ is greater than $2$; equivalently, each color class contains a vertex of degree at least $3$.

**Proof idea.** The proof reduces the claim to finding a single edge whose two endpoints both have degree greater than $2$. Such an edge exists by the previously established result `pairGraphOverFin_exists_adj_degree_gt_two`. Since a proper 2-coloring separates the endpoints of an edge, every color side contains at least one endpoint of this edge, hence every side has maximum degree greater than $2$. The general lemma `bipartition_maximum_degree_gt_two_of_adj` packages exactly this argument.

1. Work classically and invoke the existence result `pairGraphOverFin_exists_adj_degree_gt_two`, which states that under $B\ge4$ and $d\ge2$ there are adjacent vertices $u,v$ of $G_{B,d}$ with $\deg(u)>2$ and $\deg(v)>2$. The proof unpacks this as witnesses $u,v$, an adjacency $\mathrm{Adj}(u,v)$, and the two degree bounds. The goal remains the stated claim for all 2-colorings and all sides. *(lines 12517-12519)*

   <details><summary>Lean and goal state</summary>

   ```lean
     classical
     obtain ⟨u, v, hadj, hu, hv⟩ :=
       pairGraphOverFin_exists_adj_degree_gt_two baseSize depth hbase hdepth
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 2 ≤ depth
   ⊢ ∀ (coloring : (pairGraphOverFin baseSize depth).Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => (pairGraphOverFin baseSize depth).degree vertex
   ```

   </details>

2. Apply the general lemma `bipartition_maximum_degree_gt_two_of_adj` to the finite graph $G_{B,d}$ and the adjacent high-degree vertices $u,v$. That lemma states that if a finite simple graph has adjacent vertices $u,v$ with $\deg(u)>2$ and $\deg(v)>2$, then for every 2-coloring and every side, the supremum of the degrees over that side is greater than $2$. This directly closes the goal. The underlying reason is that adjacent vertices receive different colors, so each of the two sides contains one of $u,v$, and both have degree greater than $2$. *(lines 12520-12521)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact bipartition_maximum_degree_gt_two_of_adj
       (pairGraphOverFin baseSize depth) hadj hu hv
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 2 ≤ depth
   u v : Fin (Fintype.card (PairVertex baseSize depth))
   hadj : (pairGraphOverFin baseSize depth).Adj u v
   hu : 2 < (pairGraphOverFin baseSize depth).degree u
   hv : 2 < (pairGraphOverFin baseSize depth).degree v
   ⊢ ∀ (coloring : (pairGraphOverFin baseSize depth).Coloring (Fin 2)) (side : Fin 2),
       2 < {vertex | coloring vertex = side}.sup fun vertex => (pairGraphOverFin baseSize depth).degree vertex
   ```

   </details>

### `TwoDegenerateGraphs.entropyUpperEndpoint_lt_one`

**Statement.** Let $\tau=(\sqrt3-1)/2$ and let $H$ be the binary entropy in bits, $H(x)=\operatorname{binEntropy}(x)/\log 2$. Then the entropy upper endpoint $U=2H(\tau)-1$ (`TwoDegenerateGraphs.entropyUpperEndpoint`) satisfies $U<1$.

**Proof idea.** The bound is immediate: the upper endpoint is $2H(\tau)-1$, and since the binary entropy of $\tau$ is less than $1$ (the lemma `binaryEntropy_tau_lt_one`), twice it minus one is less than $1$.

1. Expand the definition of the upper endpoint $U$, turning the goal into $2H(\tau)-1<1$. *(lines 11539-11539)*

   <details><summary>Lean and goal state</summary>

   ```lean
     unfold entropyUpperEndpoint
   ```

   Goal before this step:

   ```
   ⊢ entropyUpperEndpoint < 1
   ```

   </details>

2. Close the goal by nonlinear arithmetic, using the project lemma `binaryEntropy_tau_lt_one`, which states $H(\tau)<1$. (Nonlinear arithmetic is needed only because the term $H(\tau)$ is otherwise opaque; from $H(\tau)<1$ the claim $2H(\tau)-1<1$ is a linear consequence.) *(lines 11540-11540)*

   <details><summary>Lean and goal state</summary>

   ```lean
     nlinarith [binaryEntropy_tau_lt_one]
   ```

   Goal before this step:

   ```
   ⊢ 2 * binaryEntropy tau - 1 < 1
   ```

   </details>

### `TwoDegenerateGraphs.exponentGain_pos`

**Statement.** Let $W=\frac14\log_2\!\bigl((97+56\sqrt3)/192\bigr)$ be the certified window width, let $\ell=\kappa+\tau\log_2 3$ and $U=2H(\tau)-1$ be the lower and upper entropy endpoints, and let $\beta=(\ell+U)/2$ be their midpoint. Then the exponent gain $\eta = W/\bigl(8(1-\beta)\bigr)$ is strictly positive.

**Proof idea.** The exponent gain is a quotient whose numerator is the certified window width, already known to be positive, and whose denominator is $8$ times $1-\beta$; since $8>0$ and the midpoint $\beta$ of the entropy endpoints is less than $1$, the denominator is positive too, so the quotient is positive.

1. Unfold the definition of the exponent gain, so that the goal becomes $0 < W/\bigl(8(1-\beta)\bigr)$, where $W$ is the certified window width and $\beta=(\ell+U)/2$ the midpoint of the two entropy endpoints. *(lines 11558-11558)*

   <details><summary>Lean and goal state</summary>

   ```lean
     unfold exponentGain
   ```

   Goal before this step:

   ```
   ⊢ 0 < exponentGain
   ```

   </details>

2. Apply positivity of a quotient (`div_pos`): it suffices that the numerator and denominator be positive. The numerator $W$ is positive by `certifiedWindowWidth_pos`. The denominator $8(1-\beta)$ is a product of positive factors: $8>0$ is checked by `norm_num`, and $1-\beta>0$ is exactly $\beta<1$, which is `midpointBeta_lt_one` converted to a positive difference (`sub_pos.mpr`). *(lines 11559-11560)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact div_pos certifiedWindowWidth_pos
       (mul_pos (by norm_num) (sub_pos.mpr midpointBeta_lt_one))
   ```

   Goal before this step:

   ```
   ⊢ 0 < certifiedWindowWidth / (8 * (1 - midpointBeta))
   ```

   </details>

### `CompactnessConjecture.extremalNumber_monotone_of_no_isolated`

**Statement.** Let $F$ be a simple graph on a vertex set $U$ (not assumed finite) in which every vertex has a neighbour. Then for all natural numbers $m\le n$, the extremal number $\operatorname{ex}(m,F)$ is at most $\operatorname{ex}(n,F)$.

**Proof idea.** The proof takes an arbitrary $F$-free graph on $m$ vertices and pads it to an $n$-vertex graph by mapping it into ${\rm Fin}\,n$ along the inclusion ${\rm Fin}\,m\hookrightarrow{\rm Fin}\,n$. The no-isolated-vertex hypothesis on $F$ ensures, via `free_map_of_no_isolated`, that this padding creates no copy of $F$, so the padded graph remains $F$-free. Padding preserves the number of edges, and every $F$-free graph on $n$ vertices has at most $\operatorname{ex}(n,F)$ edges. Therefore every $F$-free $m$-vertex graph has at most $\operatorname{ex}(n,F)$ edges, and the universal property of the extremal number gives $\operatorname{ex}(m,F)\le \operatorname{ex}(n,F)$.

1. Argue classically and set up the auxiliary inequality $\operatorname{ex}(m,F)\le \operatorname{ex}(n,F)$, with the left-hand side written as $\operatorname{ex}(|{\rm Fin}\,m|,F)$; since $|{\rm Fin}\,m|=m$, this is the desired bound. *(lines 2690-2693)*

   <details><summary>Lean and goal state</summary>

   ```lean
     classical
     have hbound :
         SimpleGraph.extremalNumber (Fintype.card (Fin m)) forbidden ≤
           SimpleGraph.extremalNumber n forbidden := by
   ```

   Goal before this step:

   ```
   U : Type u_1
   forbidden : SimpleGraph U
   hneighbors : ∀ (u : U), ∃ v, forbidden.Adj u v
   m n : ℕ
   hmn : m ≤ n
   ⊢ extremalNumber m forbidden ≤ extremalNumber n forbidden
   ```

   </details>

2. Apply the universal property of the extremal number (`SimpleGraph.extremalNumber_le_iff`): to prove $\operatorname{ex}(|{\rm Fin}\,m|,F)\le \operatorname{ex}(n,F)$, it suffices to show that every $F$-free graph on the vertex set ${\rm Fin}\,m$ has at most $\operatorname{ex}(n,F)$ edges. Fix such a graph $G$ (`host`) together with its $F$-freeness hypothesis; the goal becomes $|E(G)|\le \operatorname{ex}(n,F)$. *(lines 2694-2697)*

   <details><summary>Lean and goal state</summary>

   ```lean
       apply (SimpleGraph.extremalNumber_le_iff
         (V := Fin m) forbidden
         (SimpleGraph.extremalNumber n forbidden)).mpr
       intro host _ hfree
   ```

   Goal before this step:

   ```
   U : Type u_1
   forbidden : SimpleGraph U
   hneighbors : ∀ (u : U), ∃ v, forbidden.Adj u v
   m n : ℕ
   hmn : m ≤ n
   ⊢ extremalNumber (Fintype.card (Fin m)) forbidden ≤ extremalNumber n forbidden
   ```

   </details>

3. Let $e\colon {\rm Fin}\,m\hookrightarrow{\rm Fin}\,n$ be the inclusion $i\mapsto i$ supplied by $m\le n$. Because $F$ has no isolated vertices, `free_map_of_no_isolated` applied to $e$ and the $F$-freeness of $G$ shows that the image graph $e(G)=G.map\,e$ is again $F$-free. *(lines 2698-2700)*

   <details><summary>Lean and goal state</summary>

   ```lean
       let embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
       have hpadded : forbidden.Free (host.map embedding) :=
         free_map_of_no_isolated forbidden hneighbors embedding hfree
   ```

   Goal before this step:

   ```
   U : Type u_1
   forbidden : SimpleGraph U
   hneighbors : ∀ (u : U), ∃ v, forbidden.Adj u v
   m n : ℕ
   hmn : m ≤ n
   host : SimpleGraph (Fin m)
   inst✝ : DecidableRel host.Adj
   hfree : forbidden.Free host
   ⊢ host.edgeFinset.card ≤ extremalNumber n forbidden
   ```

   </details>

4. Prove the edge bound by a two-step calculation. Mapping along the injective map $e$ preserves the number of edges, so $|E(e(G))|=|E(G)|$ (using `SimpleGraph.card_edgeFinset_map`). Since $e(G)$ is an $F$-free graph on ${\rm Fin}\,n$, its edge count is at most $\operatorname{ex}(n,F)$ by the defining property of the extremal number (`SimpleGraph.card_edgeFinset_le_extremalNumber`). Hence $|E(G)|\le \operatorname{ex}(n,F)$. *(lines 2701-2708)*

   <details><summary>Lean and goal state</summary>

   ```lean
       calc
         host.edgeFinset.card =
             (host.map embedding).edgeFinset.card := by
           simpa only [SimpleGraph.edgeFinset_card,
             ← Nat.card_eq_fintype_card] using
             (SimpleGraph.card_edgeFinset_map embedding host).symm
         _ ≤ SimpleGraph.extremalNumber n forbidden := by
           simpa using SimpleGraph.card_edgeFinset_le_extremalNumber hpadded
   ```

   Goal before this step:

   ```
   U : Type u_1
   forbidden : SimpleGraph U
   hneighbors : ∀ (u : U), ∃ v, forbidden.Adj u v
   m n : ℕ
   hmn : m ≤ n
   host : SimpleGraph (Fin m)
   inst✝ : DecidableRel host.Adj
   hfree : forbidden.Free host
   embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
   hpadded : forbidden.Free (SimpleGraph.map (⇑embedding) host)
   ⊢ host.edgeFinset.card ≤ extremalNumber n forbidden
   ```

   </details>

5. Discharge the auxiliary claim: $|{\rm Fin}\,m|=m$, so the established inequality is exactly $\operatorname{ex}(m,F)\le \operatorname{ex}(n,F)$. *(lines 2709-2709)*

   <details><summary>Lean and goal state</summary>

   ```lean
     simpa using hbound
   ```

   Goal before this step:

   ```
   U : Type u_1
   forbidden : SimpleGraph U
   hneighbors : ∀ (u : U), ∃ v, forbidden.Adj u v
   m n : ℕ
   hmn : m ≤ n
   hbound : extremalNumber (Fintype.card (Fin m)) forbidden ≤ extremalNumber n forbidden
   ⊢ extremalNumber m forbidden ≤ extremalNumber n forbidden
   ```

   </details>

### `TwoDegenerateGraphs.entropyLowerEndpoint_pos`

**Statement.** Let $\kappa = \frac32 - \frac34\log_2 3$ and $\tau = \frac{\sqrt3-1}{2}$, where $\log_2 x = \log x/\log 2$. Then the lower endpoint $\ell = \kappa + \tau\log_2 3$ of the certified entropy window is strictly positive.

**Proof idea.** The lower endpoint is a sum of two positive terms: $\kappa$ itself is positive, and $\tau\log_2 3$ is a product of the positive constants $\tau$ and $\log_2 3$. The proof is an immediate appeal to positivity after unfolding the definition.

1. Unfold the definition of the lower endpoint $\ell$ (`TwoDegenerateGraphs.entropyLowerEndpoint`), turning the goal $0 < \ell$ into $0 < \kappa + \tau\log_2 3$. *(lines 11525-11525)*

   <details><summary>Lean and goal state</summary>

   ```lean
     unfold entropyLowerEndpoint
   ```

   Goal before this step:

   ```
   ⊢ 0 < entropyLowerEndpoint
   ```

   </details>

2. Conclude by positivity, from the three facts supplied: $\kappa > 0$ (`kappa_pos`, i.e. $\frac32 - \frac34\log_2 3 > 0$), $\tau > 0$ (`tau_pos`, i.e. $(\sqrt3-1)/2 > 0$), and $\log_2 3 > 0$ (`logTwo_three_pos`). A positive number plus a product of two positive numbers is positive. *(lines 11526-11526)*

   <details><summary>Lean and goal state</summary>

   ```lean
     positivity [kappa_pos, tau_pos, logTwo_three_pos]
   ```

   Goal before this step:

   ```
   ⊢ 0 < kappa + tau * logTwo 3
   ```

   </details>

### `TwoDegenerateGraphs.pairGraphOverFin_isTwoDegenerate`

**Statement.** For all natural numbers $B$ (the base size) and $d$ (the depth), the graph $G_{B,d}$ — the simple graph with vertex set $\mathrm{Fin}(|V_{B,d}|)$ obtained from the pair parent system by relabelling along a bijection — is 2-degenerate, i.e. every subgraph of it has a vertex of degree at most $2$. Here the vertex set is the disjoint union $V_{B,d}=\bigsqcup_{i=0}^{d} L_i$ of the layers with $L_0=\mathrm{Fin}(B)$ and $L_{i+1}$ the set of two-element subsets (finsets of cardinality $2$) of $L_i$, the pair parent system `pairParentSystem baseSize depth` is the structure assigning to each vertex its layer $i$ and declaring the parents of a vertex in $L_{i+1}$ to be the two elements of the pair it is, and its graph is the simple graph in which two vertices are adjacent when one of them is a parent of the other. 2-degeneracy is `IsTwoDegenerate`, defined as $2$-degeneracy $\mathrm{IsDegenerate}\,2$ of the graph.

**Proof idea.** The relabelled graph $G_{B,d}$ is isomorphic, via the relabelling isomorphism attached to the pair parent system, to the graph of the pair parent system itself; since that graph is already known to be 2-degenerate, and 2-degeneracy is an isomorphism invariant, $G_{B,d}$ is 2-degenerate for every base size $B$ and depth $d$. Conceptually the pair construction starts from $B$ base vertices and repeatedly replaces a vertex by the set of unordered pairs of vertices of the previous layer, drawing an edge between a vertex and each member of the pair it represents; each vertex in a positive layer has exactly two parents and the resulting parent system yields 2-degenerate graphs.

1. Transport 2-degeneracy across an isomorphism. The two inputs are: (i) the graph isomorphism $G \simeq_G G_{B,d}$ from the pair parent system's graph to the relabelled graph on $\mathrm{Fin}(|V_{B,d}|)$, given by `pairGraphOverFinIso baseSize depth` (for each $B$ and $d$, it is the relabelling isomorphism of `.graph.overFin rfl`); and (ii) the theorem `pairGraph_isTwoDegenerate baseSize depth`, which states that the graph of the pair parent system `pairParentSystem baseSize depth` is 2-degenerate. The generic lemma `isTwoDegenerate_of_iso` — 2-degeneracy is preserved in both directions along a graph isomorphism $G \simeq_G H$ — then gives 2-degeneracy of $G_{B,d}$. *(lines 12275-12276)*

   <details><summary>Lean and goal state</summary>

   ```lean
     isTwoDegenerate_of_iso (pairGraphOverFinIso baseSize depth)
       (pairGraph_isTwoDegenerate baseSize depth)
   ```

   </details>

### `TwoDegenerateGraphs.entropyWindow_eq_certifiedWindowWidth`

**Statement.** Let $\tau=(\sqrt3-1)/2$, let $\log_2 x=\log x/\log2$, let $H(x)$ be Mathlib's binary entropy divided by $\log2$, set $\kappa=3/2-(3/4)\log_2 3$, and define the upper and lower endpoints by $U=2H(\tau)-1$ and $\ell=\kappa+\tau\log_2 3$, and the certified window width by $W=\frac14\log_2((97+56\sqrt3)/192)$. Then $U-\ell=W$.

**Proof idea.** The proof is pure algebra from two supplied identities. The entropy identity expresses $2H(\tau)-\tau\log_2 3$ in terms of $\log_2(1+1/\sqrt3)$, while the log-certificate identity expresses $\log((97+56\sqrt3)/192)$ in terms of $\log(1+1/\sqrt3)$, $\log3$, and $\log2$. After clearing the $\log2$ denominators, rewriting $(\sqrt3+1)/\sqrt3=1+1/\sqrt3$, and normalizing, the desired equality becomes a linear combination of the two identities, so linear arithmetic finishes.

1. Record the two identities supplied by the project. The first, `entropy_tau_identity`, is $2H(\tau)-\tau\log_2 3=2\log_2(1+1/\sqrt3)$; unfolding $\log_2$ in it gives $2H(\tau)-\tau(\log3/\log2)=2\log(1+1/\sqrt3)/\log2$. The second, `log_certificate_ratio_identity`, is $\log((97+56\sqrt3)/192)=8\log(1+1/\sqrt3)+3\log3-10\log2$. *(lines 11466-11468)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hentropy := entropy_tau_identity
     have hlog := log_certificate_ratio_identity
     unfold logTwo at hentropy
   ```

   Goal before this step:

   ```
   ⊢ entropyUpperEndpoint - entropyLowerEndpoint = certifiedWindowWidth
   ```

   </details>

2. Prove the auxiliary algebraic identity $(\sqrt3+1)/\sqrt3=1+1/\sqrt3$ by clearing denominators (`field_simp`), using $\sqrt3\ne0$. *(lines 11469-11472)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hlog_argument :
         (Real.sqrt 3 + 1) / Real.sqrt 3 =
           1 + 1 / Real.sqrt 3 := by
       field_simp [sqrt_three_pos.ne']
   ```

   Goal before this step:

   ```
   hentropy : 2 * binaryEntropy tau - tau * (Real.log 3 / Real.log 2) = 2 * (Real.log (1 + 1 / √3) / Real.log 2)
   hlog : Real.log ((97 + 56 * √3) / 192) = 8 * Real.log (1 + 1 / √3) + 3 * Real.log 3 - 10 * Real.log 2
   ⊢ entropyUpperEndpoint - entropyLowerEndpoint = certifiedWindowWidth
   ```

   </details>

3. Unfold $U$, $\ell$, $\kappa$, $W$, and $\log_2$ in the goal. Then clear the denominator $\log2$ in the entropy identity and in the goal, using $\log2>0$. The entropy identity becomes $2H(\tau)\log2-\tau\log3=2\log((\sqrt3+1)/\sqrt3)$, and the goal becomes $2\log2\,(2H(\tau)-1)\,4-\bigl(3(\log2\cdot4-2\log3)+2\tau\log3\cdot4\bigr)=2\log((97+56\sqrt3)/192)$. *(lines 11473-11475)*

   <details><summary>Lean and goal state</summary>

   ```lean
     unfold entropyUpperEndpoint entropyLowerEndpoint kappa
       certifiedWindowWidth logTwo
     field_simp [log_two_pos.ne'] at hentropy ⊢
   ```

   Goal before this step:

   ```
   hentropy : 2 * binaryEntropy tau - tau * (Real.log 3 / Real.log 2) = 2 * (Real.log (1 + 1 / √3) / Real.log 2)
   hlog : Real.log ((97 + 56 * √3) / 192) = 8 * Real.log (1 + 1 / √3) + 3 * Real.log 3 - 10 * Real.log 2
   hlog_argument : (√3 + 1) / √3 = 1 + 1 / √3
   ⊢ entropyUpperEndpoint - entropyLowerEndpoint = certifiedWindowWidth
   ```

   </details>

4. Rewrite the argument $(\sqrt3+1)/\sqrt3$ in the entropy identity by the auxiliary identity, so its right-hand side is $2\log(1+1/\sqrt3)$. *(lines 11476-11476)*

   <details><summary>Lean and goal state</summary>

   ```lean
     rw [hlog_argument] at hentropy
   ```

   Goal before this step:

   ```
   hlog : Real.log ((97 + 56 * √3) / 192) = 8 * Real.log (1 + 1 / √3) + 3 * Real.log 3 - 10 * Real.log 2
   hlog_argument : (√3 + 1) / √3 = 1 + 1 / √3
   hentropy : 2 * binaryEntropy tau * Real.log 2 - tau * Real.log 3 = 2 * Real.log ((√3 + 1) / √3)
   ⊢ 2 * Real.log 2 * (2 * binaryEntropy tau - 1) * 4 -
         (3 * (Real.log 2 * 4 - 2 * Real.log 3) + 2 * tau * Real.log 3 * 4) =
       2 * Real.log ((97 + √3 * 56) / 192)
   ```

   </details>

5. Normalize the two identities and the goal with `ring_nf`, which rearranges the linear expressions and rewrites the certificate logarithm. The entropy identity becomes $2H(\tau)\log2-\tau\log3=2\log(1+(\sqrt3)^{-1})$; the log identity becomes $\log(97/192+(7/24)\sqrt3)=-10\log2+3\log3+8\log(1+(\sqrt3)^{-1})$; and the goal becomes $16H(\tau)\log2-20\log2-8\tau\log3+6\log3=2\log(97/192+(7/24)\sqrt3)$. *(lines 11477-11477)*

   <details><summary>Lean and goal state</summary>

   ```lean
     ring_nf at hentropy hlog ⊢
   ```

   Goal before this step:

   ```
   hlog : Real.log ((97 + 56 * √3) / 192) = 8 * Real.log (1 + 1 / √3) + 3 * Real.log 3 - 10 * Real.log 2
   hlog_argument : (√3 + 1) / √3 = 1 + 1 / √3
   hentropy : 2 * binaryEntropy tau * Real.log 2 - tau * Real.log 3 = 2 * Real.log (1 + 1 / √3)
   ⊢ 2 * Real.log 2 * (2 * binaryEntropy tau - 1) * 4 -
         (3 * (Real.log 2 * 4 - 2 * Real.log 3) + 2 * tau * Real.log 3 * 4) =
       2 * Real.log ((97 + √3 * 56) / 192)
   ```

   </details>

6. Close by `linarith`. Treating $\log2$, $\log3$, and $\log(1+(\sqrt3)^{-1})$ as indeterminates, the three displayed relations are linear; explicitly, multiplying the entropy identity by $8$ and substituting the log identity gives the target equality. *(lines 11478-11478)*

   <details><summary>Lean and goal state</summary>

   ```lean
     linarith
   ```

   Goal before this step:

   ```
   hlog_argument : (√3 + 1) / √3 = 1 + 1 / √3
   hentropy : binaryEntropy tau * Real.log 2 * 2 - tau * Real.log 3 = Real.log (1 + (√3)⁻¹) * 2
   hlog : Real.log (97 / 192 + √3 * (7 / 24)) = -(Real.log 2 * 10) + Real.log 3 * 3 + Real.log (1 + (√3)⁻¹) * 8
   ⊢ binaryEntropy tau * Real.log 2 * 16 - Real.log 2 * 20 - tau * Real.log 3 * 8 + Real.log 3 * 6 =
       Real.log (97 / 192 + √3 * (7 / 24)) * 2
   ```

   </details>

### `TwoDegenerateGraphs.pairGraphOverFin_forall_exists_adj`

**Statement.** Let $B$ and $d$ be natural numbers with $B\ge 4$ and $d>0$. Define $L_0=\mathrm{Fin}(B)$ and $L_{i+1}=\{P\subseteq L_i : |P|=2\}$ (finsets of cardinality two), and let $V_{B,d}=\bigsqcup_{i=0}^{d} L_i$ be the vertex type `PairVertex baseSize depth`. Let $G_{B,d}$ be the simple graph on $\mathrm{Fin}(|V_{B,d}|)$ obtained from the pair parent system `pairParentSystem B d` by applying `.graph.overFin rfl` (`pairGraphOverFin baseSize depth`). Then every vertex of $G_{B,d}$ has an adjacent neighbor.

**Proof idea.** The proof reduces the no-isolated-vertex property to connectedness of the pair graph. It first checks that the vertex type has at least two elements, hence is nontrivial, then applies the known connectedness of the pair graph, where positivity of the base size follows from $B\ge4$, and finally uses that a nontrivial preconnected graph gives every vertex a neighbor.

1. First bound the vertex set below by $2$. The project lemma `baseSize_le_pairVertex_card` gives $B\le |V_{B,d}|$, and since $B\ge 4$, linear arithmetic (`omega`) yields $2\le |V_{B,d}|$. *(lines 18026-18028)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hcard : 2 ≤ Fintype.card (PairVertex baseSize depth) := by
       have hcard_base := baseSize_le_pairVertex_card baseSize depth
       omega
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   ⊢ ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))),
       ∃ neighbor, (pairGraphOverFin baseSize depth).Adj vertex neighbor
   ```

   </details>

2. Using that cardinality bound, make $\mathrm{Fin}(|V_{B,d}|)$ into a nontrivial type via `Fin.nontrivial_iff_two_le.mpr`. This supplies the nontriviality condition needed later when applying preconnectedness at a vertex. *(lines 18029-18030)*

   <details><summary>Lean and goal state</summary>

   ```lean
     letI : Nontrivial (Fin (Fintype.card (PairVertex baseSize depth))) :=
       Fin.nontrivial_iff_two_le.mpr hcard
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hcard : 2 ≤ Fintype.card (PairVertex baseSize depth)
   ⊢ ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))),
       ∃ neighbor, (pairGraphOverFin baseSize depth).Adj vertex neighbor
   ```

   </details>

3. Fix an arbitrary vertex $v$ of $\mathrm{Fin}(|V_{B,d}|)$; it remains to find a neighbor of this $v$. *(lines 18031-18031)*

   <details><summary>Lean and goal state</summary>

   ```lean
     intro vertex
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hcard : 2 ≤ Fintype.card (PairVertex baseSize depth)
   this : Nontrivial (Fin (Fintype.card (PairVertex baseSize depth))) := Fin.nontrivial_iff_two_le.mpr hcard
   ⊢ ∀ (vertex : Fin (Fintype.card (PairVertex baseSize depth))),
       ∃ neighbor, (pairGraphOverFin baseSize depth).Adj vertex neighbor
   ```

   </details>

4. Apply `pairGraphOverFin_connected`, which states that the pair graph is connected when the base size and depth are positive. The positivity $0<B$ is discharged by `omega` from $B\ge4$, and $d>0$ is the hypothesis. From connectedness take `.preconnected`, and then `exists_adj_of_nontrivial`, using the nontriviality instance above, gives a vertex adjacent to $v$. This closes the goal. *(lines 18032-18034)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact
       (pairGraphOverFin_connected baseSize depth (by omega) hdepth).preconnected
         |>.exists_adj_of_nontrivial vertex
   ```

   Goal before this step:

   ```
   baseSize depth : ℕ
   hbase : 4 ≤ baseSize
   hdepth : 0 < depth
   hcard : 2 ≤ Fintype.card (PairVertex baseSize depth)
   this : Nontrivial (Fin (Fintype.card (PairVertex baseSize depth))) := Fin.nontrivial_iff_two_le.mpr hcard
   vertex : Fin (Fintype.card (PairVertex baseSize depth))
   ⊢ ∃ neighbor, (pairGraphOverFin baseSize depth).Adj vertex neighbor
   ```

   </details>

### `CompactnessConjecture.eventually_constant_le_positive_nat_rpow`

**Statement.** Let $c$, $a$ and $e$ be real numbers with $a > 0$ and $e > 0$. Then for all sufficiently large natural numbers $n$, $c \le a\, n^{e}$.

**Proof idea.** The comparison $c \le a\,n^{e}$ is rewritten as $c/a \le n^{e}$, and since $n^{e} \to +\infty$ for positive $e$, the latter holds for all large $n$; multiplying back by the positive constant $a$ gives the claim.

1. First record an auxiliary fact: the sequence $n \mapsto n^{e}$ (real powers of the natural number $n$, viewed in $\mathbb{R}$) tends to $+\infty$. This is the composition of two known limits: $x \mapsto x^{e}$ tends to $+\infty$ as $x \to +\infty$ when $e > 0$ (the library lemma `tendsto_rpow_atTop`, applied to the hypothesis $e > 0$), and the coercion $n \mapsto (n : \mathbb{R})$ tends to $+\infty$ (`tendsto_natCast_atTop_atTop`). *(lines 8677-8682)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hpower :
         Filter.Tendsto
           (fun n : ℕ => (n : ℝ) ^ exponent)
           Filter.atTop Filter.atTop :=
       (tendsto_rpow_atTop hexponent).comp
         (tendsto_natCast_atTop_atTop (R := ℝ))
   ```

   Goal before this step:

   ```
   constant coefficient exponent : ℝ
   hcoefficient : 0 < coefficient
   hexponent : 0 < exponent
   ⊢ ∀ᶠ (n : ℕ) in atTop, constant ≤ coefficient * ↑n ^ exponent
   ```

   </details>

2. Since $n^{e} \to +\infty$, it is eventually at least the threshold $c/a$; this is the `Filter.eventually_ge_atTop` fact transported along the limit just established, giving a set of $n$ on which $c/a \le n^{e}$. The goal is reduced to proving $c \le a\, n^{e}$ for an arbitrary such $n$, with the hypothesis $h_n : c/a \le n^{e}$ in hand. *(lines 8683-8685)*

   <details><summary>Lean and goal state</summary>

   ```lean
     filter_upwards [hpower.eventually
       (Filter.eventually_ge_atTop (constant / coefficient))]
       with n hn
   ```

   Goal before this step:

   ```
   constant coefficient exponent : ℝ
   hcoefficient : 0 < coefficient
   hexponent : 0 < exponent
   hpower : Tendsto (fun n => ↑n ^ exponent) atTop atTop
   ⊢ ∀ᶠ (n : ℕ) in atTop, constant ≤ coefficient * ↑n ^ exponent
   ```

   </details>

3. For such an $n$, compute in two steps. First $c = a \cdot (c/a)$, since $a \ne 0$ follows from $a > 0$ (the division clears by `field_simp`). Then $a \cdot (c/a) \le a \cdot n^{e}$, because $c/a \le n^{e}$ and $a \ge 0$ (the lemma `mul_le_mul_of_nonneg_left` applied to $h_n$ and $0 < a$). Chaining the two gives $c \le a\, n^{e}$. *(lines 8686-8690)*

   <details><summary>Lean and goal state</summary>

   ```lean
     calc
       constant = coefficient * (constant / coefficient) := by
         field_simp
       _ ≤ coefficient * (n : ℝ) ^ exponent :=
         mul_le_mul_of_nonneg_left hn hcoefficient.le
   ```

   Goal before this step:

   ```
   constant coefficient exponent : ℝ
   hcoefficient : 0 < coefficient
   hexponent : 0 < exponent
   hpower : Tendsto (fun n => ↑n ^ exponent) atTop atTop
   n : ℕ
   hn : constant / coefficient ≤ ↑n ^ exponent
   ⊢ constant ≤ coefficient * ↑n ^ exponent
   ```

   </details>

## Results cited without proof

- `TwoDegenerateGraphs.manuscriptExtremalPower`: `ℝ`
- `TwoDegenerateGraphs.PairVertex`: `ℕ → ℕ → Type`
- `TwoDegenerateGraphs.entropyLowerEndpoint`: `ℝ`
- `TwoDegenerateGraphs.PairLayer`: `ℕ → ℕ → Type`
- `TwoDegenerateGraphs.pairGraphOverFin_connected`: `∀ (baseSize depth : ℕ), 0 < baseSize → 0 < depth → (TwoDegenerateGraphs.pairGraphOverFin baseSize depth).Connected`
- `TwoDegenerateGraphs.pairGraphOverFin`: `(baseSize depth : ℕ) → SimpleGraph (Fin (Fintype.card (TwoDegenerateGraphs.PairVertex baseSize depth)))`
- `TwoDegenerateGraphs.baseSize_le_pairVertex_card`: `∀ (baseSize depth : ℕ), baseSize ≤ Fintype.card (TwoDegenerateGraphs.PairVertex baseSize depth)`
- `TwoDegenerateGraphs.pairLayerFintype`: `(baseSize i : ℕ) → Fintype (TwoDegenerateGraphs.PairLayer baseSize i)`
- `TwoDegenerateGraphs.manuscriptVertexCount`: `ℕ → ℕ`
- `TwoDegenerateGraphs.log_certificate_ratio_identity`: `Real.log ((97 + 56 * √3) / 192) = 8 * Real.log (1 + 1 / √3) + 3 * Real.log 3 - 10 * Real.log 2`
- `TwoDegenerateGraphs.kappa`: `ℝ`
- `TwoDegenerateGraphs.entropyUpperEndpoint`: `ℝ`
- `TwoDegenerateGraphs.logTwo`: `ℝ → ℝ`
- `TwoDegenerateGraphs.tau`: `ℝ`
- `TwoDegenerateGraphs.binaryEntropy`: `ℝ → ℝ`
- `TwoDegenerateGraphs.entropy_tau_identity`: `2 * TwoDegenerateGraphs.binaryEntropy TwoDegenerateGraphs.tau - TwoDegenerateGraphs.tau * TwoDegenerateGraphs.logTwo 3 = 2 * TwoDegenerateGraphs.logTwo (1 + 1 / √3)`
- `TwoDegenerateGraphs.certifiedWindowWidth`: `ℝ`
- `TwoDegenerateGraphs.exponentGain`: `ℝ`
- `TwoDegenerateGraphs.isTwoDegenerate_of_iso`: `∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H), TwoDegenerateGraphs.IsTwoDegenerate G → TwoDegenerateGraphs.IsTwoDegenerate H`
- `TwoDegenerateGraphs.pairGraph_isTwoDegenerate`: `∀ (baseSize depth : ℕ), TwoDegenerateGraphs.IsTwoDegenerate (TwoDegenerateGraphs.pairParentSystem baseSize depth).graph`
- `TwoDegenerateGraphs.pairParentSystem`: `(baseSize depth : ℕ) → TwoDegenerateGraphs.ParentSystem (TwoDegenerateGraphs.PairVertex baseSize depth)`
- `TwoDegenerateGraphs.IsTwoDegenerate`: `{V : Type u_1} → SimpleGraph V → Prop`
- `TwoDegenerateGraphs.pairGraphOverFinIso`: `(baseSize depth : ℕ) → (TwoDegenerateGraphs.pairParentSystem baseSize depth).graph ≃g TwoDegenerateGraphs.pairGraphOverFin baseSize depth`
- `TwoDegenerateGraphs.ParentSystem.graph`: `{V : Type u_1} → TwoDegenerateGraphs.ParentSystem V → SimpleGraph V`
- `TwoDegenerateGraphs.logTwo_three_pos`: `0 < TwoDegenerateGraphs.logTwo 3`
- `TwoDegenerateGraphs.tau_pos`: `0 < TwoDegenerateGraphs.tau`
- `TwoDegenerateGraphs.kappa_pos`: `0 < TwoDegenerateGraphs.kappa`
- `CompactnessConjecture.free_map_of_no_isolated`: `∀ {U : Type u_1} {V : Type u_2} {W : Type u_3} (forbidden : SimpleGraph U), (∀ (u : U), ∃ v, forbidden.Adj u v) → ∀ {host : SimpleGraph V} (embedding : V ↪ W), forbidden.Free host → forbidden.Free (SimpleGraph.map (⇑embedding) host)`
- `TwoDegenerateGraphs.midpointBeta_lt_one`: `TwoDegenerateGraphs.midpointBeta < 1`
- `TwoDegenerateGraphs.midpointBeta`: `ℝ`
- `TwoDegenerateGraphs.certifiedWindowWidth_pos`: `0 < TwoDegenerateGraphs.certifiedWindowWidth`
- `TwoDegenerateGraphs.binaryEntropy_tau_lt_one`: `TwoDegenerateGraphs.binaryEntropy TwoDegenerateGraphs.tau < 1`
- `TwoDegenerateGraphs.bipartition_maximum_degree_gt_two_of_adj`: `∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) {u v : V}, G.Adj u v → 2 < G.degree u → 2 < G.degree v → ∀ (coloring : G.Coloring (Fin 2)) (side : Fin 2), 2 < {vertex | coloring vertex = side}.sup fun vertex => G.degree vertex`
- `TwoDegenerateGraphs.pairGraphOverFin_exists_adj_degree_gt_two`: `∀ (baseSize depth : ℕ), 4 ≤ baseSize → 2 ≤ depth → ∃ u v, (TwoDegenerateGraphs.pairGraphOverFin baseSize depth).Adj u v ∧ 2 < (TwoDegenerateGraphs.pairGraphOverFin baseSize depth).degree u ∧ 2 < (TwoDegenerateGraphs.pairGraphOverFin baseSize depth).degree v`
- `TwoDegenerateGraphs.manuscriptVertexCount_tendsto_atTop`: `Filter.Tendsto TwoDegenerateGraphs.manuscriptVertexCount Filter.atTop Filter.atTop`
- `TwoDegenerateGraphs.pairGraph_isBipartite`: `∀ (baseSize depth : ℕ), (TwoDegenerateGraphs.pairParentSystem baseSize depth).graph.IsBipartite`
- `TwoDegenerateGraphs.isBipartite_of_iso`: `∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H), G.IsBipartite → H.IsBipartite`
- `TwoDegenerateGraphs.eventually_manuscriptVertexCount_power_le_expectedRetainedEdge`: `∀ᶠ (dimension : ℕ) in Filter.atTop, ↑(TwoDegenerateGraphs.manuscriptVertexCount dimension) ^ TwoDegenerateGraphs.manuscriptExtremalPower ≤ TwoDegenerateGraphs.hammingExpectedRetainedEdgeCount dimension (TwoDegenerateGraphs.manuscriptHammingRadius dimension) / 2`
- `TwoDegenerateGraphs.eventually_expectedRetainedEdge_le_extremalNumber`: `∃ baseSize depth, 4 ≤ baseSize ∧ 0 < depth ∧ 1 < ↑depth * (TwoDegenerateGraphs.certifiedWindowWidth / 2) ∧ ∀ᶠ (dimension : ℕ) in Filter.atTop, TwoDegenerateGraphs.hammingExpectedRetainedEdgeCount dimension (TwoDegenerateGraphs.manuscriptHammingRadius dimension) / 2 ≤ ↑(SimpleGraph.extremalNumber (TwoDegenerateGraphs.manuscriptVertexCount dimension) (TwoDegenerateGraphs.pairGraphOverFin baseSize depth))`
- `TwoDegenerateGraphs.hammingExpectedRetainedEdgeCount`: `ℕ → ℕ → ℝ`
- `TwoDegenerateGraphs.manuscriptHammingRadius`: `ℕ → ℕ`
- `TwoDegenerateGraphs.hammingRetentionProbability_mul_wordCount_eq_exp`: `∀ (dimension : ℕ), TwoDegenerateGraphs.hammingRetentionProbability dimension * ↑(2 ^ dimension) = Real.exp ((1 - TwoDegenerateGraphs.midpointBeta) * ↑dimension * Real.log 2)`
- `TwoDegenerateGraphs.log_two_pos`: `0 < Real.log 2`
- `TwoDegenerateGraphs.hammingRetentionProbability_pos`: `∀ (dimension : ℕ), 0 < TwoDegenerateGraphs.hammingRetentionProbability dimension`
- `TwoDegenerateGraphs.hammingRetentionProbability`: `ℕ → ℝ`
- `TwoDegenerateGraphs.midpointBeta_pos`: `0 < TwoDegenerateGraphs.midpointBeta`
- `TwoDegenerateGraphs.DegeneracyConjectureStatement`: `Prop`
