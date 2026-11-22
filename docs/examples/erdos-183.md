# `ErdosProblems.MulticolourTriangleRamsey.erdos_183`

**Statement.** For $k \in \mathbb{N}$ let $r(k)$ be the $k$-colour triangle Ramsey number, that is, the least $n$ such that every $k$-edge-colouring of $K_n$ contains a monochromatic triangle (`triangleRamseyNumber`). Then the real sequence $k \mapsto r(k)^{1/k}$ tends to $+\infty$ as $k \to \infty$.

**Proof idea.** The whole proof is a direct appeal to the earlier result that $r(k)^{1/k} \to +\infty$, which is stated in exactly the form required; the theorem `erdos_183` is therefore an immediate corollary of the divergence of the roots of the multicolour triangle Ramsey numbers.

1. The goal is exactly the statement that the sequence $k \mapsto (r(k))^{1/k}$ of real numbers tends to $+\infty$. The proof closes it by citing the previously established theorem `divergentRamseyRoot`, which asserts precisely this divergence of the $k$-th root of the $k$-colour triangle Ramsey number; no further argument or case distinction is needed, since the two statements coincide up to the identification of the displayed function with the one in that theorem. *(lines 3040-3040)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact divergentRamseyRoot
   ```

   Goal before this step:

   ```
   ⊢ Tendsto (fun k => ↑(triangleRamseyNumber k) ^ (1 / ↑k)) atTop atTop
   ```

   </details>

## Lemmas it uses, explained

### `ErdosProblems.MulticolourTriangleRamsey.divergentRamseyRoot`

**Statement.** For $k\in\mathbb{N}$ let $r(k)$ be the $k$-colour triangle Ramsey number, the least $n$ such that every $k$-edge-colouring of $K_n$ contains a monochromatic triangle (`triangleRamseyNumber`). Then the real sequence $k\mapsto r(k)^{1/k}$ tends to $+\infty$ as $k\to\infty$.

**Proof idea.** To prove $r(k)^{1/k}\to\infty$, fix any real $b$ and let $m=\max\{3,\lceil b e^{38}\rceil\}$. For all $k\ge C(m)$ the palette colour count is large enough ($C(3)\le k$) to apply the sharp exponential lower bound, which yields a stage $H$ with $C(H)\le k<C(H+1)$ and $(H/e^{38})^{k}\le r(k)$. Since $k<C(H+1)$, monotonicity of $C$ forces $H\ge m$, hence $b\le b\,e^{38}\le \lceil b\,e^{38}\rceil\le m\le H$, i.e. $b\le H/e^{38}$. Taking $k$-th roots of $(H/e^{38})^{k}\le r(k)$ (the real-power equivalence is valid because $k>0$) gives $b\le H/e^{38}\le r(k)^{1/k}$, which is the required eventual lower bound.

1. Rewrite the claim with the order-theoretic criterion for divergence to $+\infty$ (`Filter.tendsto_atTop.mpr`): it suffices to show that for every real $b$ the inequality $b\le r(k)^{1/k}$ holds for all sufficiently large $k$. A real number $b$ is introduced as the arbitrary target. *(lines 3004-3005)*

   <details><summary>Lean and goal state</summary>

   ```lean
     apply Filter.tendsto_atTop.mpr
     intro bound
   ```

   Goal before this step:

   ```
   ⊢ Tendsto (fun k => ↑(triangleRamseyNumber k) ^ (1 / ↑k)) atTop atTop
   ```

   </details>

2. Fix the threshold $m=\max\{3,\lceil b\,e^{38}\rceil\}$, where $\lceil\cdot\rceil$ is the ceiling to a natural number, and record that $3\le m$. *(lines 3006-3007)*

   <details><summary>Lean and goal state</summary>

   ```lean
     let minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
     have hminimum : 3 ≤ minimum := Nat.le_max_left _ _
   ```

   Goal before this step:

   ```
   bound : ℝ
   ⊢ ∀ᶠ (a : ℕ) in atTop, bound ≤ ↑(triangleRamseyNumber a) ^ (1 / ↑a)
   ```

   </details>

3. Restrict to the eventually-valid range $k\ge C(m)$, with $C$ the palette colour count (`Filter.eventually_ge_atTop`). Since $k\ge C(m)$ and $3\le m$, monotonicity of the palette colour count `paletteColourCount_mono` (for $1\le H\le H'$ one has $C(H)\le C(H')$) gives $C(3)\le C(m)\le k$. The remaining goal is $b\le r(k)^{1/k}$ for such a $k$. *(lines 3008-3011)*

   <details><summary>Lean and goal state</summary>

   ```lean
     filter_upwards [Filter.eventually_ge_atTop (paletteColourCount minimum)]
       with k hk
     have hklarge : paletteColourCount 3 ≤ k :=
       (paletteColourCount_mono (by norm_num) hminimum).trans hk
   ```

   Goal before this step:

   ```
   bound : ℝ
   minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
   hminimum : 3 ≤ minimum
   ⊢ ∀ᶠ (a : ℕ) in atTop, bound ≤ ↑(triangleRamseyNumber a) ^ (1 / ↑a)
   ```

   </details>

4. Apply the sharp exponential lower bound `allColourPaletteRamsey_exponential_bound_sharp` to $k$ (legitimate because $C(3)\le k$). It produces a stage $H\ge 3$ with $C(H)\le k<C(H+1)$ and $(H/e^{38})^{k}\le r(k)$. *(lines 3012-3013)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨H, _, _, hupper, hramsey⟩ :=
       allColourPaletteRamsey_exponential_bound_sharp k hklarge
   ```

   Goal before this step:

   ```
   bound : ℝ
   minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
   hminimum : 3 ≤ minimum
   k : ℕ
   hk : paletteColourCount minimum ≤ k
   hklarge : paletteColourCount 3 ≤ k
   ⊢ bound ≤ ↑(triangleRamseyNumber k) ^ (1 / ↑k)
   ```

   </details>

5. Show $m\le H$ by contradiction: if $H<m$ then $H+1\le m$, so monotonicity of $C$ (applied with $1\le H+1\le m$) gives $C(H+1)\le C(m)\le k$, contradicting $k<C(H+1)$. *(lines 3014-3018)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hstage : minimum ≤ H := by
       by_contra h
       have hcolour := paletteColourCount_mono
         (by omega : 1 ≤ H + 1) (by omega : H + 1 ≤ minimum)
       omega
   ```

   Goal before this step:

   ```
   bound : ℝ
   minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
   hminimum : 3 ≤ minimum
   k : ℕ
   hk : paletteColourCount minimum ≤ k
   hklarge : paletteColourCount 3 ≤ k
   H : ℕ
   left✝¹ : 3 ≤ H
   left✝ : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hramsey : (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   ⊢ bound ≤ ↑(triangleRamseyNumber k) ^ (1 / ↑k)
   ```

   </details>

6. Establish $0<k$ as a real number: $C(3)=342>0$ (by `paletteColourCount_three`) and $C(3)\le k$, so $k>0$. *(lines 3019-3022)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hkreal : (0 : ℝ) < (k : ℝ) := by
       exact_mod_cast (lt_of_lt_of_le
         (by norm_num [paletteColourCount_three] : 0 < paletteColourCount 3)
         hklarge)
   ```

   Goal before this step:

   ```
   bound : ℝ
   minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
   hminimum : 3 ≤ minimum
   k : ℕ
   hk : paletteColourCount minimum ≤ k
   hklarge : paletteColourCount 3 ≤ k
   H : ℕ
   left✝¹ : 3 ≤ H
   left✝ : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hramsey : (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   hstage : minimum ≤ H
   ⊢ bound ≤ ↑(triangleRamseyNumber k) ^ (1 / ↑k)
   ```

   </details>

7. First comparison of the calculation: $b\le H/e^{38}$. Multiplying by the positive number $e^{38}$ (using `le_div_iff₀`), this becomes $b\,e^{38}\le H$, which follows from $b\,e^{38}\le\lceil b\,e^{38}\rceil\le m\le H$ (ceiling, the definition of $m$, and the previous step). *(lines 3023-3028)*

   <details><summary>Lean and goal state</summary>

   ```lean
     calc
       bound ≤ (H : ℝ) / Real.exp 38 := by
         apply (le_div_iff₀ (Real.exp_pos 38)).mpr
         exact (Nat.le_ceil _).trans (by
           exact_mod_cast
             (Nat.le_max_right 3 ⌈bound * Real.exp 38⌉₊).trans hstage)
   ```

   Goal before this step:

   ```
   bound : ℝ
   minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
   hminimum : 3 ≤ minimum
   k : ℕ
   hk : paletteColourCount minimum ≤ k
   hklarge : paletteColourCount 3 ≤ k
   H : ℕ
   left✝¹ : 3 ≤ H
   left✝ : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hramsey : (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   hstage : minimum ≤ H
   hkreal : 0 < ↑k
   ⊢ bound ≤ ↑(triangleRamseyNumber k) ^ (1 / ↑k)
   ```

   </details>

8. Second comparison: $H/e^{38}\le r(k)^{1/k}$. The equivalence `Real.le_rpow_inv_iff_of_pos` — for nonnegative reals $a,b$ and positive $c$, $a\le b^{1/c}$ iff $a^{c}\le b$ — reduces it, with $c=k$, $a=H/e^{38}$, $b=r(k)$, to $(H/e^{38})^{k}\le r(k)$ (the nonnegativity side conditions hold by positivity, the positivity of $k$ was just proved, and the real power with natural exponent is converted to an ordinary power). That inequality is exactly the bound obtained from the sharp exponential bound theorem. *(lines 3029-3033)*

   <details><summary>Lean and goal state</summary>

   ```lean
       _ ≤ (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
         simpa only [one_div] using
           (Real.le_rpow_inv_iff_of_pos
             (by positivity) (by positivity) hkreal).mpr
               (by simpa [Real.rpow_natCast] using hramsey)
   ```

   Goal before this step:

   ```
   bound : ℝ
   minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
   hminimum : 3 ≤ minimum
   k : ℕ
   hk : paletteColourCount minimum ≤ k
   hklarge : paletteColourCount 3 ≤ k
   H : ℕ
   left✝¹ : 3 ≤ H
   left✝ : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hramsey : (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   hstage : minimum ≤ H
   hkreal : 0 < ↑k
   ⊢ ↑H / Real.exp 38 ≤ ↑(triangleRamseyNumber k) ^ (1 / ↑k)
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.paletteColourCount_three`

**Statement.** The palette colour count at stage $3$ is $342$. Here, for $H$, $C(H)=H\cdot L(H)\cdot s_H$ (`paletteColourCount`), where $L(H)=\max(2,\lceil\log H\rceil)$ (`paletteLogWidth`), $w_H=\lceil 2H\log H\rceil$ (`saturatedMatrixWidth`), and $s_H=w_H(w_H+1)+1$ (`saturatedMatrixRows`).

**Proof idea.** This is a direct evaluation of the palette colour count at $H=3$. Two numerical estimates on $\log 3$ pin down the ceilings $\lceil\log3\rceil=2$ and $\lceil6\log3\rceil=7$; these give $L(3)=2$ and $w_3=7$, hence $s_3=57$ and $C(3)=3\cdot2\cdot57=342$.

1. Using the numerical bounds for $\log 3$ named `Real.log_three_gt_d9` and `Real.log_three_lt_d9`, the proof records $1<\log 3$ and $\log 3<7/6$; both follow by linear arithmetic from those cited bounds. *(lines 2698-2701)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hlo : (1 : ℝ) < Real.log 3 := by
       nlinarith [Real.log_three_gt_d9]
     have hhi : Real.log (3 : ℝ) < 7 / 6 := by
       nlinarith [Real.log_three_lt_d9]
   ```

   Goal before this step:

   ```
   ⊢ paletteColourCount 3 = 342
   ```

   </details>

2. It computes $\lceil\log 3\rceil=2$. The criterion `Nat.ceil_eq_iff` says that for positive $n$, $\lceil x\rceil=n$ is equivalent to $n-1<x\le n$. With $n=2$ this reduces the goal to $1<\log 3$ and $\log 3\le2$; the first is the lower bound just recorded, and the second follows from $\log 3<7/6<2$. Hence $L(3)=\max(2,2)=2$. *(lines 2702-2704)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have ha : ⌈Real.log (3 : ℝ)⌉₊ = 2 := by
       apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr
       constructor <;> norm_num <;> linarith
   ```

   Goal before this step:

   ```
   hlo : 1 < Real.log 3
   hhi : Real.log 3 < 7 / 6
   ⊢ paletteColourCount 3 = 342
   ```

   </details>

3. It computes $\lceil6\log 3\rceil=7$ by the same ceiling criterion with $n=7$: it is enough to prove $6<6\log 3$ and $6\log 3\le7$. The first follows from $1<\log 3$, and the second from $\log 3<7/6$; nonlinear arithmetic closes both. Thus $w_3=\lceil 2\cdot3\log3\rceil=7$. *(lines 2705-2707)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hm : ⌈(6 : ℝ) * Real.log (3 : ℝ)⌉₊ = 7 := by
       apply (Nat.ceil_eq_iff (by norm_num : (7 : ℕ) ≠ 0)).mpr
       constructor <;> norm_num <;> nlinarith
   ```

   Goal before this step:

   ```
   hlo : 1 < Real.log 3
   hhi : Real.log 3 < 7 / 6
   ha : ⌈Real.log 3⌉₊ = 2
   ⊢ paletteColourCount 3 = 342
   ```

   </details>

4. Finally the proof unfolds the definitions and substitutes $L(3)=2$ and $w_3=7$. Therefore $s_3=7(7+1)+1=57$, and $C(3)=3\cdot(2\cdot57)=342$. *(lines 2708-2709)*

   <details><summary>Lean and goal state</summary>

   ```lean
     norm_num [paletteColourCount, paletteLogWidth,
       saturatedMatrixRows, saturatedMatrixWidth, ha, hm]
   ```

   Goal before this step:

   ```
   hlo : 1 < Real.log 3
   hhi : Real.log 3 < 7 / 6
   ha : ⌈Real.log 3⌉₊ = 2
   hm : ⌈6 * Real.log 3⌉₊ = 7
   ⊢ paletteColourCount 3 = 342
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.allColourPaletteRamsey_exponential_bound_sharp`

**Statement.** Let $k$ be a natural number with $C(3)\le k$, where $C(H)=H\,L(H)\,s_H$ is the palette colour count at stage $H$ (`paletteColourCount`), with palette log-width $L(H)=\max\{2,\lceil\log H\rceil\}$ (`paletteLogWidth`), $w_H=\lceil 2H\log H\rceil$ and $s_H=w_H(w_H+1)+1$. Then there is a natural number $H\ge 3$ such that $C(H)\le k<C(H+1)$ and $$\left(\frac{H}{e^{38}}\right)^{k}\le r(k),$$ where $r(k)$ is the $k$-colour triangle Ramsey number, the least $n$ such that every $k$-edge-colouring of $K_n$ contains a monochromatic triangle.

**Proof idea.** The proof picks the stage $H$ at which the palette colour count crosses $k$: $C(H)\le k<C(H+1)$, with $H\ge 2$ from the bracketing lemma and $H\ge 3$ because $k\ge C(3)$. The crossing inequality is converted into the ratio bound $L(H)k\le (L(H)+34)C(H)$ by multiplying by $L(H)$ and applying the adjacent scaled estimate. That ratio bound is exactly what the transfer lemma needs to pass from exponent $k$ and base $e^{-38}$ to exponent $C(H)$ and base $e^{-4}$, i.e. $(H/e^{38})^k\le (H/e^{4})^{C(H)}$; the recursive palette Ramsey bound then bounds the right side by $r(C(H))$, and monotonicity of $r$ in the number of colours replaces $C(H)$ by $k$. This shows the exponential bound is sharp at every $k$ at or above $C(3)$.

1. Since $C$ is monotone in the stage (`paletteColourCount_mono`, applied to $1\le 2\le 3$), we get $C(2)\le C(3)$, and hence $C(2)\le k$ by the hypothesis $C(3)\le k$. *(lines 2564-2565)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have htwo : paletteColourCount 2 ≤ paletteColourCount 3 :=
       paletteColourCount_mono (by omega) (by omega)
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   ⊢ ∃ H,
       3 ≤ H ∧
         paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) ∧ (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   ```

   </details>

2. Apply the bracketing result `exists_paletteStage_bracket`: from $C(2)\le k$ it produces a stage $H$ with $H\ge 2$, $C(H)\le k$ and $k<C(H+1)$. *(lines 2566-2567)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨H, hH, hlower, hupper⟩ :=
       exists_paletteStage_bracket k (htwo.trans hk)
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   htwo : paletteColourCount 2 ≤ paletteColourCount 3
   ⊢ ∃ H,
       3 ≤ H ∧
         paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) ∧ (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   ```

   </details>

3. Upgrade $H\ge 2$ to $H\ge 3$. If not, then $H=2$, and the upper bound $k<C(H+1)$ becomes $k<C(3)$, contradicting the hypothesis $C(3)\le k$. *(lines 2568-2572)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hthree : 3 ≤ H := by
       by_contra hnot
       have htwoeq : H = 2 := by omega
       subst H
       exact (Nat.not_lt_of_ge hk) (by simpa using hupper)
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   htwo : paletteColourCount 2 ≤ paletteColourCount 3
   H : ℕ
   hH : 2 ≤ H
   hlower : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   ⊢ ∃ H,
       3 ≤ H ∧
         paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) ∧ (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   ```

   </details>

4. Derive the ratio inequality $L(H)\,k\le (L(H)+34)\,C(H)$: multiply $k\le C(H+1)$ (from the strict upper bound) by $L(H)$, and then use the adjacent scaled estimate `paletteColourCount_adjacent_scaled_sharp` at $H\ge 3$, which states $L(H)\,C(H+1)\le (L(H)+34)\,C(H)$. *(lines 2573-2578)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hratio :
         paletteLogWidth H * k ≤
           (paletteLogWidth H + 34) * paletteColourCount H := by
       exact (Nat.mul_le_mul_left (paletteLogWidth H)
         (Nat.le_of_lt hupper)).trans
           (paletteColourCount_adjacent_scaled_sharp H hthree)
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   htwo : paletteColourCount 2 ≤ paletteColourCount 3
   H : ℕ
   hH : 2 ≤ H
   hlower : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hthree : 3 ≤ H
   ⊢ ∃ H,
       3 ≤ H ∧
         paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) ∧ (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   ```

   </details>

5. Choose $H$ as the witness, supplying $3\le H$, $C(H)\le k$ and $k<C(H+1)$; only the exponential inequality $((H)/e^{38})^k\le r(k)$ remains. *(lines 2579-2579)*

   <details><summary>Lean and goal state</summary>

   ```lean
     refine ⟨H, hthree, hlower, hupper, ?_⟩
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   htwo : paletteColourCount 2 ≤ paletteColourCount 3
   H : ℕ
   hH : 2 ≤ H
   hlower : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hthree : 3 ≤ H
   hratio : paletteLogWidth H * k ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ⊢ ∃ H,
       3 ≤ H ∧
         paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) ∧ (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   ```

   </details>

6. First comparison of the calculation: apply the transfer estimate `palette_exponential_adjacent_transfer_sharp` with $H\ge 3$, $a=L(H)$, $k_0=C(H)$ and $k=k$. Its hypotheses are exactly $\log H\le L(H)$ (`log_le_paletteLogWidth`), $C(H)\le k$, and $L(H)\,k\le (L(H)+34)\,C(H)$; it yields $(H/e^{38})^k\le (H/e^{4})^{C(H)}$. *(lines 2580-2585)*

   <details><summary>Lean and goal state</summary>

   ```lean
     calc
       ((H : ℝ) / Real.exp 38) ^ k ≤
           ((H : ℝ) / Real.exp 4) ^ paletteColourCount H :=
         palette_exponential_adjacent_transfer_sharp H (paletteLogWidth H)
           (paletteColourCount H) k hthree
           (log_le_paletteLogWidth H) hlower hratio
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   htwo : paletteColourCount 2 ≤ paletteColourCount 3
   H : ℕ
   hH : 2 ≤ H
   hlower : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hthree : 3 ≤ H
   hratio : paletteLogWidth H * k ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ⊢ (↑H / Real.exp 38) ^ k ≤ ↑(triangleRamseyNumber k)
   ```

   </details>

7. Second comparison: the recursive palette Ramsey bound `recursivePaletteRamsey_exponential_bound` at $H$ and $a=L(H)$ — applicable since $H\ge 2$, $L(H)\ge 2$ (`paletteLogWidth_two_le`) and $\log H\le L(H)$ — gives $(H/e^{4})^{H\,L(H)\,s_H}\le r(H\,L(H)\,s_H)$. Unfolding the definition of the palette colour count turns the exponent into $C(H)$, so this is $(H/e^{4})^{C(H)}\le r(C(H))$. *(lines 2586-2590)*

   <details><summary>Lean and goal state</summary>

   ```lean
       _ ≤ (triangleRamseyNumber (paletteColourCount H) : ℝ) :=
         by
           simpa [paletteColourCount] using
             recursivePaletteRamsey_exponential_bound H (paletteLogWidth H)
               (by omega) (paletteLogWidth_two_le H) (log_le_paletteLogWidth H)
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   htwo : paletteColourCount 2 ≤ paletteColourCount 3
   H : ℕ
   hH : 2 ≤ H
   hlower : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hthree : 3 ≤ H
   hratio : paletteLogWidth H * k ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ⊢ (↑H / Real.exp 4) ^ paletteColourCount H ≤ ↑(triangleRamseyNumber (paletteColourCount H))
   ```

   </details>

8. Finally, $r$ is monotone (`triangleRamseyNumber_mono`), so $C(H)\le k$ gives $r(C(H))\le r(k)$; casting this natural-number inequality to the reals closes the last link of the chain. *(lines 2591-2592)*

   <details><summary>Lean and goal state</summary>

   ```lean
       _ ≤ (triangleRamseyNumber k : ℝ) := by
         exact_mod_cast triangleRamseyNumber_mono hlower
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 3 ≤ k
   htwo : paletteColourCount 2 ≤ paletteColourCount 3
   H : ℕ
   hH : 2 ≤ H
   hlower : paletteColourCount H ≤ k
   hupper : k < paletteColourCount (H + 1)
   hthree : 3 ≤ H
   hratio : paletteLogWidth H * k ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ⊢ ↑(triangleRamseyNumber (paletteColourCount H)) ≤ ↑(triangleRamseyNumber k)
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.palette_exponential_adjacent_transfer_sharp`

**Statement.** Let $H,a,k_0,k$ be natural numbers such that $H\ge 3$, $\log H\le a$ (with $H$ viewed as a real number and $\log$ the natural logarithm), $k_0\le k$, and $ak\le (a+34)k_0$. Then
\[
\left(\frac{H}{e^{38}}\right)^k \le \left(\frac{H}{e^4}\right)^{k_0}.
\]

**Proof idea.** The proof takes logarithms of both sides, turning the exponential comparison into the linear inequality $k(\log H-38)\le k_0(\log H-4)$. The hypothesis $\log H\le a$, multiplied by the nonnegative factor $k-k_0$, together with the multiplicative slack $ak\le(a+34)k_0$ and $k_0\le k$, pays for replacing the exponent $38$ by $4$.

1. Since $H\ge 3$, the natural number $H$ is positive as a real number. Hence both bases $H/e^{38}$ and $H/e^4$ are positive, so both powers are positive; these positivity facts are needed for the logarithmic comparison that follows. *(lines 2539-2541)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
     have htarget : 0 < ((H : ℝ) / Real.exp 38) ^ k := by positivity
     have hsource : 0 < ((H : ℝ) / Real.exp 4) ^ k₀ := by positivity
   ```

   Goal before this step:

   ```
   H a k₀ k : ℕ
   hH : 3 ≤ H
   hlog : Real.log ↑H ≤ ↑a
   hk₀ : k₀ ≤ k
   hratio : a * k ≤ (a + 34) * k₀
   ⊢ (↑H / Real.exp 38) ^ k ≤ (↑H / Real.exp 4) ^ k₀
   ```

   </details>

2. Cast the integer inequalities to real inequalities: $ak\le(a+34)k_0$ and $0\le k-k_0$ from $k_0\le k$. Multiplying $\log H\le a$ by the nonnegative factor $k-k_0$ gives \[
(k-k_0)\log H\le (k-k_0)a.
\] *(lines 2542-2548)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hratioReal :
         (a : ℝ) * (k : ℝ) ≤
           ((a : ℝ) + 34) * (k₀ : ℝ) := by
       exact_mod_cast hratio
     have hdelta : 0 ≤ (k : ℝ) - (k₀ : ℝ) := by
       exact sub_nonneg.mpr (by exact_mod_cast hk₀)
     have hweighted := mul_le_mul_of_nonneg_left hlog hdelta
   ```

   Goal before this step:

   ```
   H a k₀ k : ℕ
   hH : 3 ≤ H
   hlog : Real.log ↑H ≤ ↑a
   hk₀ : k₀ ≤ k
   hratio : a * k ≤ (a + 34) * k₀
   hHpos : 0 < ↑H
   htarget : 0 < (↑H / Real.exp 38) ^ k
   hsource : 0 < (↑H / Real.exp 4) ^ k₀
   ⊢ (↑H / Real.exp 38) ^ k ≤ (↑H / Real.exp 4) ^ k₀
   ```

   </details>

3. Because both sides are positive, `Real.log_le_log_iff`, the equivalence between $x\le y$ and $\log x\le\log y$ for positive $x,y$, reduces the goal to proving \[
\log\!\left(\left(\frac{H}{e^{38}}\right)^k\right)
\le
\log\!\left(\left(\frac{H}{e^4}\right)^{k_0}\right).
\] *(lines 2549-2549)*

   <details><summary>Lean and goal state</summary>

   ```lean
     apply (Real.log_le_log_iff htarget hsource).mp
   ```

   Goal before this step:

   ```
   H a k₀ k : ℕ
   hH : 3 ≤ H
   hlog : Real.log ↑H ≤ ↑a
   hk₀ : k₀ ≤ k
   hratio : a * k ≤ (a + 34) * k₀
   hHpos : 0 < ↑H
   htarget : 0 < (↑H / Real.exp 38) ^ k
   hsource : 0 < (↑H / Real.exp 4) ^ k₀
   hratioReal : ↑a * ↑k ≤ (↑a + 34) * ↑k₀
   hdelta : 0 ≤ ↑k - ↑k₀
   hweighted : (↑k - ↑k₀) * Real.log ↑H ≤ (↑k - ↑k₀) * ↑a
   ⊢ (↑H / Real.exp 38) ^ k ≤ (↑H / Real.exp 4) ^ k₀
   ```

   </details>

4. Apply the logarithm laws $\log(x^n)=n\log x$, $\log(x/y)=\log x-\log y$, and $\log(e^t)=t$, with the side conditions $H>0$ and the exponentials nonzero. The goal becomes the linear inequality \[
k(\log H-38)\le k_0(\log H-4).
\] *(lines 2550-2553)*

   <details><summary>Lean and goal state</summary>

   ```lean
     rw [Real.log_pow, Real.log_pow,
       Real.log_div hHpos.ne' (Real.exp_ne_zero 38),
       Real.log_div hHpos.ne' (Real.exp_ne_zero 4),
       Real.log_exp, Real.log_exp]
   ```

   Goal before this step:

   ```
   H a k₀ k : ℕ
   hH : 3 ≤ H
   hlog : Real.log ↑H ≤ ↑a
   hk₀ : k₀ ≤ k
   hratio : a * k ≤ (a + 34) * k₀
   hHpos : 0 < ↑H
   htarget : 0 < (↑H / Real.exp 38) ^ k
   hsource : 0 < (↑H / Real.exp 4) ^ k₀
   hratioReal : ↑a * ↑k ≤ (↑a + 34) * ↑k₀
   hdelta : 0 ≤ ↑k - ↑k₀
   hweighted : (↑k - ↑k₀) * Real.log ↑H ≤ (↑k - ↑k₀) * ↑a
   ⊢ Real.log ((↑H / Real.exp 38) ^ k) ≤ Real.log ((↑H / Real.exp 4) ^ k₀)
   ```

   </details>

5. The remaining inequality is linear in $\log H,a,k,k_0$; equivalently it says $(k-k_0)\log H\le 38k-4k_0$. The weighted bound controls the left side by $(k-k_0)a=ak-ak_0$, the cast ratio inequality controls $ak-ak_0$ by $34k_0$, and $k_0\le k$ gives $34k_0\le 38k-4k_0$. Linear arithmetic closes the goal. *(lines 2554-2554)*

   <details><summary>Lean and goal state</summary>

   ```lean
     nlinarith
   ```

   Goal before this step:

   ```
   H a k₀ k : ℕ
   hH : 3 ≤ H
   hlog : Real.log ↑H ≤ ↑a
   hk₀ : k₀ ≤ k
   hratio : a * k ≤ (a + 34) * k₀
   hHpos : 0 < ↑H
   htarget : 0 < (↑H / Real.exp 38) ^ k
   hsource : 0 < (↑H / Real.exp 4) ^ k₀
   hratioReal : ↑a * ↑k ≤ (↑a + 34) * ↑k₀
   hdelta : 0 ≤ ↑k - ↑k₀
   hweighted : (↑k - ↑k₀) * Real.log ↑H ≤ (↑k - ↑k₀) * ↑a
   ⊢ ↑k * (Real.log ↑H - 38) ≤ ↑k₀ * (Real.log ↑H - 4)
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.paletteColourCount_adjacent_scaled_sharp`

**Statement.** Let $H\ge 3$ be a natural number. Put $L(H)=\max\{2,\lceil\log H\rceil\}$, $w_H=\lceil 2H\log H\rceil$, $s_H=w_H(w_H+1)+1$, and $C(H)=H\,L(H)\,s_H$. Then $L(H)\,C(H+1)\le (L(H)+34)\,C(H)$.

**Proof idea.** The proof isolates $a=L(H)$, compares consecutive row counts via $H s_{H+1}\le(H+14)s_H$, and proves a purely polynomial inequality $(H+1)(a+1)(H+14)\le(a+34)H^2$ from $a\le H$ and $H\ge3$. Multiplying by $s_H$ and cancelling the positive factor $H$ yields the key one-step bound $(H+1)(a+1)s_{H+1}\le(a+34)H s_H$; substituting $C(H)=H\,L(H)\,s_H$ and using $L(H+1)\le a+1$ gives the claimed sharp adjacent scaling.

1. Set $a=L(H)$, $s=s_H$ and $s'=s_{H+1}$. From `paletteLogWidth_le_stage` applied with $2\le H$ we get $a\le H$; from the first component of `stageWidths_succ_le` applied with $1\le H$ we get $L(H+1)\le a+1$; and from `saturatedMatrixRows_adjacent_scaled_sharp` we get $H s'\le (H+14)s$. The side conditions $2\le H$ and $1\le H$ are discharged by `omega`. *(lines 2486-2494)*

   <details><summary>Lean and goal state</summary>

   ```lean
     let a := paletteLogWidth H
     let s := saturatedMatrixRows H
     let s' := saturatedMatrixRows (H + 1)
     have haH : a ≤ H := by
       simpa [a] using paletteLogWidth_le_stage H (by omega)
     have ha' : paletteLogWidth (H + 1) ≤ a + 1 := by
       simpa [a] using (stageWidths_succ_le H (by omega)).1
     have hrows : H * s' ≤ (H + 14) * s := by
       simpa [s, s'] using saturatedMatrixRows_adjacent_scaled_sharp H hH
   ```

   Goal before this step:

   ```
   H : ℕ
   hH : 3 ≤ H
   ⊢ paletteLogWidth H * paletteColourCount (H + 1) ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ```

   </details>

2. Cast $3\le H$ and $a\le H$ to $\mathbb{R}$. Using these bounds, `nlinarith` proves the real inequality $(H+1)(a+1)(H+14)\le(a+34)H^2$; the nonnegative products it is given are $(15H+14)(H-a)$ and $(H-3)(18H+25)$, with the individual nonnegativities checked by `positivity`, `linarith`, and `positivity`. Transferring this inequality back across the natural-number cast gives the same polynomial inequality in $\mathbb{N}$. *(lines 2495-2507)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hHreal : (3 : ℝ) ≤ H := by exact_mod_cast hH
     have hareal : (a : ℝ) ≤ H := by exact_mod_cast haH
     have hpolyreal :
         ((H : ℝ) + 1) * ((a : ℝ) + 1) * ((H : ℝ) + 14) ≤
           ((a : ℝ) + 34) * (H : ℝ) ^ 2 := by
       nlinarith [
         mul_nonneg (show 0 ≤ 15 * (H : ℝ) + 14 by positivity)
           (sub_nonneg.mpr hareal),
         mul_nonneg (show 0 ≤ (H : ℝ) - 3 by linarith)
           (show 0 ≤ 18 * (H : ℝ) + 25 by positivity)]
     have hpoly :
         (H + 1) * (a + 1) * (H + 14) ≤ (a + 34) * H ^ 2 := by
       exact_mod_cast hpolyreal
   ```

   Goal before this step:

   ```
   H : ℕ
   hH : 3 ≤ H
   a : ℕ := paletteLogWidth H
   s : ℕ := saturatedMatrixRows H
   s' : ℕ := saturatedMatrixRows (H + 1)
   haH : a ≤ H
   ha' : paletteLogWidth (H + 1) ≤ a + 1
   hrows : H * s' ≤ (H + 14) * s
   ⊢ paletteLogWidth H * paletteColourCount (H + 1) ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ```

   </details>

3. Prove the key one-step bound $(H+1)(a+1)s'\le(a+34)H s$. Since $H>0$ (by `omega`), `Nat.le_of_mul_le_mul_left` reduces it to showing $H\cdot((H+1)(a+1)s')\le H\cdot((a+34)H s)$. The displayed calculation reassociates, applies $H s'\le(H+14)s$ under left multiplication, reassociates, applies the polynomial inequality under right multiplication by $s$, and reassociates again. *(lines 2508-2518)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hstep : (H + 1) * (a + 1) * s' ≤ (a + 34) * H * s := by
       apply Nat.le_of_mul_le_mul_left (c := H) ?_ (by omega)
       calc
         H * ((H + 1) * (a + 1) * s') =
             ((H + 1) * (a + 1)) * (H * s') := by ring
         _ ≤ ((H + 1) * (a + 1)) * ((H + 14) * s) :=
           Nat.mul_le_mul_left _ hrows
         _ = ((H + 1) * (a + 1) * (H + 14)) * s := by ring
         _ ≤ ((a + 34) * H ^ 2) * s :=
           Nat.mul_le_mul_right s hpoly
         _ = H * ((a + 34) * H * s) := by ring
   ```

   Goal before this step:

   ```
   H : ℕ
   hH : 3 ≤ H
   a : ℕ := paletteLogWidth H
   s : ℕ := saturatedMatrixRows H
   s' : ℕ := saturatedMatrixRows (H + 1)
   haH : a ≤ H
   ha' : paletteLogWidth (H + 1) ≤ a + 1
   hrows : H * s' ≤ (H + 14) * s
   hHreal : 3 ≤ ↑H
   hareal : ↑a ≤ ↑H
   hpolyreal : (↑H + 1) * (↑a + 1) * (↑H + 14) ≤ (↑a + 34) * ↑H ^ 2
   hpoly : (H + 1) * (a + 1) * (H + 14) ≤ (a + 34) * H ^ 2
   ⊢ paletteLogWidth H * paletteColourCount (H + 1) ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ```

   </details>

4. Finish with a calculation for $L(H)\,C(H+1)$. Unfolding $C(H+1)$ and $s'$ gives $L(H)\,C(H+1)=a\,((H+1)L(H+1)s')$. Since $L(H+1)\le a+1$, `gcongr` gives $\le a\,((H+1)(a+1)s')$; the key one-step bound gives $\le a\,((a+34)H s)$; finally unfolding $C(H)$ and $s$ and rearranging gives equality with $(L(H)+34)\,C(H)$. *(lines 2519-2529)*

   <details><summary>Lean and goal state</summary>

   ```lean
     calc
       paletteLogWidth H * paletteColourCount (H + 1) =
           a * ((H + 1) * paletteLogWidth (H + 1) * s') := by
         simp only [a, s', paletteColourCount]
         ring
       _ ≤ a * ((H + 1) * (a + 1) * s') := by
         gcongr
       _ ≤ a * ((a + 34) * H * s) := Nat.mul_le_mul_left a hstep
       _ = (paletteLogWidth H + 34) * paletteColourCount H := by
         simp only [a, s, paletteColourCount]
         ring
   ```

   Goal before this step:

   ```
   H : ℕ
   hH : 3 ≤ H
   a : ℕ := paletteLogWidth H
   s : ℕ := saturatedMatrixRows H
   s' : ℕ := saturatedMatrixRows (H + 1)
   haH : a ≤ H
   ha' : paletteLogWidth (H + 1) ≤ a + 1
   hrows : H * s' ≤ (H + 14) * s
   hHreal : 3 ≤ ↑H
   hareal : ↑a ≤ ↑H
   hpolyreal : (↑H + 1) * (↑a + 1) * (↑H + 14) ≤ (↑a + 34) * ↑H ^ 2
   hpoly : (H + 1) * (a + 1) * (H + 14) ≤ (a + 34) * H ^ 2
   hstep : (H + 1) * (a + 1) * s' ≤ (a + 34) * H * s
   ⊢ paletteLogWidth H * paletteColourCount (H + 1) ≤ (paletteLogWidth H + 34) * paletteColourCount H
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth_two_le`

**Statement.** For every natural number $H$, the palette log-width $L(H)=\max\{2,\lceil \log H\rceil\}$ is at least $2$.

**Proof idea.** The bound is read straight off the definition: $L(H)$ is by construction a maximum whose first entry is $2$, and a maximum dominates each of its entries, so $L(H)\ge 2$ for every $H$.

1. The definition of $L(H)$ (`paletteLogWidth`) is $\max\{2,\lceil \log H\rceil\}$, where $\lceil \log H\rceil$ is the natural-number ceiling of the real logarithm of $H$ (as a natural number, the ceiling of a logarithm of $0$ or $1$ being $0$). The claim $2 \le \max\{2,\lceil\log H\rceil\}$ is the left half of the defining maximum, so it is immediate for every $H$; no case distinction or estimate on $H$ is needed. *(lines 2248-2248)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact Nat.le_max_left _ _
   ```

   Goal before this step:

   ```
   H : ℕ
   ⊢ 2 ≤ paletteLogWidth H
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.log_le_paletteLogWidth`

**Statement.** For every natural number $H$, let the palette log-width be $L(H) = \max\{2, \lceil \log H \rceil\}$, where $\lceil x\rceil$ denotes the least natural number $\ge x$ and $\log$ is the real logarithm. Then $\log H \le L(H)$.

**Proof idea.** The palette log-width is by definition the maximum of $2$ and $\lceil \log H\rceil$, and $\log H$ is bounded by its own ceiling, so it is bounded by that maximum.

1. Prove the claim by a two-step chain of inequalities. The first step is $\log H \le \lceil \log H\rceil$, the defining property of the natural-number ceiling (`Nat.le_ceil`), applied to the real number $\log H$. *(lines 2252-2254)*

   <details><summary>Lean and goal state</summary>

   ```lean
     calc
       Real.log (H : ℝ) ≤ (⌈Real.log (H : ℝ)⌉₊ : ℝ) :=
         Nat.le_ceil _
   ```

   Goal before this step:

   ```
   H : ℕ
   ⊢ Real.log ↑H ≤ ↑(paletteLogWidth H)
   ```

   </details>

2. The second step is $\lceil \log H\rceil \le \max\{2, \lceil \log H\rceil\} = L(H)$: the ceiling is the right-hand entry of the maximum (`Nat.le_max_right`). Both sides are natural numbers here, so the inequality is transported to the reals by casting. Chaining the two gives $\log H \le L(H)$. *(lines 2255-2256)*

   <details><summary>Lean and goal state</summary>

   ```lean
       _ ≤ (paletteLogWidth H : ℝ) := by
         exact_mod_cast (Nat.le_max_right 2 ⌈Real.log (H : ℝ)⌉₊)
   ```

   Goal before this step:

   ```
   H : ℕ
   ⊢ ↑⌈Real.log ↑H⌉₊ ≤ ↑(paletteLogWidth H)
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.exists_paletteStage_bracket`

**Statement.** Let $k$ be a natural number with $C(2)\le k$, where $C(H)$ is the palette colour count at stage $H$, namely $C(H)=H\bigl(\max(2,\lceil\log H\rceil)\,s_H\bigr)$, with $s_H=w_H(w_H+1)+1$ and $w_H=\lceil 2H\log H\rceil$ (the ceiling is taken in $\mathbb N$). Then there exists $H\ge 2$ such that $C(H)\le k<C(H+1)$.

**Proof idea.** The proof looks at the least stage $M$ at which the nondecreasing colour count $C(M)$ exceeds $k$. It must exist because $C(H)\ge 2H$. The base condition $C(2)\le k$ and monotonicity on positive stages force $M>2$, so $H=M-1$ is at least $2$. Minimality of $M$ gives $C(M-1)\le k$, while $k<C(M)=C(M-1+1)$, producing the required bracket.

1. There is some $H$ with $k<C(H)$: choose $H=k+1$. Since $2H\le C(H)$ for every $H$ (`two_mul_stage_le_paletteColourCount`), we have $2(k+1)\le C(k+1)$, and linear arithmetic gives $k<C(k+1)$. *(lines 2401-2404)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hexists : ∃ H : ℕ, k < paletteColourCount H := by
       refine ⟨k + 1, ?_⟩
       have hcount := two_mul_stage_le_paletteColourCount (k + 1)
       omega
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 2 ≤ k
   ⊢ ∃ H, 2 ≤ H ∧ paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1)
   ```

   </details>

2. Let $M$ be the least natural number satisfying $k<C(M)$ (Lean's `Nat.find` applied to the existence statement just proved). Then `Nat.find_spec` gives $k<C(M)$. *(lines 2405-2406)*

   <details><summary>Lean and goal state</summary>

   ```lean
     let M : ℕ := Nat.find hexists
     have hM : k < paletteColourCount M := Nat.find_spec hexists
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 2 ≤ k
   hexists : ∃ H, k < paletteColourCount H
   ⊢ ∃ H, 2 ≤ H ∧ paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1)
   ```

   </details>

3. Show that $M\ge 1$. If $M=0$, then the definition of the colour count gives $C(0)=0$, contradicting $k<C(M)$. *(lines 2407-2410)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hMpos : 1 ≤ M := by
       by_contra hnot
       have hzero : M = 0 := by omega
       simp [hzero, paletteColourCount] at hM
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 2 ≤ k
   hexists : ∃ H, k < paletteColourCount H
   M : ℕ := Nat.find hexists
   hM : k < paletteColourCount M
   ⊢ ∃ H, 2 ≤ H ∧ paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1)
   ```

   </details>

4. Show that $2<M$. If instead $M\le 2$, then since $1\le M$, monotonicity of the colour count on positive stages (`paletteColourCount_mono`) gives $C(M)\le C(2)$. Together with the hypothesis $C(2)\le k$, this gives $C(M)\le k$, contradicting $k<C(M)$. *(lines 2411-2415)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hMlarge : 2 < M := by
       by_contra hnot
       have hMtwo : M ≤ 2 := by omega
       have hmono := paletteColourCount_mono hMpos hMtwo
       omega
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 2 ≤ k
   hexists : ∃ H, k < paletteColourCount H
   M : ℕ := Nat.find hexists
   hM : k < paletteColourCount M
   hMpos : 1 ≤ M
   ⊢ ∃ H, 2 ≤ H ∧ paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1)
   ```

   </details>

5. Choose the stage $H=M-1$. The inequality $2<M$ implies $H\ge 2$. *(lines 2416-2416)*

   <details><summary>Lean and goal state</summary>

   ```lean
     refine ⟨M - 1, by omega, ?_, ?_⟩
   ```

   Goal before this step:

   ```
   k : ℕ
   hk : paletteColourCount 2 ≤ k
   hexists : ∃ H, k < paletteColourCount H
   M : ℕ := Nat.find hexists
   hM : k < paletteColourCount M
   hMpos : 1 ≤ M
   hMlarge : 2 < M
   ⊢ ∃ H, 2 ≤ H ∧ paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1)
   ```

   </details>

6. For the lower bracket inequality, $M-1<M$, so minimality of $M$ (`Nat.find_min`) gives $\neg(k<C(M-1))$, which for natural numbers is exactly $C(M-1)\le k$. *(lines 2417-2420)*

   <details><summary>Lean and goal state</summary>

   ```lean
     · have hminimal :=
         Nat.find_min hexists (show M - 1 < M by omega)
       change ¬ k < paletteColourCount (M - 1) at hminimal
       omega
   ```

   Goal before this step:

   ```
   case refine_1
   k : ℕ
   hk : paletteColourCount 2 ≤ k
   hexists : ∃ H, k < paletteColourCount H
   M : ℕ := Nat.find hexists
   hM : k < paletteColourCount M
   hMpos : 1 ≤ M
   hMlarge : 2 < M
   ⊢ paletteColourCount (M - 1) ≤ k
   ```

   </details>

7. For the upper bracket inequality, $M-1+1=M$; substituting this into $k<C(M)$ gives $k<C(M-1+1)$. *(lines 2421-2422)*

   <details><summary>Lean and goal state</summary>

   ```lean
     · have hsucc : M - 1 + 1 = M := by omega
       simpa [hsucc] using hM
   ```

   Goal before this step:

   ```
   case refine_2
   k : ℕ
   hk : paletteColourCount 2 ≤ k
   hexists : ∃ H, k < paletteColourCount H
   M : ℕ := Nat.find hexists
   hM : k < paletteColourCount M
   hMpos : 1 ≤ M
   hMlarge : 2 < M
   ⊢ k < paletteColourCount (M - 1 + 1)
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.recursivePaletteRamsey_exponential_bound`

**Statement.** Let $H$ and $a$ be natural numbers with $H\ge 2$, $a\ge 2$ and $\log H\le a$. Put $w_H=\lceil 2H\log H\rceil$ (the saturated matrix width, `saturatedMatrixWidth`) and $s_H=w_H(w_H+1)+1$ (the saturated matrix row count, `saturatedMatrixRows`). Then the $H a s_H$-colour triangle Ramsey number satisfies, as a real inequality,
$$\left(\frac{H}{e^{4}}\right)^{H\,a\,s_H}\le r\bigl(H\,a\,s_H\bigr).$$

**Proof idea.** The proof instantiates the recursive palette construction at $j=H$, which produces a triangle-free colouring of $K_n$ with $H a s$ colours obeying the palette growth bound $(H!)^{as}\le n\,s^{H}(e^{2}a^{2})^{sH}(H!)^{s}$, where $s=s_H$. Triangle-freeness forces $n<r(H a s)$, so after cancelling $(H!)^{s}$ and replacing $n$ by $r(Has)$ one obtains $(H!)^{(a-1)s}\le r(Has)\,s^{H}(e^{2}a^{2})^{sH}$. On the other hand the loss estimate bounds $(H/e^{4})^{Has}$ by $(H/e)^{H(a-1)s}$ divided by $s^{H}(e^{2}a^{2})^{sH}$; clearing this denominator, bounding $(H/e)^{H}$ by $H!$ and raising to the power $(a-1)s$ turns the required inequality into exactly the cancelled growth bound.

1. Apply the recursive palette stage construction `exists_recursivePaletteStage` with $j=H$ (permissible since $H\le H$), to the effect that for $s=s_H$ there are $n$ and a colouring $C$ of the edges of $K_n$ with $H\,a\,s$ colours that is triangle-free — meaning each of its colour graphs contains no triangle (`TriangleFree`) — all of whose colour graphs are $(H+1)$-colourable (this hypothesis is never used and is discarded), and that satisfies the palette growth bound `PaletteGrowthBound`, i.e.
$$(H!)^{a s}\le n\cdot s^{H}\cdot\bigl(e^{2}a^{2}\bigr)^{sH}\cdot (H!)^{s}.$$
Because a triangle-free $H a s$-colouring of $K_n$ exists, the defining minimality of $r$ (`triangleFree_lt_triangleRamseyNumber`) yields $n<r(H a s)$. *(lines 2166-2168)*

   <details><summary>Lean and goal state</summary>

   ```lean
     obtain ⟨n, C, htriangle, _, hgrowth⟩ :=
       exists_recursivePaletteStage H a H hH ha le_rfl
     have hramsey := triangleFree_lt_triangleRamseyNumber C htriangle
   ```

   Goal before this step:

   ```
   H a : ℕ
   hH : 2 ≤ H
   ha : 2 ≤ a
   hloga : Real.log ↑H ≤ ↑a
   ⊢ (↑H / Real.exp 4) ^ (H * (a * saturatedMatrixRows H)) ≤ ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H)))
   ```

   </details>

2. Record two positivity facts used later: $s=s_H=w_H(w_H+1)+1>0$, and consequently the denominator
$$D=s^{H}\cdot\bigl(e^{2}a^{2}\bigr)^{sH}$$
is strictly positive (a positivity check). *(lines 2169-2175)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hs : 0 < saturatedMatrixRows H := by
       simp [saturatedMatrixRows]
     have hden :
         0 < (saturatedMatrixRows H : ℝ) ^ H *
           (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
             (saturatedMatrixRows H * H) := by
       positivity
   ```

   Goal before this step:

   ```
   H a : ℕ
   hH : 2 ≤ H
   ha : 2 ≤ a
   hloga : Real.log ↑H ≤ ↑a
   n : ℕ
   C : TopEdgeLabeling (Fin n) (Fin (H * (a * saturatedMatrixRows H)))
   htriangle : TriangleFree C
   left✝ : ∀ (colour : Fin (H * (a * saturatedMatrixRows H))), (EdgeLabeling.labelGraph C colour).Colorable (H + 1)
   hgrowth : PaletteGrowthBound a (saturatedMatrixRows H) H n
   hramsey : n < triangleRamseyNumber (H * (a * saturatedMatrixRows H))
   ⊢ (↑H / Real.exp 4) ^ (H * (a * saturatedMatrixRows H)) ≤ ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H)))
   ```

   </details>

3. Split the exponent: $a\,s=(a-1)s+s$, since $a\ge 1$. Unfolding `PaletteGrowthBound` and substituting this splitting, then using $x^{u+v}=x^{u}x^{v}$, turns the growth bound into
$$(H!)^{(a-1)s}\cdot (H!)^{s}\le n\cdot s^{H}\cdot\bigl(e^{2}a^{2}\bigr)^{sH}\cdot (H!)^{s}.$$ *(lines 2176-2187)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hsplit :
         a * saturatedMatrixRows H =
           (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
       calc
         a * saturatedMatrixRows H =
             ((a - 1) + 1) * saturatedMatrixRows H := by
           rw [Nat.sub_add_cancel (by omega)]
         _ = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
           simp [Nat.add_mul]
     unfold PaletteGrowthBound at hgrowth
     nth_rewrite 1 [hsplit] at hgrowth
     rw [pow_add] at hgrowth
   ```

   Goal before this step:

   ```
   H a : ℕ
   hH : 2 ≤ H
   ha : 2 ≤ a
   hloga : Real.log ↑H ≤ ↑a
   n : ℕ
   C : TopEdgeLabeling (Fin n) (Fin (H * (a * saturatedMatrixRows H)))
   htriangle : TriangleFree C
   left✝ : ∀ (colour : Fin (H * (a * saturatedMatrixRows H))), (EdgeLabeling.labelGraph C colour).Colorable (H + 1)
   hgrowth : PaletteGrowthBound a (saturatedMatrixRows H) H n
   hramsey : n < triangleRamseyNumber (H * (a * saturatedMatrixRows H))
   hs : 0 < saturatedMatrixRows H
   hden : 0 < ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   ⊢ (↑H / Real.exp 4) ^ (H * (a * saturatedMatrixRows H)) ≤ ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H)))
   ```

   </details>

4. Cancel the positive factor $(H!)^{s}$ from both sides, giving $(H!)^{(a-1)s}\le n\,s^{H}(e^{2}a^{2})^{sH}$. Then replace $n$ by the larger quantity $r(H a s)$: multiplying $n<r(Has)$ by the nonnegative common factor $s^{H}(e^{2}a^{2})^{sH}(H!)^{s}$ and chaining with the previous inequality gives
$$(H!)^{(a-1)s}\le r(H a s)\cdot s^{H}\cdot\bigl(e^{2}a^{2}\bigr)^{sH},$$
recorded as `hcancel`. *(lines 2188-2210)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hfactor : 0 < (H.factorial : ℝ) ^ saturatedMatrixRows H := by
       positivity
     have hcancel :
         (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) ≤
           (triangleRamseyNumber (H * (a * saturatedMatrixRows H)) : ℝ) *
             (saturatedMatrixRows H : ℝ) ^ H *
             (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
               (saturatedMatrixRows H * H) := by
       apply le_of_mul_le_mul_right ?_ hfactor
       calc
         (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) *
             (H.factorial : ℝ) ^ saturatedMatrixRows H ≤
           (n : ℝ) * (saturatedMatrixRows H : ℝ) ^ H *
             (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
               (saturatedMatrixRows H * H) *
             (H.factorial : ℝ) ^ saturatedMatrixRows H := hgrowth
         _ ≤ (triangleRamseyNumber
               (H * (a * saturatedMatrixRows H)) : ℝ) *
             (saturatedMatrixRows H : ℝ) ^ H *
             (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
               (saturatedMatrixRows H * H) *
             (H.factorial : ℝ) ^ saturatedMatrixRows H := by
           gcongr
   ```

   Goal before this step:

   ```
   H a : ℕ
   hH : 2 ≤ H
   ha : 2 ≤ a
   hloga : Real.log ↑H ≤ ↑a
   n : ℕ
   C : TopEdgeLabeling (Fin n) (Fin (H * (a * saturatedMatrixRows H)))
   htriangle : TriangleFree C
   left✝ : ∀ (colour : Fin (H * (a * saturatedMatrixRows H))), (EdgeLabeling.labelGraph C colour).Colorable (H + 1)
   hgrowth :
     ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) * ↑H.factorial ^ saturatedMatrixRows H ≤
       ↑n * ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H) *
         ↑H.factorial ^ saturatedMatrixRows H
   hramsey : n < triangleRamseyNumber (H * (a * saturatedMatrixRows H))
   hs : 0 < saturatedMatrixRows H
   hden : 0 < ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   hsplit : a * saturatedMatrixRows H = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H
   ⊢ (↑H / Real.exp 4) ^ (H * (a * saturatedMatrixRows H)) ≤ ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H)))
   ```

   </details>

5. The loss estimate `palette_exp_loss_bound`, applied with $H$, $a$ and $s=s_H$ (using $H\ge2$, $a\ge 2$, $s>0$ and $\log H\le a$), gives the first link of the final chain:
$$\left(\frac{H}{e^{4}}\right)^{H a s}\le \frac{\left(\frac{H}{e}\right)^{H((a-1)s)}}{D},\qquad D=s^{H}\bigl(e^{2}a^{2}\bigr)^{sH}.$$ *(lines 2211-2220)*

   <details><summary>Lean and goal state</summary>

   ```lean
     calc
       ((H : ℝ) / Real.exp 4) ^
           (H * (a * saturatedMatrixRows H)) ≤
         ((H : ℝ) / Real.exp 1) ^
             (H * ((a - 1) * saturatedMatrixRows H)) /
           ((saturatedMatrixRows H : ℝ) ^ H *
             (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
               (saturatedMatrixRows H * H)) :=
         palette_exp_loss_bound H a (saturatedMatrixRows H)
           hH ha hs hloga
   ```

   Goal before this step:

   ```
   H a : ℕ
   hH : 2 ≤ H
   ha : 2 ≤ a
   hloga : Real.log ↑H ≤ ↑a
   n : ℕ
   C : TopEdgeLabeling (Fin n) (Fin (H * (a * saturatedMatrixRows H)))
   htriangle : TriangleFree C
   left✝ : ∀ (colour : Fin (H * (a * saturatedMatrixRows H))), (EdgeLabeling.labelGraph C colour).Colorable (H + 1)
   hgrowth :
     ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) * ↑H.factorial ^ saturatedMatrixRows H ≤
       ↑n * ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H) *
         ↑H.factorial ^ saturatedMatrixRows H
   hramsey : n < triangleRamseyNumber (H * (a * saturatedMatrixRows H))
   hs : 0 < saturatedMatrixRows H
   hden : 0 < ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   hsplit : a * saturatedMatrixRows H = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H
   hfactor : 0 < ↑H.factorial ^ saturatedMatrixRows H
   hcancel :
     ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) ≤
       ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H))) * ↑(saturatedMatrixRows H) ^ H *
         (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   ⊢ (↑H / Real.exp 4) ^ (H * (a * saturatedMatrixRows H)) ≤ ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H)))
   ```

   </details>

6. Since $D>0$, multiplying through by $D$ (via $\mathrm{div\_le\_iff}_0$) reduces the remaining claim to
$$\left(\frac{H}{e}\right)^{H((a-1)s)}\le r(H a s)\cdot D.$$
Rewrite the left side as $\bigl((H/e)^{H}\bigr)^{(a-1)s}$ and bound $(H/e)^{H}\le H!$ by `factorial_exp_lower` (applied to $H>0$); raising this inequality to the power $(a-1)s$ gives $\bigl((H/e)^{H}\bigr)^{(a-1)s}\le (H!)^{(a-1)s}$. *(lines 2221-2233)*

   <details><summary>Lean and goal state</summary>

   ```lean
       _ ≤ (triangleRamseyNumber
           (H * (a * saturatedMatrixRows H)) : ℝ) := by
         apply (div_le_iff₀ hden).mpr
         calc
           ((H : ℝ) / Real.exp 1) ^
               (H * ((a - 1) * saturatedMatrixRows H)) =
             (((H : ℝ) / Real.exp 1) ^ H) ^
               ((a - 1) * saturatedMatrixRows H) := by
             rw [pow_mul]
           _ ≤ (H.factorial : ℝ) ^
               ((a - 1) * saturatedMatrixRows H) := by
             gcongr
             exact factorial_exp_lower H (by omega)
   ```

   Goal before this step:

   ```
   H a : ℕ
   hH : 2 ≤ H
   ha : 2 ≤ a
   hloga : Real.log ↑H ≤ ↑a
   n : ℕ
   C : TopEdgeLabeling (Fin n) (Fin (H * (a * saturatedMatrixRows H)))
   htriangle : TriangleFree C
   left✝ : ∀ (colour : Fin (H * (a * saturatedMatrixRows H))), (EdgeLabeling.labelGraph C colour).Colorable (H + 1)
   hgrowth :
     ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) * ↑H.factorial ^ saturatedMatrixRows H ≤
       ↑n * ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H) *
         ↑H.factorial ^ saturatedMatrixRows H
   hramsey : n < triangleRamseyNumber (H * (a * saturatedMatrixRows H))
   hs : 0 < saturatedMatrixRows H
   hden : 0 < ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   hsplit : a * saturatedMatrixRows H = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H
   hfactor : 0 < ↑H.factorial ^ saturatedMatrixRows H
   hcancel :
     ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) ≤
       ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H))) * ↑(saturatedMatrixRows H) ^ H *
         (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   ⊢ (↑H / Real.exp 1) ^ (H * ((a - 1) * saturatedMatrixRows H)) /
         (↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)) ≤
       ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H)))
   ```

   </details>

7. Close the chain with `hcancel`: $(H!)^{(a-1)s}\le r(H a s)\,s^{H}(e^{2}a^{2})^{sH}$, reassociated into the product form $r(Has)\cdot D$ required by the previous step. Combining the three links proves the claim. *(lines 2234-2239)*

   <details><summary>Lean and goal state</summary>

   ```lean
           _ ≤ (triangleRamseyNumber
                 (H * (a * saturatedMatrixRows H)) : ℝ) *
               ((saturatedMatrixRows H : ℝ) ^ H *
                 (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
                   (saturatedMatrixRows H * H)) := by
             simpa [mul_assoc] using hcancel
   ```

   Goal before this step:

   ```
   H a : ℕ
   hH : 2 ≤ H
   ha : 2 ≤ a
   hloga : Real.log ↑H ≤ ↑a
   n : ℕ
   C : TopEdgeLabeling (Fin n) (Fin (H * (a * saturatedMatrixRows H)))
   htriangle : TriangleFree C
   left✝ : ∀ (colour : Fin (H * (a * saturatedMatrixRows H))), (EdgeLabeling.labelGraph C colour).Colorable (H + 1)
   hgrowth :
     ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) * ↑H.factorial ^ saturatedMatrixRows H ≤
       ↑n * ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H) *
         ↑H.factorial ^ saturatedMatrixRows H
   hramsey : n < triangleRamseyNumber (H * (a * saturatedMatrixRows H))
   hs : 0 < saturatedMatrixRows H
   hden : 0 < ↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   hsplit : a * saturatedMatrixRows H = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H
   hfactor : 0 < ↑H.factorial ^ saturatedMatrixRows H
   hcancel :
     ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) ≤
       ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H))) * ↑(saturatedMatrixRows H) ^ H *
         (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H)
   ⊢ ↑H.factorial ^ ((a - 1) * saturatedMatrixRows H) ≤
       ↑(triangleRamseyNumber (H * (a * saturatedMatrixRows H))) *
         (↑(saturatedMatrixRows H) ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (saturatedMatrixRows H * H))
   ```

   </details>

### `ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_mono`

**Statement.** Let $k \le l$ be natural numbers. Then the $k$-colour triangle Ramsey number $r(k)$ is at most the $l$-colour triangle Ramsey number $r(l)$, where $r(k)$ (`triangleRamseyNumber k`) is the least $n$ such that every $k$-edge-colouring of the complete graph on $n$ vertices has a monochromatic triangle.

**Proof idea.** To prove monotonicity, take any triangle-free $k$-colouring of the complete graph on $r(l)$ vertices and regard its $k$ colours as $l$ colours. The resulting $l$-colouring is still triangle-free, but $r(l)$ was defined so that no such $l$-colouring exists. Hence $r(k) \le r(l)$.

1. Unfold $r(k)$ as the least element of the set of $n$ for which every $k$-edge-colouring of $K_n$ has a monochromatic triangle. The lemma `Nat.sInf_le` says that an element of a set of natural numbers is at least the infimum of that set; applying it reduces the goal to showing that $r(l)$ lies in this set, i.e. that every $k$-edge-colouring $C$ of $K_{r(l)}$ has a monochromatic triangle. The proof introduces such a colouring $C$ together with the hypothesis that each of its colour classes is triangle-free, and aims for a contradiction. *(lines 377-378)*

   <details><summary>Lean and goal state</summary>

   ```lean
     apply Nat.sInf_le
     intro C hC
   ```

   Goal before this step:

   ```
   k l : ℕ
   hkl : k ≤ l
   ⊢ triangleRamseyNumber k ≤ triangleRamseyNumber l
   ```

   </details>

2. View $C$ as an $l$-edge-colouring by composing with the inclusion of the $k$ colours into the $l$ colours. The lemma `cliqueFree_compRight_embedding` states that pulling a colouring back along an embedding of colour sets preserves the property that every colour class is triangle-free; applied to $C$ and this inclusion, it gives that the induced $l$-colouring is triangle-free. *(lines 379-381)*

   <details><summary>Lean and goal state</summary>

   ```lean
     have hlarge :
         TriangleFree (C.compRight (Fin.castLEEmb hkl)) :=
       cliqueFree_compRight_embedding C (Fin.castLEEmb hkl) hC
   ```

   Goal before this step:

   ```
   k l : ℕ
   hkl : k ≤ l
   C : TopEdgeLabeling (Fin (triangleRamseyNumber l)) (Fin k)
   hC : TriangleFree C
   ⊢ False
   ```

   </details>

3. The defining property of $r(l)$ (`triangleRamseyNumber_forces l`) says that every $l$-edge-colouring of $K_{r(l)}$ has a monochromatic triangle. Applying it to the induced $l$-colouring contradicts the triangle-freeness just obtained. *(lines 382-383)*

   <details><summary>Lean and goal state</summary>

   ```lean
     exact triangleRamseyNumber_forces l
       (C.compRight (Fin.castLEEmb hkl)) hlarge
   ```

   Goal before this step:

   ```
   k l : ℕ
   hkl : k ≤ l
   C : TopEdgeLabeling (Fin (triangleRamseyNumber l)) (Fin k)
   hC : TriangleFree C
   hlarge : TriangleFree (EdgeLabeling.compRight C ⇑(Fin.castLEEmb hkl))
   ⊢ False
   ```

   </details>

## Results cited without proof

- `ErdosProblems.MulticolourTriangleRamsey.ForcesMonochromaticTriangle`: `ℕ → ℕ → Prop`
- `ErdosProblems.MulticolourTriangleRamsey.cliqueFree_compRight_embedding`: `∀ {V : Type u_1} {K : Type u_2} {K' : Type u_3} (C : SimpleGraph.TopEdgeLabeling V K) (e : K ↪ K'), (∀ (colour : K), (SimpleGraph.EdgeLabeling.labelGraph C colour).CliqueFree 3) → ∀ (colour : K'), ((SimpleGraph.EdgeLabeling.compRight C ⇑e).labelGraph colour).CliqueFree 3`
- `ErdosProblems.MulticolourTriangleRamsey.TriangleFree`: `{n k : ℕ} → SimpleGraph.TopEdgeLabeling (Fin n) (Fin k) → Prop`
- `ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_forces`: `∀ (k : ℕ), ErdosProblems.MulticolourTriangleRamsey.ForcesMonochromaticTriangle (ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber k) k`
- `ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber`: `ℕ → ℕ`
- `ErdosProblems.MulticolourTriangleRamsey.exists_recursivePaletteStage`: `∀ (H a j : ℕ), 2 ≤ H → 2 ≤ a → j ≤ H → ∃ n C, ErdosProblems.MulticolourTriangleRamsey.TriangleFree C ∧ (∀ (colour : Fin (j * (a * ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows H))), (SimpleGraph.EdgeLabeling.labelGraph C colour).Colorable (j + 1)) ∧ ErdosProblems.MulticolourTriangleRamsey.PaletteGrowthBound a (ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows H) j n`
- `ErdosProblems.MulticolourTriangleRamsey.triangleFree_lt_triangleRamseyNumber`: `∀ {n k : ℕ} (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)), ErdosProblems.MulticolourTriangleRamsey.TriangleFree C → n < ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber k`
- `ErdosProblems.MulticolourTriangleRamsey.palette_exp_loss_bound`: `∀ (H a s : ℕ), 2 ≤ H → 2 ≤ a → 0 < s → Real.log ↑H ≤ ↑a → (↑H / Real.exp 4) ^ (H * (a * s)) ≤ (↑H / Real.exp 1) ^ (H * ((a - 1) * s)) / (↑s ^ H * (Real.exp 1 ^ 2 * ↑a ^ 2) ^ (s * H))`
- `ErdosProblems.MulticolourTriangleRamsey.PaletteGrowthBound`: `ℕ → ℕ → ℕ → ℕ → Prop`
- `ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixWidth`: `ℕ → ℕ`
- `ErdosProblems.MulticolourTriangleRamsey.factorial_exp_lower`: `∀ (s : ℕ), 0 < s → (↑s / Real.exp 1) ^ s ≤ ↑s.factorial`
- `ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows`: `ℕ → ℕ`
- `ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth`: `ℕ → ℕ`
- `ErdosProblems.MulticolourTriangleRamsey.paletteColourCount_mono`: `∀ {H H' : ℕ}, 1 ≤ H → H ≤ H' → ErdosProblems.MulticolourTriangleRamsey.paletteColourCount H ≤ ErdosProblems.MulticolourTriangleRamsey.paletteColourCount H'`
- `ErdosProblems.MulticolourTriangleRamsey.two_mul_stage_le_paletteColourCount`: `∀ (H : ℕ), 2 * H ≤ ErdosProblems.MulticolourTriangleRamsey.paletteColourCount H`
- `ErdosProblems.MulticolourTriangleRamsey.paletteColourCount`: `ℕ → ℕ`
- `ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth_le_stage`: `∀ (H : ℕ), 2 ≤ H → ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth H ≤ H`
- `ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows_adjacent_scaled_sharp`: `∀ (H : ℕ), 3 ≤ H → H * ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows (H + 1) ≤ (H + 14) * ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows H`
- `ErdosProblems.MulticolourTriangleRamsey.stageWidths_succ_le`: `∀ (H : ℕ), 1 ≤ H → ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth (H + 1) ≤ ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth H + 1 ∧ ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixWidth (H + 1) ≤ ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixWidth H + 2 * ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth H + 4`
