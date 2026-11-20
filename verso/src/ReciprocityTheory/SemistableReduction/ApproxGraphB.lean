import ReciprocityTheory.SemistableReduction.ApproxGraphA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [posPart, negPart, Pi.zero_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
lemma posPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (posPart p u) = posPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [posPart, negPart, Pi.zero_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
lemma posPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (negPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [posPart, negPart, Pi.zero_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
lemma negPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (posPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [posPart, negPart, Pi.zero_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
lemma negPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (negPart p u) = negPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use extensionality with `k`. Simplify using `[posPart]`.
-/
lemma posPart_zero (p : ℕ) {r : ℕ} : posPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [posPart]

/- English proof (translation)
Use extensionality with `k`. Simplify using `[negPart]`.
-/
lemma negPart_zero (p : ℕ) {r : ℕ} : negPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [negPart]

/- English proof (translation)
Introduce `j hj` and use `by simp [posPart, not_lt.mpr hj]`.
-/
lemma posPart_supp (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ∀ j : Fin r, p ≤ (j : ℕ) → posPart p u j = 0 := fun j hj => by
  simp [posPart, not_lt.mpr hj]

/- English proof (translation)
Unfold `approxR`. Conclude with `div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hμ.le) hρ.le`.
-/
lemma approxR_nonneg (r : ℕ) {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) : 0 ≤ approxR r μ ρ := by
  unfold approxR
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hμ.le) hρ.le

/- English proof (translation)
Use `set R := approxR r μ ρ with hRdef`. Establish `hR0 : 0 ≤ R` using `approxR_nonneg r hμ hρ`. Use `set E : Fin r → ℂ := ∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) with hE`. Establish `hEn : ‖euc E‖ ≤ √(r : ℝ) * μ * ‖euc w‖` using `norm_err_le X hX hμ.le w hw`. Establish `hsum : ∑ j, w j • X j = (R : ℂ) • w + E`.

Use extensionality with `k`. Simplify using `[hE, Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpw : posPart p w = w`. Use extensionality with `k`.

Simplify using `only [posPart]`. Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `(hw k (not_lt.mp h)).symm`. Establish `hnw : negPart p w = 0`.

Use extensionality with `k`. Simplify using `only [negPart, Pi.zero_apply]`. Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `hw k (not_lt.mp h)`.

Establish `hpos : posPart p (∑ j, w j • X j) = (R : ℂ) • w + posPart p E`. Rewrite using `[hsum, posPart_add, posPart_smul, hpw]`. Establish `hneg : negPart p (∑ j, w j • X j) = negPart p E`. Rewrite using `[hsum, negPart_add, negPart_smul, hnw, smul_zero, zero_add]`. Use `set s := √(r : ℝ) * μ * ‖euc w‖ with hs`.

Establish `hs0 : 0 ≤ s` using `mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hμ.le) (norm_nonneg _)`. Establish `hnegle : ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s`. Rewrite using `[hneg]`. Conclude with `(norm_negPart_le p E).trans hEn`. Establish `hRw : ‖euc ((R : ℂ) • w)‖ = 4 * s / ρ`.

Rewrite using `[euc_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hR0, hRdef, approxR, hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hposge : 4 * s / ρ - s ≤ ‖euc (posPart p (∑ j, w j • X j))‖`. Rewrite using `[hpos, euc_add]`. Establish `h1` using `norm_sub_le (euc ((R : ℂ) • w) + euc (posPart p E)) (euc (posPart p E))`.

Rewrite `h1` using `[add_sub_cancel_right]`. Establish `h2` using `(norm_posPart_le p E).trans hEn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : 4 * s ≤ 4 * s / ρ`. Rewrite using `[le_div_iff₀ hρ]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hqρ : 4 * s / ρ * ρ = 4 * s` using `div_mul_cancel₀ _ hρ.ne'`. Use `⟨?_, by linarith⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma graph_bound {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (negPart p (∑ j, w j • X j))‖ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ ∧
      3 * (√(r : ℝ) * μ * ‖euc w‖) ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
  set R := approxR r μ ρ with hRdef
  have hR0 : 0 ≤ R := approxR_nonneg r hμ hρ
  set E : Fin r → ℂ := ∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) with hE
  have hEn : ‖euc E‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := norm_err_le X hX hμ.le w hw

  have hsum : ∑ j, w j • X j = (R : ℂ) • w + E := by
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hpw : posPart p w = w := by
    ext k
    simp only [posPart]
    split_ifs with h
    · rfl
    · exact (hw k (not_lt.mp h)).symm
  have hnw : negPart p w = 0 := by
    ext k
    simp only [negPart, Pi.zero_apply]
    split_ifs with h
    · rfl
    · exact hw k (not_lt.mp h)
  have hpos : posPart p (∑ j, w j • X j) = (R : ℂ) • w + posPart p E := by
    rw [hsum, posPart_add, posPart_smul, hpw]
  have hneg : negPart p (∑ j, w j • X j) = negPart p E := by
    rw [hsum, negPart_add, negPart_smul, hnw, smul_zero, zero_add]
  set s := √(r : ℝ) * μ * ‖euc w‖ with hs
  have hs0 : 0 ≤ s := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hμ.le) (norm_nonneg _)
  have hnegle : ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := by
    rw [hneg]; exact (norm_negPart_le p E).trans hEn
  have hRw : ‖euc ((R : ℂ) • w)‖ = 4 * s / ρ := by
    rw [euc_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hR0, hRdef, approxR, hs]
    ring
  have hposge : 4 * s / ρ - s ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
    rw [hpos, euc_add]
    have h1 := norm_sub_le (euc ((R : ℂ) • w) + euc (posPart p E)) (euc (posPart p E))
    rw [add_sub_cancel_right] at h1
    have h2 := (norm_posPart_le p E).trans hEn
    linarith
  have hq : 4 * s ≤ 4 * s / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith
  have hqρ : 4 * s / ρ * ρ = 4 * s := div_mul_cancel₀ _ hρ.ne'
  refine ⟨?_, by linarith⟩
  calc ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := hnegle
    _ ≤ ρ / 3 * (4 * s / ρ - s) := by nlinarith [mul_le_mul_of_nonneg_right hρ1 hs0]
    _ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ :=
      mul_le_mul_of_nonneg_left hposge (by positivity)

/- English proof (translation)
Take `⟨h1, h2⟩` from `graph_bound X hμ hρ hρ1 hX w hw`. Use `⟨?_, fun hw0 => ?_⟩` and prove the remaining obligations. Rewrite using `[negSq_eq, posSq_eq, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h1 2`. Rewrite using `[posSq_eq]`.

Establish `hwpos : 0 < ‖euc w‖`. Rewrite using `[norm_pos_iff]`. Introduce `h`. Conclude with `hw0 (euc_eq_zero h)`. Establish `hr : 0 < r`.

Break down `Nat.eq_zero_or_pos r with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `absurd (Subsingleton.elim w 0) hw0`. Conclude with `h`. Establish `hsq : 0 < √(r : ℝ)` using `Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)`.

Establish `h3 : 0 < 3 * (√(r : ℝ) * μ * ‖euc w‖)` using `mul_pos (by norm_num) (mul_pos (mul_pos hsq hμ) hwpos)`. Conclude with `pow_pos (lt_of_lt_of_le h3 h2) 2`.
-/
lemma approxGraph_one {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)) := by
  obtain ⟨h1, h2⟩ := graph_bound X hμ hρ hρ1 hX w hw
  refine ⟨?_, fun hw0 => ?_⟩
  · rw [negSq_eq, posSq_eq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · rw [posSq_eq]
    have hwpos : 0 < ‖euc w‖ := by
      rw [norm_pos_iff]; intro h; exact hw0 (euc_eq_zero h)
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; exact absurd (Subsingleton.elim w 0) hw0
      · exact h
    have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
    have h3 : 0 < 3 * (√(r : ℝ) * μ * ‖euc w‖) :=
      mul_pos (by norm_num) (mul_pos (mul_pos hsq hμ) hwpos)
    exact pow_pos (lt_of_lt_of_le h3 h2) 2

def graphMap (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun w := posPart p (∑ j, posPart p w j • X j) + negPart p w
  map_add' u v := by
    simp only [posPart_add, negPart_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c u := by
    have h : ∀ j, posPart p (c • u) j • X j = c • (posPart p u j • X j) := fun j => by
      rw [posPart_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [Finset.sum_congr rfl (fun j _ => h j)]
    simp only [← Finset.smul_sum, posPart_smul, negPart_smul, RingHom.id_apply, smul_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma graphMap_apply (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) :
    graphMap p X w = posPart p (∑ j, posPart p w j • X j) + negPart p w := rfl

/- English proof (translation)
Establish `hinj : Function.Injective (graphMap p X)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Rewrite `hu` using `[graphMap_apply]`. Establish `hn : negPart p u = 0`.

Use `congrArg (negPart p) hu` as an intermediate fact. Rewrite `this` using `[negPart_add, negPart_posPart, zero_add, negPart_negPart, negPart_zero]`. Then use the resulting hypothesis. Establish `hp : posPart p (∑ j, posPart p u j • X j) = 0`. Use `congrArg (posPart p) hu` as an intermediate fact. Rewrite `this` using `[posPart_add, posPart_posPart, posPart_negPart, add_zero, posPart_zero]`. Then use the resulting hypothesis.

Establish `h2` using `(graph_bound X hμ hρ hρ1 hX (posPart p u) (posPart_supp p u)).2`. Rewrite `h2` using `[hp, euc_zero, norm_zero]`. Establish `hu0 : posPart p u = 0`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality.

Conclude with `Subsingleton.elim _ _`. Establish `hsq : 0 < √(r : ℝ)` using `Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)`. Establish `hle : ‖euc (posPart p u)‖ ≤ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Use `mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (mul_pos hsq hμ) hc)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `euc_eq_zero (norm_le_zero_iff.mp hle)`. Rewrite using `[← posPart_add_negPart p u, hu0, hn, add_zero]`. Take `⟨u, hu⟩` from `(LinearMap.injective_iff_surjective.mp hinj) (posPart p b)`.

Use `⟨posPart p u, posPart_supp p u, ?_⟩` and prove the remaining obligations. Use `congrArg (posPart p) hu` as an intermediate fact. Rewrite `this` using `[graphMap_apply, posPart_add, posPart_posPart, posPart_negPart, add_zero, posPart_posPart]`. Then use the resulting hypothesis.
-/
lemma exists_graph_pos {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (b : Fin r → ℂ) : ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧
      posPart p (∑ j, w j • X j) = posPart p b := by

  have hinj : Function.Injective (graphMap p X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [graphMap_apply] at hu
    have hn : negPart p u = 0 := by
      have := congrArg (negPart p) hu
      rwa [negPart_add, negPart_posPart, zero_add, negPart_negPart, negPart_zero] at this
    have hp : posPart p (∑ j, posPart p u j • X j) = 0 := by
      have := congrArg (posPart p) hu
      rwa [posPart_add, posPart_posPart, posPart_negPart, add_zero, posPart_zero] at this
    have h2 := (graph_bound X hμ hρ hρ1 hX (posPart p u) (posPart_supp p u)).2
    rw [hp, euc_zero, norm_zero] at h2
    have hu0 : posPart p u = 0 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; exact Subsingleton.elim _ _
      · have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
        have hle : ‖euc (posPart p u)‖ ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (mul_pos hsq hμ) hc)
          linarith
        exact euc_eq_zero (norm_le_zero_iff.mp hle)
    rw [← posPart_add_negPart p u, hu0, hn, add_zero]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) (posPart p b)
  refine ⟨posPart p u, posPart_supp p u, ?_⟩
  have := congrArg (posPart p) hu
  rwa [graphMap_apply, posPart_add, posPart_posPart, posPart_negPart, add_zero,
    posPart_posPart] at this

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
