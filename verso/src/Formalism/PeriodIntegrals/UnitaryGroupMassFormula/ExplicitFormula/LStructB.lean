import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

section prim
variable {N : ℕ}

/- English proof (translation)
Take `⟨hd, χ₀, hχ⟩` from `h`. Conclude with `⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩`.
-/
lemma factorsThrough_inv {χ : DirichletCharacter ℂ N} {d : ℕ} (h : χ.FactorsThrough d) :
    (χ⁻¹).FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

/- English proof (translation)
Unfold `DirichletCharacter.conductor`. Use `congr 1`. Use extensionality with `d`. Simplify using `only [DirichletCharacter.conductorSet, Set.mem_setOf_eq]`. Conclude with `⟨fun h => by simpa using factorsThrough_inv h, factorsThrough_inv⟩`.
-/
lemma conductor_inv (χ : DirichletCharacter ℂ N) : (χ⁻¹).conductor = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  simp only [DirichletCharacter.conductorSet, Set.mem_setOf_eq]
  exact ⟨fun h => by simpa using factorsThrough_inv h, factorsThrough_inv⟩

/- English proof (translation)
Establish `h' : χ.conductor = N` using `h`. Use `show (χ⁻¹).conductor = N`. Rewrite using `[conductor_inv, h']`.
-/
lemma isPrimitive_inv {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  have h' : χ.conductor = N := h
  show (χ⁻¹).conductor = N
  rw [conductor_inv, h']

/- English proof (translation)
Establish `h' : χ.conductor = N` using `h`. Rewrite `h'` using `[h1, DirichletCharacter.conductor_one]`. Conclude with `h'.symm`.
-/
lemma level_eq_one_of_primitive_one [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive)
    (h1 : χ = 1) : N = 1 := by
  have h' : χ.conductor = N := h
  rw [h1, DirichletCharacter.conductor_one] at h'
  exact h'.symm

end prim

variable {N : ℕ} [NeZero N]

/- English proof (translation)
Introduce `h0`. Establish `hs0 : s ≠ 0`. Introduce `h`. Rewrite `hs` using `[h]`. Evaluate the numerical expressions using `at hs`.

Establish `h2` using `DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)`. Rewrite `h2` using `[h0, zero_div]`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 hs h2`.
-/
lemma completed_ne_zero_right (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 ≤ s.re)
    (h1 : χ ≠ 1 ∨ s ≠ 1) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  rw [h0, zero_div] at h2
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 hs h2

/- English proof (translation)
Introduce `h0`. Establish `hp` using `(isPrimitive_inv hχ).completedLFunction_one_sub s`. Rewrite `hp` using `[inv_inv, h0, mul_zero]`. Use `completed_ne_zero_right χ⁻¹ (s := 1 - s) (by simp; linarith) ?_ hp` and prove the remaining obligations. Break down `h1 with h | h` into its components or cases.

Use `left`. Conclude with `fun h' => h (inv_eq_one.mp h')`. Use `right`. Introduce `h'`. Apply `h` to reduce the goal to its premises.

Take the linear combination `-h'`.
-/
lemma completed_ne_zero_left {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) (h1 : χ ≠ 1 ∨ s ≠ 0) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hp := (isPrimitive_inv hχ).completedLFunction_one_sub s
  rw [inv_inv, h0, mul_zero] at hp
  refine completed_ne_zero_right χ⁻¹ (s := 1 - s) (by simp; linarith) ?_ hp
  rcases h1 with h | h
  · left
    exact fun h' => h (inv_eq_one.mp h')
  · right
    intro h'
    apply h
    linear_combination -h'

/- English proof (translation)
Introduce `N _ χ hχ s hs hs1 hL`. Distinguish the cases in `hre1 : 1 ≤ s.re`. Conclude with `absurd hL (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hre1)`. Distinguish the cases in `hre0 : 0 < s.re`. Use `left`.

Conclude with `⟨hre0, by linarith⟩`. Use `push_neg at hre1 hre0`. Use `right`. Distinguish the cases in `hc : s = 0 ∧ χ = 1`. It suffices to derive a contradiction.

Take `⟨rfl, rfl⟩` from `hc`. Establish `hN` using `level_eq_one_of_primitive_one hχ rfl`. Substitute `hN` using the available equality. Rewrite `hL` using `[DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero]`. Evaluate the numerical expressions using `at hL`.

Establish `hc' : χ ≠ 1 ∨ s ≠ 0` using `by tauto`. Establish `hne` using `completed_ne_zero_left hχ hre0 hc'`. Establish `hsN : s ≠ 0 ∨ N ≠ 1`. Break down `hc' with h | h` into its components or cases. Use `right`.

Introduce `hN`. Substitute `hN` using the available equality. Conclude with `h (DirichletCharacter.level_one χ)`. Use `left`. Conclude with `h`.

Establish `hdiv` using `DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hsN`. Rewrite `hdiv` using `[hL, eq_comm, div_eq_zero_iff]`. Break down `hdiv with h | hg` into its components or cases. Conclude with `absurd h hne`. Break down `DirichletCharacter.even_or_odd χ with he | ho` into its components or cases.

Rewrite `hg` using `[he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]`. Take `⟨n, hn⟩` from `hg`. Establish `hre` using `congrArg Complex.re hn`. Simplify using `at hre`. Establish `hn1 : (n : ℝ) < 1` using `by linarith`.

Establish `hn0 : n = 0` using `by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)`. Substitute `hn0` using the available equality. Simplify using `at hn`. Use `Or.inl ⟨hn, he, ?_⟩` and prove the remaining obligations. Introduce `h1`.

Conclude with `hc ⟨hn, h1⟩`. Rewrite `hg` using `[ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]`. Take `⟨n, hn⟩` from `hg`. Establish `hre` using `congrArg Complex.re hn`. Simplify using `at hre`.

Establish `hn1 : (n : ℝ) < 1` using `by linarith`. Establish `hn0 : n = 0` using `by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)`. Substitute `hn0` using the available equality. Use `Or.inr ⟨?_, ho⟩` and prove the remaining obligations. Simplify using `at hn`.

Take the linear combination `hn`.
-/
theorem zeroLocus : ZeroLocus := by
  intro N _ χ hχ s hs hs1 hL
  by_cases hre1 : 1 ≤ s.re
  · exact absurd hL (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hre1)
  by_cases hre0 : 0 < s.re
  · left
    exact ⟨hre0, by linarith⟩
  push_neg at hre1 hre0
  right
  by_cases hc : s = 0 ∧ χ = 1
  · exfalso
    obtain ⟨rfl, rfl⟩ := hc
    have hN := level_eq_one_of_primitive_one hχ rfl
    subst hN
    rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero] at hL
    norm_num at hL
  have hc' : χ ≠ 1 ∨ s ≠ 0 := by tauto
  have hne := completed_ne_zero_left hχ hre0 hc'
  have hsN : s ≠ 0 ∨ N ≠ 1 := by
    rcases hc' with h | h
    · right
      intro hN
      subst hN
      exact h (DirichletCharacter.level_one χ)
    · left
      exact h
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hsN
  rw [hL, eq_comm, div_eq_zero_iff] at hdiv
  rcases hdiv with h | hg
  · exact absurd h hne
  rcases DirichletCharacter.even_or_odd χ with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    simp at hn
    refine Or.inl ⟨hn, he, ?_⟩
    intro h1
    exact hc ⟨hn, h1⟩
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    refine Or.inr ⟨?_, ho⟩
    simp at hn
    linear_combination hn

/- English proof (translation)
Use `⟨fun s => (Real.pi : ℂ) ^ (s / 2) * (1 / 2 * (Complex.Gamma (s / 2 + 1))⁻¹), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Differentiable.mul ?_ ?_` and prove the remaining obligations. Conclude with `(differentiable_id.div_const (2 : ℂ)).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))`. Conclude with `(differentiable_const _).mul (Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const (2 : ℂ)).add_const 1))`. Simplify using `[Complex.Gamma_one]`.

Introduce `z`. Rewrite using `[Complex.Gammaℝ_def, neg_div, Complex.cpow_neg, mul_inv, inv_inv]`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Simplify using `[Complex.Gamma_zero]`.

Establish `key : (Complex.Gamma (z / 2))⁻¹ = z * (1 / 2 * (Complex.Gamma (z / 2 + 1))⁻¹)`. Rewrite using `[Complex.Gamma_add_one _ (div_ne_zero hz two_ne_zero), mul_inv]`. Establish `h2 : z * (1 / 2) * (z / 2)⁻¹ = 1` using `by field_simp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_differentiable_Gammaℝ_inv_eq_mul : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
    ∀ z : ℂ, (Gammaℝ z)⁻¹ = z * g z := by
  refine ⟨fun s => (Real.pi : ℂ) ^ (s / 2) * (1 / 2 * (Complex.Gamma (s / 2 + 1))⁻¹), ?_, ?_, ?_⟩
  · refine Differentiable.mul ?_ ?_
    · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (differentiable_const _).mul
        (Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const (2 : ℂ)).add_const 1))
  · simp [Complex.Gamma_one]
  · intro z
    rw [Complex.Gammaℝ_def, neg_div, Complex.cpow_neg, mul_inv, inv_inv]
    by_cases hz : z = 0
    · subst hz
      simp [Complex.Gamma_zero]
    · have key : (Complex.Gamma (z / 2))⁻¹ = z * (1 / 2 * (Complex.Gamma (z / 2 + 1))⁻¹) := by
        rw [Complex.Gamma_add_one _ (div_ne_zero hz two_ne_zero), mul_inv]
        have h2 : z * (1 / 2) * (z / 2)⁻¹ = 1 := by field_simp
        calc (Complex.Gamma (z / 2))⁻¹
            = (z * (1 / 2) * (z / 2)⁻¹) * (Complex.Gamma (z / 2))⁻¹ := by rw [h2, one_mul]
          _ = _ := by ring
      rw [key]
      ring

/- English proof (translation)
Take `⟨g, hgd, hg0, hgz⟩` from `exists_differentiable_Gammaℝ_inv_eq_mul`. Use `show analyticOrderAt _ _ = ((1 : ℕ) : ℕ∞)`. Rewrite using `[(Complex.differentiable_Gammaℝ_inv.analyticAt 0).analyticOrderAt_eq_natCast]`. Use `⟨g, hgd.analyticAt 0, hg0, ?_⟩` and prove the remaining obligations. Use `filter_upwards with z`.

Rewrite using `[hgz z]`. Simplify using the standard rewrite rules.
-/
lemma order_Gammaℝ_inv_zero : analyticOrderAt (fun s : ℂ => (Gammaℝ s)⁻¹) 0 = 1 := by
  obtain ⟨g, hgd, hg0, hgz⟩ := exists_differentiable_Gammaℝ_inv_eq_mul
  show analyticOrderAt _ _ = ((1 : ℕ) : ℕ∞)
  rw [(Complex.differentiable_Gammaℝ_inv.analyticAt 0).analyticOrderAt_eq_natCast]
  refine ⟨g, hgd.analyticAt 0, hg0, ?_⟩
  filter_upwards with z
  rw [hgz z]
  simp

/- English proof (translation)
Take `⟨g, hgd, hg0, hgz⟩` from `exists_differentiable_Gammaℝ_inv_eq_mul`. Establish `hN1 : N ≠ 1`. Introduce `hN`. Substitute `hN` using the available equality. Conclude with `h1 (DirichletCharacter.level_one χ)`.

Establish `hLeq : ∀ s, LFunction χ s = completedLFunction χ s * (s * g s)`. Introduce `s`. Rewrite using `[DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1), he.gammaFactor_def, div_eq_mul_inv, hgz]`. Establish `hc0 : completedLFunction χ 0 ≠ 0` using `completed_ne_zero_left hχ (by simp) (Or.inl h1)`. Establish `hcd : Differentiable ℂ (completedLFunction χ)` using `DirichletCharacter.differentiable_completedLFunction h1`.

Use `⟨by rw [hLeq]; simp, ?_⟩` and prove the remaining obligations. Establish `hLa : AnalyticAt ℂ (LFunction χ) 0` using `(DirichletCharacter.differentiable_LFunction h1).analyticAt 0`. Establish `hord : analyticOrderAt (LFunction χ) 0 = ((1 : ℕ) : ℕ∞)`. Rewrite using `[hLa.analyticOrderAt_eq_natCast]`. Use `⟨fun s => completedLFunction χ s * g s, (hcd.mul hgd).analyticAt 0, mul_ne_zero hc0 hg0, ?_⟩` and prove the remaining obligations.

Use `filter_upwards with z`. Rewrite using `[hLeq]`. Simplify using `only [sub_zero, pow_one, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[analyticOrderNatAt, hord]`.
-/
theorem mult_zero_of_even {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (he : χ.Even)
    (h1 : χ ≠ 1) : LFunction χ 0 = 0 ∧ analyticOrderNatAt (LFunction χ) 0 = 1 := by
  obtain ⟨g, hgd, hg0, hgz⟩ := exists_differentiable_Gammaℝ_inv_eq_mul
  have hN1 : N ≠ 1 := by
    intro hN
    subst hN
    exact h1 (DirichletCharacter.level_one χ)
  have hLeq : ∀ s, LFunction χ s = completedLFunction χ s * (s * g s) := by
    intro s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1),
      he.gammaFactor_def, div_eq_mul_inv, hgz]
  have hc0 : completedLFunction χ 0 ≠ 0 := completed_ne_zero_left hχ (by simp) (Or.inl h1)
  have hcd : Differentiable ℂ (completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction h1
  refine ⟨by rw [hLeq]; simp, ?_⟩
  have hLa : AnalyticAt ℂ (LFunction χ) 0 := (DirichletCharacter.differentiable_LFunction h1).analyticAt 0
  have hord : analyticOrderAt (LFunction χ) 0 = ((1 : ℕ) : ℕ∞) := by
    rw [hLa.analyticOrderAt_eq_natCast]
    refine ⟨fun s => completedLFunction χ s * g s, (hcd.mul hgd).analyticAt 0, mul_ne_zero hc0 hg0, ?_⟩
    filter_upwards with z
    rw [hLeq]
    simp only [sub_zero, pow_one, smul_eq_mul]
    ring
  simp [analyticOrderNatAt, hord]

end PI.EF
