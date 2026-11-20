import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Formalism.LandauZeroFreeBounds.Statement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZeroFreeHalf

/- English proof (translation)
Unfold `Formalism.ZeroFreeDirichlet.InRegion`. Use `set M := max (N : ℝ) (N * |ρ.im|) with hM`. Establish `hN3 : (3 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hMN : (N : ℝ) ≤ M` using `le_max_left _ _`. Establish `hMt : (N : ℝ) * |ρ.im| ≤ M` using `le_max_right _ _`.

Establish `hMpos : 0 < M` using `by linarith`. Establish `ht` using `abs_nonneg ρ.im`. Establish `hA : (N : ℝ) * (|ρ.im| + 2) ≤ M ^ 2` using `by nlinarith`. Establish `hA1 : 1 < (N : ℝ) * (|ρ.im| + 2)` using `by nlinarith`. Establish `hL : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2))` using `Real.log_pos hA1`.

Establish `hle : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log M`. Establish `e` using `Real.log_le_log (by linarith) hA`. Rewrite `e` using `[Real.log_pow]`. Move the coercions through the operations in `at e`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hdiv : c / (2 * Real.log M) ≤ c / Real.log ((N : ℝ) * (|ρ.im| + 2))` using `div_le_div_of_nonneg_left hc.le hL hle`. Rewrite `h` using `[div_div]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inRegion_of_max {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 3 ≤ N) {ρ : ℂ}
    (h : 1 - c / 2 / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re) : Formalism.ZeroFreeDirichlet.InRegion c N ρ := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  set M := max (N : ℝ) (N * |ρ.im|) with hM
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : (N : ℝ) ≤ M := le_max_left _ _
  have hMt : (N : ℝ) * |ρ.im| ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  have ht := abs_nonneg ρ.im
  have hA : (N : ℝ) * (|ρ.im| + 2) ≤ M ^ 2 := by nlinarith
  have hA1 : 1 < (N : ℝ) * (|ρ.im| + 2) := by nlinarith
  have hL : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA1
  have hle : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log M := by
    have e := Real.log_le_log (by linarith) hA
    rw [Real.log_pow] at e
    push_cast at e
    linarith
  have hdiv : c / (2 * Real.log M) ≤ c / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
    div_le_div_of_nonneg_left hc.le hL hle
  rw [div_div] at h
  linarith

/- English proof (translation)
Introduce `a`. Distinguish the cases in `ha : IsUnit a`. Establish `h2 : χ a * χ a = 1`. Rewrite using `[← pow_two, ← MulChar.pow_apply' χ two_ne_zero, h, MulChar.one_apply ha]`. Apply the tactic sequence `rcases mul_self_eq_one_iff.mp h2 with e | e <;> simp [e]`.

Simplify using `[MulChar.map_nonunit χ ha]`.
-/
theorem isRealChar_of_sq {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ ^ 2 = 1) : IsRealChar χ := by
  intro a
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, h, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.mp h2 with e | e <;> simp [e]
  · simp [MulChar.map_nonunit χ ha]

/- English proof (translation)
Introduce `h1`. Rewrite `hp` using `[DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : 3 ≤ N) : χ ≠ 1 := by
  intro h1
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hp
  omega

/- English proof (translation)
Introduce `hZ`. Take `⟨c, hc, hZ⟩` from `hZ`. Use `⟨c / 2, by positivity, ?_, ?_⟩` and prove the remaining obligations. Introduce `N _ χ hp hN ρ hρ hreg`. Establish `hχ1 : χ ≠ 1` using `ne_one_of_isPrimitive χ hp hN`.

Take `⟨hsq, -, him, hder, huniq⟩` from `hZ N χ ρ (inRegion_of_max hc hN hreg) ⟨Or.inl hχ1, hρ⟩`. Use `⟨isRealChar_of_sq χ hsq, him, ?_, ?_⟩` and prove the remaining obligations. Establish `han : AnalyticAt ℂ (LFunction χ) ρ` using `(DirichletCharacter.differentiable_LFunction hχ1).analyticAt ρ`. Simplify using `[analyticOrderNatAt, han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hder]`. Introduce `ρ' hρ' hreg'`.

Conclude with `(huniq χ ρ' (inRegion_of_max hc hN hreg') ⟨Or.inl hχ1, hρ'⟩).2`. Introduce `ρ hρ _ hre1`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `ht` using `abs_nonneg ρ.im`.

Establish `hR : Formalism.ZeroFreeDirichlet.InRegion c 1 ρ`. Unfold `Formalism.ZeroFreeDirichlet.InRegion`. Establish `ha : 0 < Real.log (|ρ.im| + 2)` using `Real.log_pos (by linarith)`. Establish `hab : Real.log (|ρ.im| + 2) ≤ 2 * Real.log (|ρ.im| + 3)`. Establish `e` using `Real.log_le_log (by linarith) (by linarith : |ρ.im| + 2 ≤ |ρ.im| + 3)`.

Establish `e2 : 0 ≤ Real.log (|ρ.im| + 3)` using `Real.log_nonneg (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdiv` using `div_le_div_of_nonneg_left hc.le ha hab`. Rewrite `hlt` using `[div_div]`. Simplify using `only [Nat.cast_one, one_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : ρ ≠ 1`. Introduce and unpack `rfl`. Simplify using `at hre1`. Establish `hZ0 : Formalism.ZeroFreeDirichlet.IsLZero (1 : DirichletCharacter ℂ 1) ρ` using `⟨Or.inr hne, by rw [DirichletCharacter.LFunction_modOne_eq]; exact hρ⟩`.

Conclude with `(hZ 1 1 ρ hR hZ0).2.1 rfl`.
-/
theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∃ c : ℝ, 0 < c ∧ (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧ (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  intro hZ
  obtain ⟨c, hc, hZ⟩ := hZ
  refine ⟨c / 2, by positivity, ?_, ?_⟩
  · intro N _ χ hp hN ρ hρ hreg
    have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hp hN
    obtain ⟨hsq, -, him, hder, huniq⟩ :=
      hZ N χ ρ (inRegion_of_max hc hN hreg) ⟨Or.inl hχ1, hρ⟩
    refine ⟨isRealChar_of_sq χ hsq, him, ?_, ?_⟩
    · have han : AnalyticAt ℂ (LFunction χ) ρ :=
        (DirichletCharacter.differentiable_LFunction hχ1).analyticAt ρ
      simp [analyticOrderNatAt, han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hder]
    · intro ρ' hρ' hreg'
      exact (huniq χ ρ' (inRegion_of_max hc hN hreg') ⟨Or.inl hχ1, hρ'⟩).2
  · intro ρ hρ _ hre1
    by_contra hlt
    rw [not_le] at hlt
    have ht := abs_nonneg ρ.im
    have hR : Formalism.ZeroFreeDirichlet.InRegion c 1 ρ := by
      unfold Formalism.ZeroFreeDirichlet.InRegion
      have ha : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith)
      have hab : Real.log (|ρ.im| + 2) ≤ 2 * Real.log (|ρ.im| + 3) := by
        have e := Real.log_le_log (by linarith) (by linarith : |ρ.im| + 2 ≤ |ρ.im| + 3)
        have e2 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith)
        linarith
      have hdiv := div_le_div_of_nonneg_left hc.le ha hab
      rw [div_div] at hlt
      simp only [Nat.cast_one, one_mul]
      linarith
    have hne : ρ ≠ 1 := by
      rintro rfl
      simp at hre1
    have hZ0 : Formalism.ZeroFreeDirichlet.IsLZero (1 : DirichletCharacter ℂ 1) ρ :=
      ⟨Or.inr hne, by rw [DirichletCharacter.LFunction_modOne_eq]; exact hρ⟩
    exact (hZ 1 1 ρ hR hZ0).2.1 rfl

end GlobalTheory.ZeroFreeHalf
