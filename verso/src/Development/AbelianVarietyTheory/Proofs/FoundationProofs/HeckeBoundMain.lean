import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformNormCoeffPrimeLeOfNotDvdLevel
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

/- English proof (translation)
Establish `hq1 : (1 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`. Use `set x : ℝ := (q : ℝ) ^ ((k : ℝ) / 2) with hx`. Use `set y : ℝ := (q : ℝ) ^ ((k : ℝ) / 2 - 1) with hy`. Establish `hk' : (3 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Establish `hx1 : 1 < x` using `Real.one_lt_rpow hq1 (by linarith)`. Establish `hy1 : 1 < y` using `Real.one_lt_rpow hq1 (by linarith)`. Establish `hxy : x * y = (q : ℝ) ^ (k - 1)`. Rewrite using `[hx, hy, ← Real.rpow_add hq0, ← Real.rpow_natCast]`. Use `congr 1`.

Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use polynomial arithmetic with `[mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1)]`.
-/
theorem hecke_bound_lt (k q : ℕ) (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) < 1 + (q : ℝ) ^ (k - 1) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set x : ℝ := (q : ℝ) ^ ((k : ℝ) / 2) with hx
  set y : ℝ := (q : ℝ) ^ ((k : ℝ) / 2 - 1) with hy
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : 1 < x := Real.one_lt_rpow hq1 (by linarith)
  have hy1 : 1 < y := Real.one_lt_rpow hq1 (by linarith)
  have hxy : x * y = (q : ℝ) ^ (k - 1) := by
    rw [hx, hy, ← Real.rpow_add hq0, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  nlinarith [mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1)]

/- English proof (translation)
Establish `hb` using `GlobalTheory.HeckeBd.norm_a_le k g q hq hqM`. Use `⟨hb, fun h => ?_⟩` and prove the remaining obligations. Establish `hlt` using `hecke_bound_lt k q hk hq.two_le`. Establish `hn : ‖(1 : ℂ) + (q : ℂ) ^ (k - 1)‖ = 1 + (q : ℝ) ^ (k - 1)`. Establish `: (1 : ℂ) + (q : ℂ) ^ (k - 1) = (((1 : ℝ) + (q : ℝ) ^ (k - 1) : ℝ) : ℂ)` using `by push_cast; ring`.

Rewrite using `[this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Rewrite `hb` using `[h, hn]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hecke_bound_ne (k : ℕ) (g : UpperTheory.V.Af.Newform k) (q : ℕ) (hk : 3 ≤ k) (hq : q.Prime)
    (hqM : ¬ q ∣ g.M) :
    ‖g.a q‖ ≤ (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) ∧
      g.a q ≠ 1 + (q : ℂ) ^ (k - 1) := by
  have hb := GlobalTheory.HeckeBd.norm_a_le k g q hq hqM
  refine ⟨hb, fun h => ?_⟩
  have hlt := hecke_bound_lt k q hk hq.two_le
  have hn : ‖(1 : ℂ) + (q : ℂ) ^ (k - 1)‖ = 1 + (q : ℝ) ^ (k - 1) := by
    have : (1 : ℂ) + (q : ℂ) ^ (k - 1) = (((1 : ℝ) + (q : ℝ) ^ (k - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h, hn] at hb
  linarith

/- English proof (translation)
Introduce `k g q hk hq hqM` and use `hecke_bound_ne k g q hk hq hqM`.
-/
theorem hecke_bound_main : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (q : ℕ), 3 ≤ k → q.Prime → ¬ q ∣ g.M →
    ‖g.a q‖ ≤ (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) ∧ g.a q ≠ 1 + (q : ℂ) ^ (k - 1) :=
  fun k g q hk hq hqM => hecke_bound_ne k g q hk hq hqM

end GlobalTheory.HeckeFamilyMatrices
