import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

/- English proof (translation)
Introduce `ι _ _ N d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `Φ`. Use `⟨C (Φ 1), isHomogeneous_C _ _, fun lam => ?_⟩` and prove the remaining obligations.

Simplify using `[ev]`. Consider the case `succ d ih`. Introduce `Φ`. Use `choose P hP hev using fun x : ι × Fin N => ih (Φ ∘ₗ LinearMap.mulLeft ℝ (-X x : Pol ι N))`. Use `⟨∑ x, X x * P x, ?_, fun lam => ?_⟩` and prove the remaining obligations.

Use `IsHomogeneous.sum _ _ _ fun x _ => ?_` and prove the remaining obligations. Use `(isHomogeneous_X ℝ x).mul (hP x)` as an intermediate fact. Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis. Establish `h1 : linRoot lam ^ (d + 1) = ∑ x : ι × Fin N, lam x.1 x.2 • (-X x * linRoot lam ^ d)`. Establish `h0 : linRoot lam = ∑ x : ι × Fin N, lam x.1 x.2 • (-X x : Pol ι N)`.

Simplify using `[linRoot, smul_eq_C_mul]`. Rewrite using `[pow_succ']`. Use `conv_lhs => enter [1]`. Rewrite using `[h0]`. Rewrite using `[Finset.sum_mul]`.

Simplify using `only [smul_mul_assoc]`. Rewrite using `[h1, map_sum]`. Unfold `ev`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Use `hev x lam` as an intermediate fact. Unfold `ev at this`. Rewrite using `[map_mul, this, map_smul, eval_X]`. Simplify using the standard rewrite rules.
-/
theorem exists_form_of_functional : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (d : ℕ) (Φ : Pol ι N →ₗ[ℝ] ℝ), ∃ P : Pol ι N, P.IsHomogeneous d ∧ ∀ lam : ι → Fin N → ℝ, ev lam P = Φ (linRoot lam ^ d) := by
  intro ι _ _ N d
  induction d with
  | zero =>
    intro Φ
    refine ⟨C (Φ 1), isHomogeneous_C _ _, fun lam => ?_⟩
    simp [ev]
  | succ d ih =>
    intro Φ
    choose P hP hev using fun x : ι × Fin N => ih (Φ ∘ₗ LinearMap.mulLeft ℝ (-X x : Pol ι N))
    refine ⟨∑ x, X x * P x, ?_, fun lam => ?_⟩
    · refine IsHomogeneous.sum _ _ _ fun x _ => ?_
      have := (isHomogeneous_X ℝ x).mul (hP x)
      rwa [add_comm] at this
    · have h1 : linRoot lam ^ (d + 1) = ∑ x : ι × Fin N, lam x.1 x.2 • (-X x * linRoot lam ^ d) := by
        have h0 : linRoot lam = ∑ x : ι × Fin N, lam x.1 x.2 • (-X x : Pol ι N) := by
          simp [linRoot, smul_eq_C_mul]
        rw [pow_succ']
        conv_lhs => enter [1]; rw [h0]
        rw [Finset.sum_mul]
        simp only [smul_mul_assoc]
      rw [h1, map_sum]
      unfold ev
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have := hev x lam
      unfold ev at this
      rw [map_mul, this, map_smul, eval_X]
      simp

end GlobalTheory.FlagPoly
