import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormulaStatement
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

/- English proof (translation)
Unfold `Formalism.DegreeFormula.weylProd GlobalTheory.FlagPoly.ev delPol`. Simplify using `only [map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Simplify using `[div_eq_inv_mul]`.

Simplify using the standard rewrite rules.
-/
theorem weylProd_eq_mul_ev_delPol {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) :
    Formalism.DegreeFormula.weylProd lam =
      (∏ _τ : ι, ∏ i : Fin N, ∏ k : Fin N, if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1) *
        GlobalTheory.FlagPoly.ev lam (delPol ι N) := by
  unfold Formalism.DegreeFormula.weylProd GlobalTheory.FlagPoly.ev delPol
  simp only [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ =>
    Finset.prod_congr rfl fun k _ => ?_
  split_ifs with h
  · simp [div_eq_inv_mul]
  · simp

/- English proof (translation)
Introduce `ι _ _ N`. Use `⟨(Nat.factorial (dimFl ι N) : ℝ) * (∏ _τ : ι, ∏ i : Fin N, ∏ k : Fin N, if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1), ?_, fun lam => ?_⟩` and prove the remaining obligations. Use `mul_pos (by exact_mod_cast Nat.factorial_pos _) ?_` and prove the remaining obligations. Use `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Establish `h' : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ)` using `by exact_mod_cast h`. Conclude with `inv_pos.mpr (sub_pos.mpr h')`. Conclude with `one_pos`. Rewrite using `[GlobalTheory.T.flag_degree_formula ι N lam, weylProd_eq_mul_ev_delPol, mul_assoc]`.
-/
theorem flagDeg_eq_pos_mul_delPol :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ), ∃ c : ℝ, 0 < c ∧
      ∀ lam : ι → Fin N → ℝ, flagDeg ι N lam = c * ev lam (delPol ι N) := by
  intro ι _ _ N
  refine ⟨(Nat.factorial (dimFl ι N) : ℝ) *
    (∏ _τ : ι, ∏ i : Fin N, ∏ k : Fin N, if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1), ?_, fun lam => ?_⟩
  · refine mul_pos (by exact_mod_cast Nat.factorial_pos _) ?_
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => ?_
    split_ifs with h
    · have h' : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast h
      exact inv_pos.mpr (sub_pos.mpr h')
    · exact one_pos
  · rw [GlobalTheory.T.flag_degree_formula ι N lam, weylProd_eq_mul_ev_delPol, mul_assoc]

end GlobalTheory.FlagPoly
