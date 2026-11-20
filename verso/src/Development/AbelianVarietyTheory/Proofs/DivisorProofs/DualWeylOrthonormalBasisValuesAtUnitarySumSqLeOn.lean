import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DualWeyl.EvBound

/- English proof (translation)
Take `⟨k, hk⟩` from `GlobalTheory.DualWeyl.Repro.exists_repr la`. Establish `h1` using `GlobalTheory.DualWeyl.Repro.normSq_repr hla hk`. Set `e : Idx la → nabla la ℂ` to `fun i => (toSpace la).symm (onBasis la i)`. Establish `he : ∀ i, toSpace la (e i) = onBasis la i` using `fun i => (toSpace la).apply_symm_apply _`. Set `u : UN n` to `⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩`.

Rewrite using `[← h1, ← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← he, inner_toSpace, GlobalTheory.DualWeyl.Repro.form_rhoU_repr hk]`. Both sides reduce to the same expression.
-/
theorem sum_sq_norm_evalAt_onBasis_eq_one (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (g : UN n) :
    ∑ i, ‖evalAt g.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := GlobalTheory.DualWeyl.Repro.exists_repr la
  have h1 := GlobalTheory.DualWeyl.Repro.normSq_repr hla hk
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  let u : UN n := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
  rw [← h1, ← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← he, inner_toSpace, GlobalTheory.DualWeyl.Repro.form_rhoU_repr hk]
  rfl

/- English proof (translation)
Introduce `n la hla u` and use `(sum_sq_norm_evalAt_onBasis_eq_one n la hla u).le`.
-/
theorem sum_sq_norm_evalAt_onBasis_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n,
    ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 :=
  fun n la hla u => (sum_sq_norm_evalAt_onBasis_eq_one n la hla u).le

end GlobalTheory.DualWeyl.EvBound
