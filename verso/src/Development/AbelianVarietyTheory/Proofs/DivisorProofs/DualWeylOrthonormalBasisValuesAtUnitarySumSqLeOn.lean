import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DualWeyl.EvBound

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem sum_sq_norm_evalAt_onBasis_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n,
    ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 :=
  fun n la hla u => (sum_sq_norm_evalAt_onBasis_eq_one n la hla u).le

end GlobalTheory.DualWeyl.EvBound
