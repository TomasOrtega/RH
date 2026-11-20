import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusEndomorphismStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frob_isFrob_unique : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K),
    IsFrob (frob A) ∧ ∀ π : End A, IsFrob π → π = frob A := by
  intro K _ _ A
  have hex : ∃ π : End A, IsFrob π := by
    obtain ⟨π, hπ, -⟩ := GlobalTheory.T.exists_frobenius_endomorphism K A
    exact ⟨π, hπ⟩
  have hf : IsFrob (frob A) := by
    unfold frob
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hf, fun π hπ => ?_⟩
  apply GlobalTheory.AV.AbVar.ext_of_pt_eq
  intro x
  rw [hπ x, hf x]

end GlobalTheory.AV.AbVar
