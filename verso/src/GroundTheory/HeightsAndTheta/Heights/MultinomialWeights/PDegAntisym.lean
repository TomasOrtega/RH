import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem blockPermute_lamDotX_permWeight (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N))
    (u : Idx d → ℚ) :
    RestTerms.blockPermute d.f d.N w (lamDotX d (permWeight d w u)) = lamDotX d u := by
  simp only [lamDotX, map_sum, map_mul, RestTerms.blockPermute, rename_C, rename_X, permWeight]
  exact Fintype.sum_equiv (Equiv.prodShear (Equiv.refl _) w) _ _ (fun p => rfl)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem blockPermute_lineClass_permWeight (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N))
    (u : Idx d → ℚ) :
    RestTerms.blockPermute d.f d.N w (lineClass d (permWeight d w u)) = lineClass d u := by
  simp only [lineClass, map_neg, blockPermute_lamDotX_permWeight]

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intFl_blockPermute (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N)) (H : XPoly d) :
    intFl d (RestTerms.blockPermute d.f d.N w H) = RestTerms.blockSign d.f d.N w * intFl d H := by
  simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul, RestTerms.FlagIntegralPermute.full d.f d.N w H]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem DegAntisym.proof : DegAntisym.Statement := by
  intro d w u
  have h : degAt d u = RestTerms.blockSign d.f d.N w * degAt d (permWeight d w u) := by
    simp only [degAt]
    rw [← intFl_blockPermute, map_pow (RestTerms.blockPermute d.f d.N w),
      blockPermute_lineClass_permWeight]
  rw [h, ← mul_assoc, RestTerms.Flag.blockSign_mul_self, one_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegAntisym.full : DegAntisym.Statement := DegAntisym.proof

end GroundTheory.Heights₂.Heights.TheoremB
