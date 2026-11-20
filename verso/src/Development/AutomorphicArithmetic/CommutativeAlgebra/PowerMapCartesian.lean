import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
open UpperTheory.Gal.Int.Geo
open CategoryTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.power_map_cartesian :
    PowCart := by
  intro X Y Z A B C f g φ χ u v k
  refine ⟨fun H => GlobalTheory.KS.PowPB.powMap_isPullback _ _ _ _ f φ u H k,
    GlobalTheory.KS.PowPB.powMap_w f φ u k, fun w => ?_⟩
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_w]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_pr]
