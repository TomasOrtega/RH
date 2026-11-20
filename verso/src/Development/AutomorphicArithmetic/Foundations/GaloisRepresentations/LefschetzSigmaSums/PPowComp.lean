import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
open UpperTheory.Gal.LocalSmoothExtension
open CategoryTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Substitute using the available equality. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.powComp_of :
    PowComp := by
  intro S₁ S₂ S₃ A₁ A₂ A₃ f g e φ χ ω h₁ h₂ h₃ hfg hφχ k
  subst hfg
  subst hφχ
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      GlobalTheory.KS.PowPB.powMap_w, Category.assoc]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      GlobalTheory.KS.PowPB.powMap_pr, Category.assoc]
