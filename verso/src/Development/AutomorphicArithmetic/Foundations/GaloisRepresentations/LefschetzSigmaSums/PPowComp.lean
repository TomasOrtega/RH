import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
open UpperTheory.Gal.LocalSmoothExtension
open CategoryTheory

/- English proof (translation)
Introduce `S₁ S₂ S₃ A₁ A₂ A₃ f g e φ χ ω h₁ h₂ h₃ hfg hφχ k`. Substitute `hfg` using the available equality. Substitute `hφχ` using the available equality. Apply `GlobalTheory.KS.PowPB.pow_left_hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, GlobalTheory.KS.PowPB.powMap_w, Category.assoc]`.

Introduce `i`. Rewrite using `[Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, GlobalTheory.KS.PowPB.powMap_pr, Category.assoc]`.
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
