import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.OverIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PsiOf

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.V.ML.iv :
    GlobalTheory.Published.PoitouTateDuality → ReciprocityTheory.Gal.UnramifiedOrthogonality → UpperTheory.V.Odd.PsiBound :=
  fun h₁ h₂ => UpperTheory.V.ML.psiOf (UpperTheory.V.ML.recip h₁ h₂)
