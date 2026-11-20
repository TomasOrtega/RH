import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.OverIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PsiOf

/- English proof (translation)
Introduce `h₁ h₂` and use `UpperTheory.V.ML.psiOf (UpperTheory.V.ML.recip h₁ h₂)`.
-/
theorem UpperTheory.V.ML.iv :
    GlobalTheory.Published.PoitouTateDuality → ReciprocityTheory.Gal.UnramifiedOrthogonality → UpperTheory.V.Odd.PsiBound :=
  fun h₁ h₂ => UpperTheory.V.ML.psiOf (UpperTheory.V.ML.recip h₁ h₂)
