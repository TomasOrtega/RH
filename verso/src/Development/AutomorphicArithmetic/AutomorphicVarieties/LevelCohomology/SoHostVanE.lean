import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoVanEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

/- English proof (translation)
Introduce `CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF`. Apply `So.vanEOf c.O _ _ _ F` to reduce the goal to its premises. Introduce `j hj s`. Break down `hj.lt_or_eq with hlt | heq` into its components or cases. Conclude with `So.lineNeg CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω l c N e ψ S A F hD.e_pos hF j hlt s`.

Substitute `heq` using the available equality. Conclude with `So.lineZero c.O _ _ _ F (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hD S A F hF) s`.
-/
theorem UpperTheory.V.X.So.hostVanE : ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → UnitaryThreeInertia.HostVanE := by
  intro CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF
  apply So.vanEOf c.O _ _ _ F
  intro j hj s
  rcases hj.lt_or_eq with hlt | heq
  · exact So.lineNeg CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω l c N e ψ S A F hD.e_pos hF j hlt s
  · subst heq
    exact So.lineZero c.O _ _ _ F (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hD S A F hF) s
