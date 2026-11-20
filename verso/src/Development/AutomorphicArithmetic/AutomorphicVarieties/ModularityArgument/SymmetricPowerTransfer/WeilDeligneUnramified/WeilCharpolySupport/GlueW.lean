import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties

/- English proof (translation)
Introduce `L Ω _ _ _ _ _ _ l _ ι R h π _ hπ`. Take `⟨t, ht⟩` from `UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOfP_of UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl L 3 (by norm_num) π`. Use `⟨t, fun w => ?_⟩` and prove the remaining obligations. Take `⟨π', hπ', hc⟩` from `h w`. Establish `e : π' = π`.

Use `GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC L 3 π' π ?_)` and prove the remaining obligations. Use `filter_upwards [hπ'.2, hπ.2] with v h1 h2`. Take `⟨B, hB, hE⟩` from `h1`. Take `⟨B', hB', hE'⟩` from `h2`. Establish `e : B = B'` using `(UpperTheory.hecke_eigenvalue_basic_properties L Ω l ι v).2.2 3 R B B' hE hE'`.

Conclude with `⟨B, (GlobalTheory.CuspRep.CG.hasSat_mk π' v B).1 hB, (GlobalTheory.CuspRep.CG.hasSat_mk π v B).1 (e ▸ hB')⟩`. Substitute `e` using the available equality. Break down `hc with ⟨B, hB⟩ | hp` into its components or cases. Conclude with `(ht w).2 B hB`. Conclude with `(ht w).1 hp`.
-/
theorem UpperTheory.V.Z.Sym.W.glueW :
    UpperTheory.V.Z.Sym.W.GlueW := by
  intro L Ω _ _ _ _ _ _ l _ ι R h π _ hπ
  obtain ⟨t, ht⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOfP_of UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl
    L 3 (by norm_num) π
  refine ⟨t, fun w => ?_⟩
  obtain ⟨π', hπ', hc⟩ := h w
  have e : π' = π := by
    refine GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC L 3 π' π ?_)
    filter_upwards [hπ'.2, hπ.2] with v h1 h2
    obtain ⟨B, hB, hE⟩ := h1
    obtain ⟨B', hB', hE'⟩ := h2
    have e : B = B' := (UpperTheory.hecke_eigenvalue_basic_properties L Ω l ι v).2.2 3 R B B' hE hE'
    exact ⟨B, (GlobalTheory.CuspRep.CG.hasSat_mk π' v B).1 hB, (GlobalTheory.CuspRep.CG.hasSat_mk π v B).1 (e ▸ hB')⟩
  subst e
  rcases hc with ⟨B, hB⟩ | hp
  · exact (ht w).2 B hB
  · exact (ht w).1 hp
