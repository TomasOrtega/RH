import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.UnderCPl

/- English proof (translation)
Introduce `hP K _ _ _ hK n hn m wt hm M hM l _ hl Ω _ _ _ _ _ _ ι r hr hirr`. Establish `hC` using `UpperTheory.V.Lev.LevelF.of_level hr.level`. Establish `hF` using `UpperTheory.V.Lev.levelFRes ℚ K Ω l n M m r hC`. Take `⟨P, hreg, hA⟩` from `hr.aut hC.cont K hK hirr`. Take `⟨θ, hθ, hd⟩` from `hr.dual`.

Take `⟨χ, μ, hpol, -, -⟩` from `UpperTheory.V.Z.Bc.polK hP K hK n (by omega) l Ω ι r wt θ P hθ hd hA`. Conclude with `⟨hirr, ⟨P, hreg, ⟨χ, hpol⟩, hA⟩, hF.cont, hF.away, hF.above, hr.safe⟩`.
-/
theorem UpperTheory.V.Br.isCrys_isDR_restrict_openSubgroup :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.AdmRes := by
  intro hP K _ _ _ hK n hn m wt hm M hM l _ hl Ω _ _ _ _ _ _ ι r hr hirr
  have hC := UpperTheory.V.Lev.LevelF.of_level hr.level
  have hF := UpperTheory.V.Lev.levelFRes ℚ K Ω l n M m r hC
  obtain ⟨P, hreg, hA⟩ := hr.aut hC.cont K hK hirr
  obtain ⟨θ, hθ, hd⟩ := hr.dual
  obtain ⟨χ, μ, hpol, -, -⟩ := UpperTheory.V.Z.Bc.polK hP K hK n (by omega) l Ω ι r wt θ P hθ hd hA
  exact ⟨hirr, ⟨P, hreg, ⟨χ, hpol⟩, hA⟩, hF.cont, hF.away, hF.above, hr.safe⟩
