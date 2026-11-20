import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueStable

/- English proof (translation)
Introduce `D U M g hg Λ hΛ`. Take `⟨hgI, hgU⟩` from `hg`. Take `⟨hlat, huni, hcap⟩` from `hΛ`. Establish `H` using `Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT g hgI Λ`. Use `⟨H.2.2.2.2.mpr hlat, H.2.2.2.1.mpr huni, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hcap]`. Use extensionality with `x`. Simplify using `only [Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Establish `e : g.symm x = x` using `by conv_lhs => rw [← hgU x h2]`. Simplify using the standard rewrite rules. Conclude with `⟨e ▸ h1, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `e : g.symm x = x` using `by conv_lhs => rw [← hgU x h2]`.

Simplify using the standard rewrite rules. Conclude with `⟨e.symm ▸ h1, h2⟩`.
-/
theorem glueSet_gmap_mem : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M := by
  intro D U M g hg Λ hΛ
  obtain ⟨hgI, hgU⟩ := hg
  obtain ⟨hlat, huni, hcap⟩ := hΛ
  have H := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT g hgI Λ
  refine ⟨H.2.2.2.2.mpr hlat, H.2.2.2.1.mpr huni, ?_⟩
  rw [← hcap]
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e ▸ h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e.symm ▸ h1, h2⟩

end GlobalTheory.GlueStable
