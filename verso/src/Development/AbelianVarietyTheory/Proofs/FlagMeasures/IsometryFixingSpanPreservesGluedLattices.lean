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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Supply the required witnesses or components.
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
