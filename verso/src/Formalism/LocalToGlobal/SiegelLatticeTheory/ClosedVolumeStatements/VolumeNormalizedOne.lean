import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.SupportG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolSemiDirect
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolumeUnipotentOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolStabSW
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SupportDatum
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocProdFormula
import Formalism.PeriodIntegrals.LocProdFormula
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound

namespace Formalism.L2.SG.Closed

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volume_normalized_all : Formalism.L2.SG.Volumes.VolumeUnipotentAllCM := volume_unipotent_all_cm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LevelSAll_holds : Formalism.L2.SG.Volumes.LevelSAll := level_s_all_split
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volume_normalized_one : Formalism.L2.SG.Volumes.VolumeUnipotentOneFrom := volumeUnipotentOne

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions.

Fix the arbitrary inputs and assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem VolumesFromSW_holds (hS0 : PI.VolFromSW.VolumeDegenerateFromSiegelWeil) : Formalism.L2.SG.Volumes.VolumesFromSW := by
  have hS := volume_stabilizer_from_siegel_weil
  unfold PI.VolFromSW.VolStabFromSW at hS
  unfold PI.VolFromSW.VolumeDegenerateFromSiegelWeil at hS0
  unfold Formalism.L2.SG.Volumes.VolumesFromSW
  unfold Formalism.MainNotions.UnusedSlot34.ForAllCM at *
  intros
  beta_reduce
  intro h1 h2
  constructor
  · apply hS <;> assumption
  · apply hS0 <;> assumption

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem NormProd_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.NormProd D := by
  intro δ M hA x hx
  exact local_product_formula D.host.F D.host.E (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.conjF D.s.atP M
    (fun p => (hA p).1) x hx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SupportLoc_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.SupportLoc D := Formalism.L2.SG.Pf.localSupport_holds D

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SupportLemma_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.SupportLemma D :=
  Formalism.L2.SG.SupportG.supportLemma_of_loc (SupportLoc_holds D) (NormProd_holds D)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SupportVec_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.SupportVec D := support_vector_all D

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiffExists_holds {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : Formalism.L2.SG.LocVol.DiffExists v :=
  diffExists v

end Formalism.L2.SG.Closed
