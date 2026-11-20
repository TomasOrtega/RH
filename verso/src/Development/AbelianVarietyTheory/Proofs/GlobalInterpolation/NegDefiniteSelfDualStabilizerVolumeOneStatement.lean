import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegDefiniteSelfDualStabilizerVolumeOne
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.NegDefStab.measure_SFin_negDef | exact GlobalTheory.NegDefStab.measure_SFin_negDef | (intros; apply GlobalTheory.NegDefStab.measure_SFin_negDef <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.negDefinite_selfDualStabilizer_volume_one : ∀ (D : D7) (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) → ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W 0 n μ → μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) = 1 := by
  first | exact @GlobalTheory.NegDefStab.measure_SFin_negDef | exact GlobalTheory.NegDefStab.measure_SFin_negDef | (intros; apply GlobalTheory.NegDefStab.measure_SFin_negDef <;> assumption)
