import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSmoothCuspFormMemUnitaryRapidDecayForms.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F, IsCuspForm θ V F → F ∈ Decay θ V := by
  first | exact @GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | exact GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | (intros; apply GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay <;> assumption)
