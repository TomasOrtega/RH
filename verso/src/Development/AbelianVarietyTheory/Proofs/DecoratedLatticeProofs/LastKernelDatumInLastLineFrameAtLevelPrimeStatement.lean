import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelDatumInLastLineFrameAtLevelPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SeeSaw.lastKernel_reps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLastKernelDatumInLastLineFrameAtLevelPrime.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.lastKernelDatum_in_lastLineFrame_at_levelPrime : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsLattice k) (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧ Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L (fun i => haveI := hΛ i; phiOne (u i • o.Q (j + 1) i) (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  first | exact @GlobalTheory.SeeSaw.lastKernel_reps | exact GlobalTheory.SeeSaw.lastKernel_reps | (intros; apply GlobalTheory.SeeSaw.lastKernel_reps <;> assumption)
