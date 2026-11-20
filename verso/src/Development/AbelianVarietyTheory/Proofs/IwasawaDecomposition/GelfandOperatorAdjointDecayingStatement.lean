import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorAdjointDecaying
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGelfandOperatorAdjointDecaying.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.gelfand_operator_adjoint_decaying : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ (Z : Submodule ℂ (GA D V → ℂ)), (∀ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ k, ∀ F ∈ Decay θ V ⊓ Z, ∃ F' ∈ Decay θ V ⊓ Z, ∀ φ, IsMod θ V φ → ∫ g in 𝓕, gelf θ V τ k φ g * F g ∂μ = ∫ g in 𝓕, φ g * F' g ∂μ := by
  first | exact @GlobalTheory.Mem.GelfParts.gelf_by_parts | exact GlobalTheory.Mem.GelfParts.gelf_by_parts | (intros; apply GlobalTheory.Mem.GelfParts.gelf_by_parts <;> assumption)
