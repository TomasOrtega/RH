import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingRepresentationInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEnvelopingRepresentationInjective.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.enveloping_representation_injective : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V), Function.Injective (envRepAll R) := by
  first | exact @GlobalTheory.CentralOps.envRepAll_injective | exact GlobalTheory.CentralOps.envRepAll_injective | (intros; apply GlobalTheory.CentralOps.envRepAll_injective <;> assumption)
