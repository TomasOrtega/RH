import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDerivedActionIntertwinesOfGroup.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.derived_action_intertwines_of_group : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w (f f' : GlobalTheory.RealWeil.Sch l), ⇑f' = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(A' f') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' f)) →
    ∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f) := by
  first | exact @GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine | exact GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine | (intros; apply GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine <;> assumption)
