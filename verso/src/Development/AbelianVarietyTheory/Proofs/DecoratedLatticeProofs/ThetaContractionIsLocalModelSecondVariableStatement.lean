import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsLocalModelSecondVariable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FThetaContractionIsLocalModelSecondVariable.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.thetaContraction_isLocalModel_secondVariable : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B' s FA' F₀' → ∀ (T₂ : SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] (WO S B'.V₀ → ℂ)), p.IsModel ψ FS F₀' T₂ → ∀ (φ₀ : SB (n → k)) (Ξ₁ : WO B.V₀ S → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → ∀ (u : WO B.A S) (T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ)), (∀ Ξ₂ v, T Ξ₂ v = GlobalTheory.Unf.contr l S vL Ξ₁ (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Ξ₂)) u v) → p.IsModel ψ FS FA' T := by
  first | exact @GlobalTheory.ContrModR.contr_isModel | exact GlobalTheory.ContrModR.contr_isModel | (intros; apply GlobalTheory.ContrModR.contr_isModel <;> assumption)
