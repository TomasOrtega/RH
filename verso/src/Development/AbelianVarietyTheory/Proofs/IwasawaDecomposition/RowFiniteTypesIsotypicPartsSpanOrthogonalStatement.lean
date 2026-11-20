import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRowFiniteTypesIsotypicPartsSpanOrthogonal.lean&line=208#L208)
-/
theorem _root_.GlobalTheory.T.rowFiniteTypes_isotypicParts_span_orthogonal : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (P : principalLevelFrame.RowPsi V D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Inputs D → V.SigOK → IsInfFam θ → StdFrame hF P → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → (∃ (s : Finset (GA D V)) (c : GA D V → ℂ), (∀ g ∈ s, g ∈ GfC V) ∧ e = ∑ g ∈ s, c g • principalLevelFrame.rtA g) → (⨆ π, principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π) = goodPart θ M (levS V β L) (levChi V β L) e ∧ ∀ π π', ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π, ∀ y ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π', ipM M μ 𝓕 x y = 0 := by
  first | exact @GlobalTheory.FinTypesRows.isotL_span_orth | exact GlobalTheory.FinTypesRows.isotL_span_orth | (intros; apply GlobalTheory.FinTypesRows.isotL_span_orth <;> assumption)
