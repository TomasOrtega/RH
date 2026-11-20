import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuotientHeightLowerBoundShortIsotropicVector.lean&line=269#L269)
-/
theorem _root_.GlobalTheory.T.quotientHeight_lower_bound_short_isotropic_vector : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → ∀ a ∈ GfC V, ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ z ∈ ZI V ξ, ∀ u ∈ GinfC V, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ τ i, ‖((archM V (θ τ) u)⁻¹.mulVec (fun j => tauE D τ (ξ j))) i‖ ≤ δ) → c ≤ δ * (GlobalTheory.CuspDecay.quotHeight θ V (z * a * u) : ℝ) ^ N := by
  first | exact @GlobalTheory.HolDict.quotHeight_lower_bound | exact GlobalTheory.HolDict.quotHeight_lower_bound | (intros; apply GlobalTheory.HolDict.quotHeight_lower_bound <;> assumption)
