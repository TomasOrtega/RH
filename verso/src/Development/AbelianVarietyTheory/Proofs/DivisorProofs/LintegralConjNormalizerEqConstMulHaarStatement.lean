import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjNormalizerEqConstMulHaar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralConjNormalizerEqConstMulHaar.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.lintegral_conj_normalizer_eq_const_mul_haar : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure N) (b : G), IsClosed (N : Set G) → ν.IsHaarMeasure → (∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) → ∃ κ : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν := by
  first | exact @GlobalTheory.SphEis.lintegral_conj_eq_const_mul | exact GlobalTheory.SphEis.lintegral_conj_eq_const_mul | (intros; apply GlobalTheory.SphEis.lintegral_conj_eq_const_mul <;> assumption)
