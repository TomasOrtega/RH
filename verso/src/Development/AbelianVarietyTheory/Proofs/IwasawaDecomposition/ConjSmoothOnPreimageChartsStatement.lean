import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageCharts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.smoothOn_comp_ddcForm_of_isConjMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FConjSmoothOnPreimageCharts.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.conj_smoothOn_preimage_charts : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (σ σ' : k →+* ℂ) (j : CxPts p σ' → CxPts p σ), IsConjMap j → ∀ (W : Set (CxPts p σ)) (φ : CxPts p σ → ℝ), IsOpen W → (AnRead.all p σ d).SmoothOn W φ → IsOpen (j ⁻¹' W) ∧ (AnRead.all p σ' d).SmoothOn (j ⁻¹' W) (φ ∘ j) ∧ ∀ (c' : AlgChart p σ' d), ∀ z ∈ c'.e.source, ∃ c : AlgChart p σ d, j z ∈ c.e.source ∧ ∀ (ψ : CxPts p σ → ℝ) (ξ : Fin d → ℂ), ddcForm (ψ ∘ j) c' z ξ = ddcForm ψ c (j z) (star ξ) := by
  first | exact @GlobalTheory.ShFam.smoothOn_comp_ddcForm_of_isConjMap | exact GlobalTheory.ShFam.smoothOn_comp_ddcForm_of_isConjMap | (intros; apply GlobalTheory.ShFam.smoothOn_comp_ddcForm_of_isConjMap <;> assumption)
