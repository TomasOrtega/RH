import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpiRingHomFieldClosure
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FEpiRingHomFieldClosure.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.epi_ring_hom_field_closure : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top | exact GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top | (intros; apply GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top <;> assumption)
