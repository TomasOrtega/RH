import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FWedgeLatticeGenerator.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.wedge_lattice_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p → L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} ∧ exteriorPower.ιMulti Ω r b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti | exact GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti <;> assumption)
