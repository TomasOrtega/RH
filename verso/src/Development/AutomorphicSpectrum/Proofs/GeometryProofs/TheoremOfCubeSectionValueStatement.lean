import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TheoremOfCubeSectionValue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTheoremOfCubeSectionValue.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.theorem_of_cube_section_value : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) {T : Over S} (x a : T ⟶ G) (m : ℕ), x ^ m = 1 → ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U), v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen <;> assumption)
