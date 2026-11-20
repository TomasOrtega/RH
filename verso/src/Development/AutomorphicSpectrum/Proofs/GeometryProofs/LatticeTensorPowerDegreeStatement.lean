import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLatticeTensorPowerDegree.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.lattice_tensor_power_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn | exact GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn <;> assumption)
