import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLatticeEigenVectorBundle.lean&line=238#L238)
-/
theorem _root_.GlobalTheory.T.lattice_eigen_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (L : Lat ξ E) (T : Set (Cpt ξ)) (g : ℕ) (I : Type) [Fintype I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), IsCptGen ξ → Function.Injective σ → Fintype.card I = Module.finrank ℚ F → [CharZero Ω] → L.IsVBOn T g ⊤ → (∀ p ∈ T, ∀ a, ∀ e ∈ L p, ρ a e ∈ L p) → (∀ p ∈ T, ∀ s a, σ s a ∈ regAt ξ p) → (∀ p ∈ T, unitAt ξ p ((NumberField.discr F : ℤ) : Ω)) → (∀ s, (L.inter (eigSp ρ (σ s))).IsVBOn T (Module.finrank Ω (eigSp ρ (σ s))) (eigSp ρ (σ s))) ∧ ∀ p ∈ T, L p = ⨆ s, (L.inter (eigSp ρ (σ s))) p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigSplit.isVBOn_eigSp | exact GlobalTheory.CompanionTheory.Ar.EigSplit.isVBOn_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.EigSplit.isVBOn_eigSp <;> assumption)
