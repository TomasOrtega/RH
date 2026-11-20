import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreads
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.hypersurface_part_preirreducible_spreads` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHypersurfacePartGeometricIrreducibleSpreads.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  first | exact @GlobalTheory.hypersurface_part_preirreducible_spreads | exact GlobalTheory.hypersurface_part_preirreducible_spreads | (intros; apply GlobalTheory.hypersurface_part_preirreducible_spreads <;> assumption)
