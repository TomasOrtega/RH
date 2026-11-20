import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreadsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEtaleMvPolynomialHypersurfaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simpa [Set.image_univ_of_surjective hs] using hX.isPreirreducible_univ.image f hf.continuousOn⟩`.
-/
theorem preirreducibleSpace_of_continuous_surjective_fibreChart {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [hX : PreirreducibleSpace X] (f : X → Y) (hf : Continuous f)
    (hs : Function.Surjective f) : PreirreducibleSpace Y :=
  ⟨by simpa [Set.image_univ_of_surjective hs] using
    hX.isPreirreducible_univ.image f hf.continuousOn⟩

/- English proof (translation)
Set `E : k ⊗[A] B ≃ₐ[A] k ⊗[A] C` to `Algebra.TensorProduct.congr AlgEquiv.refl e`. Set `H` to `PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `preirreducibleSpace_of_continuous_surjective_fibreChart H H.continuous H.surjective`.

Introduce `h`. Conclude with `preirreducibleSpace_of_continuous_surjective_fibreChart H.symm H.symm.continuous H.symm.surjective`.
-/
theorem preirreducibleSpace_tensor_congr_fibreChart (A B C k : Type) [CommRing A] [CommRing B]
    [CommRing C] [CommRing k] [Algebra A B] [Algebra A C] [Algebra A k] (e : B ≃ₐ[A] C) :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) ↔ PreirreducibleSpace (PrimeSpectrum (k ⊗[A] C)) := by
  let E : k ⊗[A] B ≃ₐ[A] k ⊗[A] C := Algebra.TensorProduct.congr AlgEquiv.refl e
  let H := PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
  constructor
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H H.continuous H.surjective
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H.symm H.symm.continuous
      H.symm.surjective

/- English proof (translation)
Introduce `A B _ _ _ n _ _ hB Ω _ _ _ hΩ`. Take `⟨f, g, hf, hd, ⟨e⟩⟩` from `GlobalTheory.T.standardEtale_localization_away_quotient_span A B n hB`. Establish `hΩ'` using `(GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g Ω).1 ((preirreducibleSpace_tensor_congr_fibreChart A _ _ Ω e).1 hΩ)`. Take `⟨a, I, ha, hI, hk⟩` from `GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads A (Option (Fin n)) f g none hf hd Ω (algebraMap A Ω) hΩ'`. Use `⟨a, I, ha, hI, ?_⟩` and prove the remaining obligations.

Introduce `k _ _ _ hak hIk`. Conclude with `(preirreducibleSpace_tensor_congr_fibreChart A _ _ k e).2 ((GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g k).2 (hk k (algebraMap A k) hak hIk))`.
-/
theorem preirreducibleSpace_fibre_standardEtale_spreads :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by
  intro A B _ _ _ n _ _ hB Ω _ _ _ hΩ
  obtain ⟨f, g, hf, hd, ⟨e⟩⟩ := GlobalTheory.T.standardEtale_localization_away_quotient_span A B n hB
  have hΩ' := (GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g Ω).1 ((preirreducibleSpace_tensor_congr_fibreChart A _ _ Ω e).1 hΩ)
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads A (Option (Fin n)) f g none hf hd Ω (algebraMap A Ω) hΩ'
  refine ⟨a, I, ha, hI, ?_⟩
  intro k _ _ _ hak hIk
  exact (preirreducibleSpace_tensor_congr_fibreChart A _ _ k e).2
    ((GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g k).2 (hk k (algebraMap A k) hak hIk))

end GlobalTheory
