import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLift

universe u

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

namespace StandardSmoothLift

section

variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)

/- English proof (translation)
Establish `hu : Nat.card Unit = 1`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_unit]`. Establish `h1 : Nat.card (Unit ⊕ ι) = Nat.card ι + 1`. Rewrite using `[Nat.card_sum, hu]`. Use linear arithmetic over natural numbers and integers.

Establish `h2 : Nat.card (Unit ⊕ σ) = Nat.card σ + 1`. Rewrite using `[Nat.card_sum, hu]`. Use linear arithmetic over natural numbers and integers. Use `show Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = Nat.card ι - Nat.card σ`. Rewrite using `[h1, h2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem liftedSubmersivePresentation_dimension :
    (liftedSubmersivePresentation hsurj P).dimension = P.dimension := by
  have hu : Nat.card Unit = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_unit]
  have h1 : Nat.card (Unit ⊕ ι) = Nat.card ι + 1 := by
    rw [Nat.card_sum, hu]
    omega
  have h2 : Nat.card (Unit ⊕ σ) = Nat.card σ + 1 := by
    rw [Nat.card_sum, hu]
    omega
  show Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = Nat.card ι - Nat.card σ
  rw [h1, h2]
  omega

end

end StandardSmoothLift

section

variable (S R B : Type u) [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] [Algebra S B] [IsScalarTower S R B]

/- English proof (translation)
Establish `hinst : Algebra.IsStandardSmoothOfRelativeDimension r R B` using `‹_›`. Take `⟨ι, σ, hσ, hι, P, hdim⟩` from `hinst.out`. Establish `: Finite ι` using `hι`. Establish `: Finite σ` using `hσ`. Use `⟨StandardSmoothLift.LiftedAlgebra hsurj P, inferInstance, inferInstance, StandardSmoothLift.liftedAlgebraHom hsurj P, ?_, StandardSmoothLift.liftedAlgebraHom_surjective hsurj P, StandardSmoothLift.baseChangeEquiv hsurj P, StandardSmoothLift.baseChangeEquiv_one_tmul hsurj P⟩` and prove the remaining obligations.

Conclude with `⟨⟨Unit ⊕ ι, Unit ⊕ σ, inferInstance, inferInstance, StandardSmoothLift.liftedSubmersivePresentation hsurj P, (StandardSmoothLift.liftedSubmersivePresentation_dimension hsurj P).trans hdim⟩⟩`.
-/
theorem exists_lift_of_isStandardSmoothOfRelativeDimension (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r R B]
    (hsurj : Function.Surjective (algebraMap S R)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra S B') (f : B' →ₐ[S] B),
      Algebra.IsStandardSmoothOfRelativeDimension r S B' ∧ Function.Surjective f ∧
        ∃ e : (R ⊗[S] B') ≃ₐ[R] B, ∀ b' : B', e (1 ⊗ₜ[S] b') = f b' := by
  have hinst : Algebra.IsStandardSmoothOfRelativeDimension r R B := ‹_›
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ := hinst.out
  have : Finite ι := hι
  have : Finite σ := hσ
  refine ⟨StandardSmoothLift.LiftedAlgebra hsurj P, inferInstance, inferInstance,
    StandardSmoothLift.liftedAlgebraHom hsurj P, ?_,
    StandardSmoothLift.liftedAlgebraHom_surjective hsurj P,
    StandardSmoothLift.baseChangeEquiv hsurj P,
    StandardSmoothLift.baseChangeEquiv_one_tmul hsurj P⟩
  exact ⟨⟨Unit ⊕ ι, Unit ⊕ σ, inferInstance, inferInstance,
    StandardSmoothLift.liftedSubmersivePresentation hsurj P,
    (StandardSmoothLift.liftedSubmersivePresentation_dimension hsurj P).trans hdim⟩⟩

end

end FunctorialResolution.EmbeddedResolution
