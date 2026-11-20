import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

/- English proof (translation)
Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq]`. Set `p : Spec (Z.presheaf.stalk ζ)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk ζ))`. Establish `hp : Z.fromSpecStalk ζ p ∈ Set.range (Z.fromSpecStalk ζ)` using `⟨p, rfl⟩`. Rewrite `hp` using `[Scheme.range_fromSpecStalk]`. Establish `h1 : Z.fromSpecStalk ζ p = Z.fromSpecStalk ζ (IsLocalRing.closedPoint _)` using `(h _ hp).trans Scheme.fromSpecStalk_closedPoint.symm`.

Establish `h2` using `(Z.fromSpecStalk ζ).isEmbedding.injective h1`. Conclude with `(congrArg PrimeSpectrum.asIdeal h2).symm`.
-/
theorem isField_stalk_of_forall_specializes {Z : Scheme.{0}} (ζ : Z) [IsDomain (Z.presheaf.stalk ζ)]
    (h : ∀ z : Z, z ⤳ ζ → z = ζ) : IsField (Z.presheaf.stalk ζ) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  let p : Spec (Z.presheaf.stalk ζ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk ζ))
  have hp : Z.fromSpecStalk ζ p ∈ Set.range (Z.fromSpecStalk ζ) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  have h1 : Z.fromSpecStalk ζ p = Z.fromSpecStalk ζ (IsLocalRing.closedPoint _) :=
    (h _ hp).trans Scheme.fromSpecStalk_closedPoint.symm
  have h2 := (Z.fromSpecStalk ζ).isEmbedding.injective h1
  exact (congrArg PrimeSpectrum.asIdeal h2).symm

/- English proof (translation)
Introduce `Y Z π _ _ hW`. Use `haveI := GlobalTheory.IsNormalScheme.isDomain_stalk (X := Z) (genPt π)`. Use `isField_stalk_of_forall_specializes _ fun z hz => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩ : z ∈ Set.range π` from `hz.mem_open hW ⟨_, rfl⟩`. Conclude with `(hz.antisymm ((genericPoint_specializes y).map π.continuous)).eq`.
-/
theorem isField_stalk_genPt :
    ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ _ hW
  haveI := GlobalTheory.IsNormalScheme.isDomain_stalk (X := Z) (genPt π)
  refine isField_stalk_of_forall_specializes _ fun z hz => ?_
  obtain ⟨y, rfl⟩ : z ∈ Set.range π := hz.mem_open hW ⟨_, rfl⟩
  exact (hz.antisymm ((genericPoint_specializes y).map π.continuous)).eq

end GlobalTheory.NormSheafDescent
