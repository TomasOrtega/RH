import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Introduce `S _ _ Y f _ _ _ _ _ ⟨y, hy⟩`. Set `F` to `finitePart f`. Establish `hyF : y ∈ F` using `mem_finitePart_of_eq_closedPoint f y hy`. Establish `hfin : IsFinite (F.ι ≫ f)` using `isFinite_finitePart f`. Establish `: IsAffine F.toScheme` using `isAffine_of_isAffineHom (F.ι ≫ f)`.

Set `g : Spec Γ(F.toScheme, ⊤) ⟶ Spec (.of S)` to `F.toScheme.isoSpec.inv ≫ F.ι ≫ f`. Take `⟨φ, hφ⟩` from `Spec.map_surjective g`. Use `letI : Algebra S Γ(F.toScheme, ⊤) := φ.hom.toAlgebra`. Establish `hφ' : CommRingCat.ofHom (algebraMap S Γ(F.toScheme, ⊤)) = φ` using `rfl`. Establish `hgfin : IsFinite g` using `by dsimp [g]; infer_instance`.

Establish `hgfl : Flat g` using `by dsimp [g]; infer_instance`. Use `⟨Γ(F.toScheme, ⊤), inferInstance, inferInstance, ?_, ?_, ?_, F.toScheme.isoSpec.inv ≫ F.ι, ?_⟩` and prove the remaining obligations. Rewrite `hgfin` using `[← hφ, IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.1 hgfin`. Rewrite `hgfl` using `[← hφ, Flat.SpecMap_iff]`.

Conclude with `RingHom.flat_algebraMap_iff.1 hgfl`. Establish `: Nonempty F.toScheme` using `⟨⟨y, hyF⟩⟩`. Set `x : Spec Γ(F.toScheme, ⊤)` to `F.toScheme.isoSpec.hom ⟨y, hyF⟩`. Establish `hp : x.asIdeal.IsPrime` using `x.isPrime`. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Conclude with `hp.ne_top (Subsingleton.elim _ _)`. Rewrite using `[hφ', hφ]`. Simplify using `[g]`.
-/
theorem exists_finite_flat_spec_of_quasiFinite_of_henselian :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of S))
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f],
      (∃ y : Y, f y = IsLocalRing.closedPoint S) → ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A),
        Module.Finite S A ∧ Module.Flat S A ∧ Nontrivial A ∧
          ∃ h : Spec (.of A) ⟶ Y, h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S A)) := by
  intro S _ _ Y f _ _ _ _ _ ⟨y, hy⟩
  let F := finitePart f
  have hyF : y ∈ F := mem_finitePart_of_eq_closedPoint f y hy
  have hfin : IsFinite (F.ι ≫ f) := isFinite_finitePart f
  have : IsAffine F.toScheme := isAffine_of_isAffineHom (F.ι ≫ f)
  let g : Spec Γ(F.toScheme, ⊤) ⟶ Spec (.of S) := F.toScheme.isoSpec.inv ≫ F.ι ≫ f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  letI : Algebra S Γ(F.toScheme, ⊤) := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap S Γ(F.toScheme, ⊤)) = φ := rfl
  have hgfin : IsFinite g := by dsimp [g]; infer_instance
  have hgfl : Flat g := by dsimp [g]; infer_instance
  refine ⟨Γ(F.toScheme, ⊤), inferInstance, inferInstance, ?_, ?_, ?_, F.toScheme.isoSpec.inv ≫ F.ι, ?_⟩
  · rw [← hφ, IsFinite.SpecMap_iff] at hgfin
    exact RingHom.finite_algebraMap.1 hgfin
  · rw [← hφ, Flat.SpecMap_iff] at hgfl
    exact RingHom.flat_algebraMap_iff.1 hgfl
  · have : Nonempty F.toScheme := ⟨⟨y, hyF⟩⟩
    let x : Spec Γ(F.toScheme, ⊤) := F.toScheme.isoSpec.hom ⟨y, hyF⟩
    have hp : x.asIdeal.IsPrime := x.isPrime
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hp.ne_top (Subsingleton.elim _ _)
  · rw [hφ', hφ]
    simp [g]

end GlobalTheory
