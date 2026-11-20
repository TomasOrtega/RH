import Mathlib
open IsLocalRing

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `_ hβ`. Use `letI : Algebra A K := α.toAlgebra`. Use `letI : Algebra K L := ι.toAlgebra`. Use `letI : Algebra A L := (ι.comp α).toAlgebra`. Use `haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Set `g : B →ₐ[A] L` to `{ β with commutes' := fun a => congrArg (fun f : A →+* L => f a) hβ }`. Set `f : K ⊗[A] B →ₐ[K] L` to `Algebra.TensorProduct.lift (Algebra.ofId K L) g (fun _ _ => Commute.all _ _)`. Use `haveI : Module.Finite K (K ⊗[A] B) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)`. Use `haveI : Algebra.IsIntegral K (K ⊗[A] B) := Algebra.IsIntegral.of_finite K _`. Use `haveI : Algebra.IsIntegral K f.range := Algebra.IsIntegral.of_surjective f.rangeRestrict (AlgHom.rangeRestrict_surjective f)`.

Establish `hsurj : Function.Surjective (algebraMap K f.range)`. Introduce `y`. Establish `hy : IsIntegral K (y : L)` using `(Algebra.IsIntegral.isIntegral y).map f.range.val`. Take `⟨k, hk⟩` from `minpoly.mem_range_of_degree_eq_one K (y : L) (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy))`. Conclude with `⟨k, Subtype.ext hk⟩`.

Set `e : K ≃+* f.range` to `RingEquiv.ofBijective (algebraMap K f.range) ⟨(algebraMap K f.range).injective, hsurj⟩`. Set `ψ : B →+* K` to `e.symm.toRingHom.comp (f.rangeRestrict.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B).toRingHom)`. Establish `hι : ∀ x, ι (ψ x) = β x`. Introduce `x`. Establish `h1 : (algebraMap K f.range (ψ x) : L) = ι (ψ x)` using `rfl`.

Establish `h2 : algebraMap K f.range (ψ x) = f.rangeRestrict (1 ⊗ₜ x)`. Simplify using `only [ψ, e, RingHom.comp_apply]`. Conclude with `(RingEquiv.ofBijective (algebraMap K f.range) _).apply_symm_apply _`. Rewrite using `[← h1, h2]`. Simplify using `[f, g]`.

Use `⟨ψ, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[RingHom.comp_apply, hι]`. Conclude with `congrArg (fun f : A →+* L => f a) hβ`.

Use extensionality with `x`. Conclude with `hι x`.
-/
theorem etale_hom_to_field_lands_in_algClosed_subfield
    (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L]
    (α : A →+* K) (ι : K →+* L) (β : B →+* L) :
    (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α →
      ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  intro _ hβ
  letI : Algebra A K := α.toAlgebra
  letI : Algebra K L := ι.toAlgebra
  letI : Algebra A L := (ι.comp α).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : B →ₐ[A] L :=
    { β with
      commutes' := fun a => congrArg (fun f : A →+* L => f a) hβ }
  let f : K ⊗[A] B →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) g (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K (K ⊗[A] B) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)
  haveI : Algebra.IsIntegral K (K ⊗[A] B) := Algebra.IsIntegral.of_finite K _
  haveI : Algebra.IsIntegral K f.range :=
    Algebra.IsIntegral.of_surjective f.rangeRestrict (AlgHom.rangeRestrict_surjective f)
  have hsurj : Function.Surjective (algebraMap K f.range) := by
    intro y
    have hy : IsIntegral K (y : L) := (Algebra.IsIntegral.isIntegral y).map f.range.val
    obtain ⟨k, hk⟩ := minpoly.mem_range_of_degree_eq_one K (y : L)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy))
    exact ⟨k, Subtype.ext hk⟩
  let e : K ≃+* f.range :=
    RingEquiv.ofBijective (algebraMap K f.range) ⟨(algebraMap K f.range).injective, hsurj⟩
  let ψ : B →+* K :=
    e.symm.toRingHom.comp (f.rangeRestrict.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B).toRingHom)
  have hι : ∀ x, ι (ψ x) = β x := by
    intro x
    have h1 : (algebraMap K f.range (ψ x) : L) = ι (ψ x) := rfl
    have h2 : algebraMap K f.range (ψ x) = f.rangeRestrict (1 ⊗ₜ x) := by
      simp only [ψ, e, RingHom.comp_apply]
      exact (RingEquiv.ofBijective (algebraMap K f.range) _).apply_symm_apply _
    rw [← h1, h2]
    simp [f, g]
  refine ⟨ψ, ?_, ?_⟩
  · ext a
    apply ι.injective
    rw [RingHom.comp_apply, hι]
    exact congrArg (fun f : A →+* L => f a) hβ
  · ext x
    exact hι x

end GlobalTheory
