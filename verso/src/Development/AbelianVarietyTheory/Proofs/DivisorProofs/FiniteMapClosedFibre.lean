import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Use `haveI : IsAffine V.toScheme := hV`. Use `haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hU`. Use `haveI hg : IsFinite (f ∣_ V) := by`. Rewrite using `[HasAffineProperty.iff_of_isAffine (P := @IsFinite)]`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations.

Establish `h1 : (f.app (V.ι ''ᵁ ⊤)).hom.Finite`. Rewrite using `[Scheme.Opens.ι_image_top]`. Conclude with `hfin`. Establish `h2 : ∀ {A B : CommRingCat.{0}} (e : A ⟶ B) [IsIso e], e.hom.Finite` using `fun e _ => RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).2`. Rewrite using `[morphismRestrict_appTop]`.

Conclude with `(h2 _).comp h1`. Establish `hmemU : ∀ y : Y, f.base y = x → y ∈ f ⁻¹ᵁ V` using `fun y hy => by show f.base y ∈ V`. Rewrite using `[hy]`. Conclude with `hxV`. Establish `hres : ∀ (y : Y) (hy : f.base y = x), (f ∣_ V) (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) = (⟨x, hxV⟩ : V.toScheme)`.

Introduce `y hy`. Conclude with `Subtype.ext ((morphismRestrict_base_coe f V _).trans hy)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(((f ∣_ V).finite_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).image (f ⁻¹ᵁ V).ι.base).subset ?_` and prove the remaining obligations. Introduce `y hy`.

Conclude with `⟨⟨y, hmemU y hy⟩, hres y hy, rfl⟩`. Introduce `y hy`. Rewrite using `[← closure_subset_iff_isClosed]`. Introduce `z hz`. Rewrite `hz` using `[← specializes_iff_mem_closure]`.

Establish `hfz : f.base z = x`. Establish `h1 : f.base y ⤳ f.base z` using `hz.map f.base.hom.continuous`. Rewrite `h1` using `[hy, specializes_iff_mem_closure, hx.closure_eq]`. Conclude with `h1`. Establish `hspec : (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) ⤳ ⟨z, hmemU z hfz⟩` using `(f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.1 hz`.

Establish `hdisc` using `((f ∣_ V).isDiscrete_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).to_subtype`. Establish `hs2 : (⟨_, hres y hy⟩ : ((f ∣_ V) ⁻¹' {(⟨x, hxV⟩ : V.toScheme)} : Set _)) ⤳ ⟨_, hres z hfz⟩` using `Topology.IsInducing.subtypeVal.specializes_iff.1 hspec`. Use `congrArg (fun p => (p.1 : (f ⁻¹ᵁ V).toScheme).1) hs2.eq` as an intermediate fact. Conclude with `(Set.mem_singleton_iff.2 this.symm)`.
-/
theorem fibre_finite_isClosed_of_affine_finite {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V))
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    (f.base ⁻¹' {x}).Finite ∧ ∀ y : Y, f.base y = x → IsClosed ({y} : Set Y) := by
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hU
  haveI hg : IsFinite (f ∣_ V) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h1 : (f.app (V.ι ''ᵁ ⊤)).hom.Finite := by
      rw [Scheme.Opens.ι_image_top]; exact hfin
    have h2 : ∀ {A B : CommRingCat.{0}} (e : A ⟶ B) [IsIso e], e.hom.Finite := fun e _ =>
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).2
    rw [morphismRestrict_appTop]
    exact (h2 _).comp h1
  have hmemU : ∀ y : Y, f.base y = x → y ∈ f ⁻¹ᵁ V := fun y hy => by
    show f.base y ∈ V
    rw [hy]; exact hxV
  have hres : ∀ (y : Y) (hy : f.base y = x),
      (f ∣_ V) (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) = (⟨x, hxV⟩ : V.toScheme) := by
    intro y hy
    exact Subtype.ext ((morphismRestrict_base_coe f V _).trans hy)
  refine ⟨?_, ?_⟩
  · refine (((f ∣_ V).finite_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).image
      (f ⁻¹ᵁ V).ι.base).subset ?_
    intro y hy
    exact ⟨⟨y, hmemU y hy⟩, hres y hy, rfl⟩
  · intro y hy
    rw [← closure_subset_iff_isClosed]
    intro z hz
    rw [← specializes_iff_mem_closure] at hz
    have hfz : f.base z = x := by
      have h1 : f.base y ⤳ f.base z := hz.map f.base.hom.continuous
      rw [hy, specializes_iff_mem_closure, hx.closure_eq] at h1
      exact h1
    have hspec : (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) ⤳ ⟨z, hmemU z hfz⟩ :=
      (f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.1 hz
    have hdisc := ((f ∣_ V).isDiscrete_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).to_subtype
    have hs2 : (⟨_, hres y hy⟩ : ((f ∣_ V) ⁻¹' {(⟨x, hxV⟩ : V.toScheme)} : Set _)) ⤳
        ⟨_, hres z hfz⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
    have := congrArg (fun p => (p.1 : (f ⁻¹ᵁ V).toScheme).1) hs2.eq
    exact (Set.mem_singleton_iff.2 this.symm)

end GlobalTheory
