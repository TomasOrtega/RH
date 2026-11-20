import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `X G S B β f g π w J Y P ψ e p q hψ hcov he hP hβ hf hr`. Set `ψ' : ∀ j, P j ⟶ pullback g π` to `fun j => pullback.lift (p j ≫ ψ j) (q j) (by rw [Category.assoc]; exact (hP j).w)`. Establish `hψ'f : ∀ j, ψ' j ≫ pullback.fst g π = p j ≫ ψ j` using `fun j => pullback.lift_fst _ _ _`. Establish `hψ's : ∀ j, ψ' j ≫ pullback.snd g π = q j` using `fun j => pullback.lift_snd _ _ _`. Establish `sq : ∀ j, IsPullback (ψ' j) (p j) (pullback.fst g π) (ψ j)` using `fun j => (IsPullback.of_bot (v₁₁ := ψ' j) (v₂₁ := pullback.snd g π) (by rw [hψ's]; exact hP j) (hψ'f j).symm (IsPullback.of_hasPullback g π)).flip`.

Use `haveI : ∀ j, IsOpenImmersion (ψ' j) := fun j => MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq j).flip (hψ j)`. Establish `hc : ∀ z : (pullback g π : Scheme), ∃ j y, ψ' j y = z`. Introduce `z`. Take `⟨j, y, hy⟩` from `hcov (pullback.fst g π z)`. Take `⟨t, ht, -⟩` from `Scheme.exists_preimage_of_isPullback (sq j) z y hy.symm`.

Conclude with `⟨j, t, ht⟩`. Set `c : X ⟶ pullback g π` to `pullback.lift β f w`. Establish `hcf : c ≫ pullback.fst g π = β` using `pullback.lift_fst _ _ _`. Establish `hce : ∀ j, e j ≫ c = ψ' j` using `fun j => by`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hcf, hβ, hψ'f]`. Rewrite using `[Category.assoc, pullback.lift_snd, hf, hψ's]`. Establish `loc : ∀ j, IsPullback (e j) (𝟙 (P j)) c (ψ' j)` using `fun j => by haveI := he j`. Use `(IsOpenImmersion.isPullback (𝟙 (P j)) (e j) (ψ' j) c (by rw [hce, Category.id_comp]) ?_).flip` and prove the remaining obligations. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `c x ∈ Set.range (ψ' j) ↔ x ∈ Set.range (e j)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Apply `hr j x` to reduce the goal to its premises. Use `⟨p j y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hcf, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ'f]`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, by rw [← Scheme.Hom.comp_apply, hce]⟩`. Establish `key : ∀ j : J, (MorphismProperty.isomorphisms Scheme) (pullback.snd c (ψ' j))` using `fun j => by`. Rewrite using `[← (loc j).isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)]`.

Conclude with `MorphismProperty.isomorphisms.infer_property _`. Establish `hiso : (MorphismProperty.isomorphisms Scheme) c` using `IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers J P ψ' hc) fun j => key j`. Use `haveI : IsIso c := hiso`. Conclude with `IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)`.
-/
theorem isPullback_of_openCover_target : ∀ (X G S B : Scheme.{0}) (β : X ⟶ G) (f : X ⟶ S) (g : G ⟶ B) (π : S ⟶ B), β ≫ g = f ≫ π → ∀ (J : Type) (Y P : J → Scheme.{0}) (ψ : ∀ j, Y j ⟶ G) (e : ∀ j, P j ⟶ X) (p : ∀ j, P j ⟶ Y j) (q : ∀ j, P j ⟶ S), (∀ j, IsOpenImmersion (ψ j)) → (∀ y : G, ∃ j, y ∈ Set.range (ψ j)) → (∀ j, IsOpenImmersion (e j)) → (∀ j, IsPullback (p j) (q j) (ψ j ≫ g) π) → (∀ j, e j ≫ β = p j ≫ ψ j) → (∀ j, e j ≫ f = q j) → (∀ (j : J) (x : X), β x ∈ Set.range (ψ j) → x ∈ Set.range (e j)) → IsPullback β f g π := by
  intro X G S B β f g π w J Y P ψ e p q hψ hcov he hP hβ hf hr
  let ψ' : ∀ j, P j ⟶ pullback g π := fun j =>
    pullback.lift (p j ≫ ψ j) (q j) (by rw [Category.assoc]; exact (hP j).w)
  have hψ'f : ∀ j, ψ' j ≫ pullback.fst g π = p j ≫ ψ j := fun j => pullback.lift_fst _ _ _
  have hψ's : ∀ j, ψ' j ≫ pullback.snd g π = q j := fun j => pullback.lift_snd _ _ _
  have sq : ∀ j, IsPullback (ψ' j) (p j) (pullback.fst g π) (ψ j) := fun j =>
    (IsPullback.of_bot (v₁₁ := ψ' j) (v₂₁ := pullback.snd g π) (by rw [hψ's]; exact hP j)
      (hψ'f j).symm (IsPullback.of_hasPullback g π)).flip
  haveI : ∀ j, IsOpenImmersion (ψ' j) := fun j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq j).flip (hψ j)
  have hc : ∀ z : (pullback g π : Scheme), ∃ j y, ψ' j y = z := by
    intro z
    obtain ⟨j, y, hy⟩ := hcov (pullback.fst g π z)
    obtain ⟨t, ht, -⟩ := Scheme.exists_preimage_of_isPullback (sq j) z y hy.symm
    exact ⟨j, t, ht⟩
  let c : X ⟶ pullback g π := pullback.lift β f w
  have hcf : c ≫ pullback.fst g π = β := pullback.lift_fst _ _ _
  have hce : ∀ j, e j ≫ c = ψ' j := fun j => by
    apply pullback.hom_ext
    · rw [Category.assoc, hcf, hβ, hψ'f]
    · rw [Category.assoc, pullback.lift_snd, hf, hψ's]
  have loc : ∀ j, IsPullback (e j) (𝟙 (P j)) c (ψ' j) := fun j => by
    haveI := he j
    refine (IsOpenImmersion.isPullback (𝟙 (P j)) (e j) (ψ' j) c
      (by rw [hce, Category.id_comp]) ?_).flip
    ext x
    change c x ∈ Set.range (ψ' j) ↔ x ∈ Set.range (e j)
    constructor
    · rintro ⟨y, hy⟩
      apply hr j x
      refine ⟨p j y, ?_⟩
      rw [← hcf, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ'f]
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, hce]⟩
  have key : ∀ j : J, (MorphismProperty.isomorphisms Scheme) (pullback.snd c (ψ' j)) := fun j => by
    rw [← (loc j).isoPullback_inv_snd,
      MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)]
    exact MorphismProperty.isomorphisms.infer_property _
  have hiso : (MorphismProperty.isomorphisms Scheme) c :=
    IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers J P ψ' hc) fun j => key j
  haveI : IsIso c := hiso
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
