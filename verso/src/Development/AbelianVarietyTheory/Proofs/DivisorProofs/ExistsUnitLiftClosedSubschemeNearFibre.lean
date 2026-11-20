import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

/- English proof (translation)
Introduce `X X' Z Z' p i i' p' h hp hi W x hx u`. Establish `hi' : IsClosedImmersion i'` using `MorphismProperty.of_isPullback h.flip hi`. Establish `hw : ∀ z : Z', p (i' z) = i (p' z)` using `fun z => by`. Rewrite using `[← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]`. Distinguish the cases in `hxr : x ∈ Set.range i`.

Use `swap`. Use `⟨W ⊓ ⟨(Set.range i)ᶜ, hi.base_closed.isClosed_range.isOpen_compl⟩, 1, inf_le_left, ⟨hx, hxr⟩, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `absurd ⟨p' z, (hw z).symm⟩ hz.2`. Take `⟨z0, hz0⟩` from `hxr`. Take `⟨W₀, hW₀, hxW₀, hW₀W⟩` from `exists_isAffineOpen_mem_and_subset hx`.

Establish `hle0 : W₀ ≤ W` using `hW₀W`. Establish `hA : IsAffineOpen (p ⁻¹ᵁ W₀)` using `IsAffineHom.isAffine_preimage _ hW₀`. Set `u0 : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W₀))` to `(Z'.presheaf.map (homOfLE (i'.preimage_mono (p.preimage_mono hle0))).op).hom u.val`. Establish `hu0 : IsUnit u0` using `(Units.isUnit u).map _`. Take `⟨t, ht⟩` from `Scheme.Hom.app_surjective i' (p ⁻¹ᵁ W₀) hA u0`.

Establish `hC : IsClosed ((X'.basicOpen t : Set X')ᶜ)` using `(X'.basicOpen t).isOpen.isClosed_compl`. Set `W' : X.Opens` to `W₀ ⊓ ⟨(p '' (X'.basicOpen t : Set X')ᶜ)ᶜ, (p.isClosedMap _ hC).isOpen_compl⟩`. Establish `hsub : p ⁻¹ᵁ W' ≤ X'.basicOpen t` using `fun y hy => by`. Assume the negation of the conclusion as `hc`. Conclude with `hy.2 ⟨y, hc, rfl⟩`.

Establish `hx' : x ∈ W'`. Use `⟨hxW₀, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hyC, hy⟩`. Take `⟨z', hz'1, -⟩` from `Scheme.exists_preimage_of_isPullback h y z0 (hy.trans hz0.symm)`. Apply `hyC` to reduce the goal to its premises.

Establish `hz'W : z' ∈ i' ⁻¹ᵁ (p ⁻¹ᵁ W₀)` using `by show p (i' z') ∈ W₀`. Rewrite using `[hz'1, hy]`. Conclude with `hxW₀`. Establish `: z' ∈ i' ⁻¹ᵁ X'.basicOpen t`. Rewrite using `[Scheme.preimage_basicOpen, ht, Scheme.basicOpen_of_isUnit _ hu0]`.

Conclude with `hz'W`. Rewrite using `[← hz'1]`. Conclude with `this`. Establish `hle' : p ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W₀` using `hsub.trans (X'.basicOpen_le t)`. Establish `hunit : IsUnit ((X'.presheaf.map (homOfLE hle').op).hom t)`.

Use `(X'.toRingedSpace.isUnit_res_basicOpen t).map (X'.presheaf.map (homOfLE hsub).op).hom` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = (X'.presheaf.map (homOfLE (X'.basicOpen_le t)).op ≫ X'.presheaf.map (homOfLE hsub).op).hom t`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression.

Use `⟨W', hunit.unit, inf_le_left.trans hle0, hx', fun z hz => ?_⟩` and prove the remaining obligations. Establish `hle2 : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W)` using `i'.preimage_mono (p.preimage_mono (inf_le_left.trans hle0))`. Rewrite using `[← gm_id_pull i' z (p ⁻¹ᵁ W') hz, ← gm_res (𝟙 Z') z hle2 hz]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises.

Use `show (i'.app (p ⁻¹ᵁ W')).hom ((X'.presheaf.map (homOfLE hle').op).hom t) = (Z'.presheaf.map (homOfLE hle2).op).hom u.val`. Establish `e` using `congrArg (fun φ => φ.hom t) (i'.naturality (homOfLE hle').op)`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e`. Rewrite using `[e, ht]`. Use `show (Z'.presheaf.map _).hom ((Z'.presheaf.map _).hom u.val) = _`.

Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem unit_lift_near_fibre : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → ∀ (W : X.Opens) (x : X), x ∈ W → ∀ u : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W))ˣ, ∃ (W' : X.Opens) (u' : Γ(X', p ⁻¹ᵁ W')ˣ), W' ≤ W ∧ x ∈ W' ∧ ∀ z : Z', p (i' z) ∈ W' → gm i' z (p ⁻¹ᵁ W') u' = gm (𝟙 Z') z (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) u := by
  intro X X' Z Z' p i i' p' h hp hi W x hx u
  have hi' : IsClosedImmersion i' := MorphismProperty.of_isPullback h.flip hi
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  by_cases hxr : x ∈ Set.range i
  swap
  · refine ⟨W ⊓ ⟨(Set.range i)ᶜ, hi.base_closed.isClosed_range.isOpen_compl⟩, 1, inf_le_left, ⟨hx, hxr⟩,
      fun z hz => ?_⟩
    exact absurd ⟨p' z, (hw z).symm⟩ hz.2
  obtain ⟨z0, hz0⟩ := hxr
  obtain ⟨W₀, hW₀, hxW₀, hW₀W⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle0 : W₀ ≤ W := hW₀W
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineHom.isAffine_preimage _ hW₀
  let u0 : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W₀)) :=
    (Z'.presheaf.map (homOfLE (i'.preimage_mono (p.preimage_mono hle0))).op).hom u.val
  have hu0 : IsUnit u0 := (Units.isUnit u).map _
  obtain ⟨t, ht⟩ := Scheme.Hom.app_surjective i' (p ⁻¹ᵁ W₀) hA u0
  have hC : IsClosed ((X'.basicOpen t : Set X')ᶜ) := (X'.basicOpen t).isOpen.isClosed_compl
  let W' : X.Opens := W₀ ⊓ ⟨(p '' (X'.basicOpen t : Set X')ᶜ)ᶜ, (p.isClosedMap _ hC).isOpen_compl⟩
  have hsub : p ⁻¹ᵁ W' ≤ X'.basicOpen t := fun y hy => by
    by_contra hc
    exact hy.2 ⟨y, hc, rfl⟩
  have hx' : x ∈ W' := by
    refine ⟨hxW₀, ?_⟩
    rintro ⟨y, hyC, hy⟩
    obtain ⟨z', hz'1, -⟩ := Scheme.exists_preimage_of_isPullback h y z0 (hy.trans hz0.symm)
    apply hyC
    have hz'W : z' ∈ i' ⁻¹ᵁ (p ⁻¹ᵁ W₀) := by
      show p (i' z') ∈ W₀
      rw [hz'1, hy]; exact hxW₀
    have : z' ∈ i' ⁻¹ᵁ X'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, Scheme.basicOpen_of_isUnit _ hu0]
      exact hz'W
    rw [← hz'1]; exact this
  have hle' : p ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W₀ := hsub.trans (X'.basicOpen_le t)
  have hunit : IsUnit ((X'.presheaf.map (homOfLE hle').op).hom t) := by
    have := (X'.toRingedSpace.isUnit_res_basicOpen t).map (X'.presheaf.map (homOfLE hsub).op).hom
    convert this using 1
    change _ = (X'.presheaf.map (homOfLE (X'.basicOpen_le t)).op ≫ X'.presheaf.map (homOfLE hsub).op).hom t
    rw [← Functor.map_comp]
    rfl
  refine ⟨W', hunit.unit, inf_le_left.trans hle0, hx', fun z hz => ?_⟩
  have hle2 : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) :=
    i'.preimage_mono (p.preimage_mono (inf_le_left.trans hle0))
  rw [← gm_id_pull i' z (p ⁻¹ᵁ W') hz, ← gm_res (𝟙 Z') z hle2 hz]
  congr 1
  apply Units.ext
  show (i'.app (p ⁻¹ᵁ W')).hom ((X'.presheaf.map (homOfLE hle').op).hom t) =
    (Z'.presheaf.map (homOfLE hle2).op).hom u.val
  have e := congrArg (fun φ => φ.hom t) (i'.naturality (homOfLE hle').op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, ht]
  show (Z'.presheaf.map _).hom ((Z'.presheaf.map _).hom u.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Pinch
