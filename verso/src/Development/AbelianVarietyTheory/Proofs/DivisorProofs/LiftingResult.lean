import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfGeo

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Z R k _ _ _ ψ hψ x yy hx`. Use `haveI := hψ`. Take `⟨g, hg⟩ : ∃ g : 𝓞 c.F →+* R, x ≫ Z.s = spMap g` from `⟨(Spec.preimage (x ≫ Z.s)).hom, (Spec.map_preimage _).symm⟩`. Take `⟨h, hh⟩ : ∃ h : c.F →+* k, yy ≫ Z.jQ ≫ pullback.snd _ _ = spMap h` from `⟨(Spec.preimage (yy ≫ Z.jQ ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩`. Establish `e : Z.j ≫ Z.s = (Z.jQ ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F)`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, Category.assoc]`. Establish `hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f₁ : A →+* B) (f₂ : B →+* C), spMap (f₂.comp f₁) = spMap f₂ ≫ spMap f₁`. Introduce `A B C _ _ _ f₁ f₂`. Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `hinj : ∀ {A B : Type} [CommRing A] [CommRing B] (f₁ f₂ : A →+* B), spMap f₁ = spMap f₂ → f₁ = f₂`. Introduce `A B _ _ f₁ f₂ hf`. Use `Spec.map_injective hf` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`. Establish `hcomp : ψ.comp g = h.comp (algebraMap (𝓞 c.F) c.F)`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hsp, hsp, ← hg, ← hh, ← Category.assoc, hx, Category.assoc, e]`. Simplify using `only [Category.assoc]`. Establish `hunit : ∀ y : nonZeroDivisors (𝓞 c.F), IsUnit (g y)`. Introduce `y`.

Establish `hy0 : algebraMap (𝓞 c.F) c.F y ≠ 0`. Introduce `h0`. Conclude with `nonZeroDivisors.coe_ne_zero y (IsFractionRing.injective (𝓞 c.F) c.F (h0.trans (map_zero _).symm))`. Establish `h1 : IsUnit (ψ (g y))`. Establish `: ψ (g y) = h (algebraMap (𝓞 c.F) c.F y)` using `congrArg (fun f : 𝓞 c.F →+* k => f y) hcomp`.

Rewrite using `[this]`. Conclude with `(map_ne_zero h |>.2 hy0).isUnit`. Conclude with `isUnit_of_map_unit ψ _ h1`. Set `g' : c.F →+* R` to `IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) hunit`. Establish `hg'a : g'.comp (algebraMap (𝓞 c.F) c.F) = g` using `IsLocalization.lift_comp _`.

Establish `hψg' : ψ.comp g' = h`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F))` to reduce the goal to its premises. Rewrite using `[RingHom.comp_assoc, hg'a, hcomp]`. Establish `hcond : x ≫ Z.s = spMap g' ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[← hsp, hg'a, hg]`.

Set `x' : Sp R ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F))` to `pullback.lift x (spMap g') hcond`. Establish `hx'1 : x' ≫ pullback.fst _ _ = x` using `pullback.lift_fst _ _ _`. Establish `hx'ψ : spMap ψ ≫ x' = yy ≫ Z.jQ`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hx'1, hx, Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]`.

Rewrite using `[Category.assoc, pullback.lift_snd, Category.assoc, hh, ← hsp, hψg']`. Use `haveI := Z.jQ_open`. Establish `hmem : x' (IsLocalRing.closedPoint R) ∈ Z.jQ.opensRange`. Establish `hc : spMap ψ (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R` using `Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of k) (f := CommRingCat.ofHom ψ)`. Rewrite using `[← hc]`.

Use `show (spMap ψ ≫ x') (IsLocalRing.closedPoint k) ∈ Z.jQ.opensRange`. Rewrite using `[hx'ψ]`. Conclude with `⟨yy (IsLocalRing.closedPoint k), (Scheme.Hom.comp_apply yy Z.jQ _).symm⟩`. Establish `hr : Set.range x' ⊆ Set.range Z.jQ`. Introduce and unpack `_ ⟨q, rfl⟩`.

Use `show q ∈ x' ⁻¹ᵁ Z.jQ.opensRange`. Rewrite using `[Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of R) x' hmem]`. Discharge the goal by the elementary cases of `trivial`. Use `⟨IsOpenImmersion.lift Z.jQ x' hr, ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hx'1]`.
-/
theorem liftSt : LiftSt := by
  intro E _ _ _ H Dw l Xo c Z R k _ _ _ ψ hψ x yy hx
  haveI := hψ
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 c.F →+* R, x ≫ Z.s = spMap g :=
    ⟨(Spec.preimage (x ≫ Z.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨h, hh⟩ : ∃ h : c.F →+* k, yy ≫ Z.jQ ≫ pullback.snd _ _ = spMap h :=
    ⟨(Spec.preimage (yy ≫ Z.jQ ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  have e : Z.j ≫ Z.s = (Z.jQ ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, Category.assoc]
  have hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f₁ : A →+* B) (f₂ : B →+* C),
      spMap (f₂.comp f₁) = spMap f₂ ≫ spMap f₁ := by
    intro A B C _ _ _ f₁ f₂
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] (f₁ f₂ : A →+* B), spMap f₁ = spMap f₂ → f₁ = f₂ := by
    intro A B _ _ f₁ f₂ hf
    have := Spec.map_injective hf
    exact congrArg CommRingCat.Hom.hom this
  have hcomp : ψ.comp g = h.comp (algebraMap (𝓞 c.F) c.F) := by
    apply hinj
    rw [hsp, hsp, ← hg, ← hh, ← Category.assoc, hx, Category.assoc, e]
    simp only [Category.assoc]
  have hunit : ∀ y : nonZeroDivisors (𝓞 c.F), IsUnit (g y) := by
    intro y
    have hy0 : algebraMap (𝓞 c.F) c.F y ≠ 0 := by
      intro h0
      exact nonZeroDivisors.coe_ne_zero y
        (IsFractionRing.injective (𝓞 c.F) c.F (h0.trans (map_zero _).symm))
    have h1 : IsUnit (ψ (g y)) := by
      have : ψ (g y) = h (algebraMap (𝓞 c.F) c.F y) := congrArg (fun f : 𝓞 c.F →+* k => f y) hcomp
      rw [this]
      exact (map_ne_zero h |>.2 hy0).isUnit
    exact isUnit_of_map_unit ψ _ h1
  let g' : c.F →+* R := IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) hunit
  have hg'a : g'.comp (algebraMap (𝓞 c.F) c.F) = g := IsLocalization.lift_comp _
  have hψg' : ψ.comp g' = h := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F))
    rw [RingHom.comp_assoc, hg'a, hcomp]
  have hcond : x ≫ Z.s = spMap g' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← hsp, hg'a, hg]
  let x' : Sp R ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift x (spMap g') hcond
  have hx'1 : x' ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx'ψ : spMap ψ ≫ x' = yy ≫ Z.jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hx'1, hx, Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, hh, ← hsp, hψg']
  haveI := Z.jQ_open
  have hmem : x' (IsLocalRing.closedPoint R) ∈ Z.jQ.opensRange := by
    have hc : spMap ψ (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R :=
      Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of k) (f := CommRingCat.ofHom ψ)
    rw [← hc]
    show (spMap ψ ≫ x') (IsLocalRing.closedPoint k) ∈ Z.jQ.opensRange
    rw [hx'ψ]
    exact ⟨yy (IsLocalRing.closedPoint k), (Scheme.Hom.comp_apply yy Z.jQ _).symm⟩
  have hr : Set.range x' ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    show q ∈ x' ⁻¹ᵁ Z.jQ.opensRange
    rw [Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of R) x' hmem]
    trivial
  refine ⟨IsOpenImmersion.lift Z.jQ x' hr, ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hx'1]

end GlobalTheory.HalfGeo
