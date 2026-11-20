import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpiRingHomFieldClosureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExtendToFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHomCharZeroUnitsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericVanishingStalkVanishingStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntOpen

/- English proof (translation)
Establish `h1 : spMap g₁ ≫ spMap β = spMap g₂ ≫ spMap β`. Rewrite using `[← spMap_comp, ← spMap_comp, e]`. Establish `h2` using `Spec.map_injective ((cancel_mono (spMap β)).1 h1)`. Conclude with `congrArg CommRingCat.Hom.hom h2`.
-/
theorem epi_of_mono_spMap {O F : Type} [CommRing O] [CommRing F] (β : O →+* F) (h : Mono (spMap β))
    {T : Type} [CommRing T] (g₁ g₂ : F →+* T) (e : g₁.comp β = g₂.comp β) : g₁ = g₂ := by
  have h1 : spMap g₁ ≫ spMap β = spMap g₂ ≫ spMap β := by
    rw [← spMap_comp, ← spMap_comp, e]
  have h2 := Spec.map_injective ((cancel_mono (spMap β)).1 h1)
  exact congrArg CommRingCat.Hom.hom h2

/- English proof (translation)
Establish `hr : Set.range g ⊆ Set.range j`. Introduce and unpack `_ ⟨p, rfl⟩`. Establish `hs : p ⤳ IsLocalRing.closedPoint R` using `IsLocalRing.specializes_closedPoint p`. Conclude with `(hs.map g.continuous).mem_open j.isOpenEmbedding.isOpen_range h`. Conclude with `⟨IsOpenImmersion.lift j g hr, IsOpenImmersion.lift_fac _ _ _⟩`.
-/
theorem lift_local {R : CommRingCat} [IsLocalRing R] {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : Spec R ⟶ X) (h : g (IsLocalRing.closedPoint R) ∈ Set.range j) : ∃ u, u ≫ j = g := by
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    have hs : p ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint p
    exact (hs.map g.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift j g hr, IsOpenImmersion.lift_fac _ _ _⟩

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A z hβ`. Establish `hab : ∀ x : A.X, A.f x ∈ abLocus Y.t.G ↔ x ∈ abLocus A.t.G` using `abLocus_pullback abLocusOne Y.t.semi A.m.cart.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: IsOpenImmersion Y.jQ` using `Y.jQ_open`. Unfold `Model.j`.

Use `infer_instance`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : A.f (centre z) ∈ abLocus Y.t.G` using `(hab _).2 hx`. Use `haveI : FiniteDimensional ℚ c.F := c.fin`.

Use `haveI : NumberField c.F := {}`. Use `haveI : IsReduced A.X := by`. Establish `: ∀ x : A.X, _root_.IsReduced (A.X.presheaf.stalk x)` using `fun x => by`. Use `(A.normal x).1` as an intermediate fact. Use `infer_instance`.

Conclude with `isReduced_of_isReduced_stalk A.X`. Set `g : Spec (A.X.presheaf.stalk (centre z)) ⟶ Sp O` to `A.X.fromSpecStalk (centre z) ≫ A.f ≫ Y.s`. Set `θ : O →+* A.X.presheaf.stalk (centre z)` to `(Spec.preimage g).hom`. Establish `hk : ∀ a, β a = 0 → θ a = 0` using `fun a ha => GlobalTheory.T.generic_vanishing_stalk_vanishing A.X Ω O A.ξ A.all (A.f ≫ Y.s) (A.cst.comp β) A.cst_over (centre z) a (by simp [ha])`. Establish `hu : ∀ b, β b ≠ 0 → IsUnit (θ b)` using `fun b hb => GlobalTheory.T.local_hom_char_zero_units O c.F _ ℂ β θ (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) hk b hb`.

Take `⟨χ, hχ⟩` from `GlobalTheory.T.extend_to_fraction_field O c.F _ β θ (GlobalTheory.T.epi_ring_hom_field_closure O c.F β (fun T _ g₁ g₂ e => epi_of_mono_spMap β hβ g₁ g₂ e)) hu hk`. Establish `w : (A.X.fromSpecStalk (centre z) ≫ A.f) ≫ Y.s = spMap χ ≫ spMap β`. Rewrite using `[← spMap_comp, hχ, Category.assoc]`. Express the relevant statement in the definitionally equal form `g = _`. Rewrite using `[← Spec.map_preimage g]`.

Both sides reduce to the same expression. Use `haveI : IsOpenImmersion Y.jQ := Y.jQ_open`. Take `⟨u, hu⟩` from `lift_local Y.jQ (pullback.lift _ _ w) (by`. Rewrite using `[← Y.ab_gen]`. Use `show (pullback.lift _ _ w ≫ pullback.fst _ _) _ ∈ abLocus _`.

Rewrite using `[pullback.lift_fst]`. Establish `e1 : (A.X.fromSpecStalk (centre z) ≫ A.f) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z))) = A.f (centre z)` using `by show A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = _`. Rewrite using `[Scheme.fromSpecStalk_closedPoint]`. Conclude with `e1 ▸ hx')`. Use `⟨u, ?_⟩` and prove the remaining obligations.

Rewrite using `[Model.j, ← Category.assoc, hu, pullback.lift_fst]`. Introduce and unpack `⟨u, hu⟩ show centre z ∈ abLocus A.t.G`. Rewrite using `[← hab]`. Establish `h1 : A.f (centre z) = Y.j (u (IsLocalRing.closedPoint _))`. Establish `e1` using `congrArg (fun φ : Spec (A.X.presheaf.stalk (centre z)) ⟶ Y.X => φ (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) hu`.

Express the relevant statement in the definitionally equal form `Y.j (u (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) at e1`. Rewrite `e1` using `[Scheme.fromSpecStalk_closedPoint]`. Conclude with `e1.symm`. Rewrite using `[h1]`. Establish `h2 : Y.jQ (u (IsLocalRing.closedPoint _)) ∈ Set.range Y.jQ` using `⟨_, rfl⟩`.

Rewrite `h2` using `[← Y.ab_gen]`. Conclude with `h2`.
-/
theorem interior_iff_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A z hβ
  have hab : ∀ x : A.X, A.f x ∈ abLocus Y.t.G ↔ x ∈ abLocus A.t.G :=
    abLocus_pullback abLocusOne Y.t.semi A.m.cart.1
  refine ⟨?_, ?_⟩
  · have : IsOpenImmersion Y.jQ := Y.jQ_open
    unfold Model.j; infer_instance
  constructor
  · intro hx
    have hx' : A.f (centre z) ∈ abLocus Y.t.G := (hab _).2 hx
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := {}
    haveI : IsReduced A.X := by
      have : ∀ x : A.X, _root_.IsReduced (A.X.presheaf.stalk x) := fun x => by
        have := (A.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk A.X
    let g : Spec (A.X.presheaf.stalk (centre z)) ⟶ Sp O := A.X.fromSpecStalk (centre z) ≫ A.f ≫ Y.s
    let θ : O →+* A.X.presheaf.stalk (centre z) := (Spec.preimage g).hom
    have hk : ∀ a, β a = 0 → θ a = 0 := fun a ha =>
      GlobalTheory.T.generic_vanishing_stalk_vanishing A.X Ω O A.ξ A.all (A.f ≫ Y.s) (A.cst.comp β) A.cst_over (centre z) a (by simp [ha])
    have hu : ∀ b, β b ≠ 0 → IsUnit (θ b) := fun b hb =>
      GlobalTheory.T.local_hom_char_zero_units O c.F _ ℂ β θ (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) hk b hb
    obtain ⟨χ, hχ⟩ := GlobalTheory.T.extend_to_fraction_field O c.F _ β θ (GlobalTheory.T.epi_ring_hom_field_closure O c.F β (fun T _ g₁ g₂ e => epi_of_mono_spMap β hβ g₁ g₂ e)) hu hk
    have w : (A.X.fromSpecStalk (centre z) ≫ A.f) ≫ Y.s = spMap χ ≫ spMap β := by
      rw [← spMap_comp, hχ, Category.assoc]
      change g = _
      rw [← Spec.map_preimage g]
      rfl
    haveI : IsOpenImmersion Y.jQ := Y.jQ_open
    obtain ⟨u, hu⟩ := lift_local Y.jQ (pullback.lift _ _ w) (by
      rw [← Y.ab_gen]
      show (pullback.lift _ _ w ≫ pullback.fst _ _) _ ∈ abLocus _
      rw [pullback.lift_fst]
      have e1 : (A.X.fromSpecStalk (centre z) ≫ A.f) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z))) = A.f (centre z) := by
        show A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = _
        rw [Scheme.fromSpecStalk_closedPoint]
      exact e1 ▸ hx')
    refine ⟨u, ?_⟩
    rw [Model.j, ← Category.assoc, hu, pullback.lift_fst]
  · rintro ⟨u, hu⟩
    show centre z ∈ abLocus A.t.G
    rw [← hab]
    have h1 : A.f (centre z) = Y.j (u (IsLocalRing.closedPoint _)) := by
      have e1 := congrArg (fun φ : Spec (A.X.presheaf.stalk (centre z)) ⟶ Y.X => φ (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) hu
      change Y.j (u (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) at e1
      rw [Scheme.fromSpecStalk_closedPoint] at e1
      exact e1.symm
    rw [h1]
    have h2 : Y.jQ (u (IsLocalRing.closedPoint _)) ∈ Set.range Y.jQ := ⟨_, rfl⟩
    rw [← Y.ab_gen] at h2
    exact h2

end GlobalTheory.CompanionTheory.Ar.IntOpen
