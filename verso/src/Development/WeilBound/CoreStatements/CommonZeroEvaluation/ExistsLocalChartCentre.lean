import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenMapEqOfFactor

open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

/- English proof (translation)
Introduce and unpack `_ ⟨s, rfl⟩ h0 hi`. Establish `hu : IsUnit (ψ s)`. Use `IsUnit.of_mul_eq_one (⟨_, hi⟩ : A) (Subtype.ext ?_)` and prove the remaining obligations. Establish `h1` using `mul_inv_cancel₀ h0`. Substitute `hg` using the available equality.

Conclude with `h1`. Take `⟨s', hs'⟩` from `(IsUnit.of_map ψ s hu).exists_right_inv`. Use `⟨s', ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg g hs'`. Rewrite `h2` using `[map_mul, map_one]`.

Conclude with `eq_inv_of_mul_eq_one_right h2`.
-/
theorem inv_mem_range_of_local {S Ω : Type} [CommRing S] [Field Ω] (A : Subring Ω) (ψ : S →+* A)
    (hψ : IsLocalHom ψ) (g : S →+* Ω) (hg : g = (algebraMap A Ω).comp ψ) :
    ∀ a ∈ g.range, a ≠ 0 → a⁻¹ ∈ A → a⁻¹ ∈ g.range := by
  rintro _ ⟨s, rfl⟩ h0 hi
  have hu : IsUnit (ψ s) := by
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : A) (Subtype.ext ?_)
    have h1 := mul_inv_cancel₀ h0
    subst hg
    exact h1
  obtain ⟨s', hs'⟩ := (IsUnit.of_map ψ s hu).exists_right_inv
  refine ⟨s', ?_⟩
  have h2 := congrArg g hs'
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_right h2

/- English proof (translation)
Introduce `X Ω _ ξ κ x T A _ c hc hA`. Take `⟨V, hV, hmem⟩` from `T.affine c hc`. Establish `hgV : genPt ξ ∈ V`. Use `(hmem _).2 ⟨specializes_rfl, hc, fun j => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `T.gen.bij.2 (x j / x c)`.

Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs]`. Simplify using `only [genMap, TopCat.Presheaf.stalkSpecializes_refl]`. Both sides reduce to the same expression. Set `ρ : Γ(X, V) →+* Ω` to `(X.presheaf.germ V (genPt ξ) hgV ≫ Scheme.stalkClosedPointTo ξ).hom`.

Establish `hρ : ∀ (f : Γ(X, V)) (p : Cpt ξ) (hp : p.1 ∈ V), genMap ξ p (X.presheaf.germ V p.1 hp f) = ρ f` using `fun f p hp => genMap_germ' V hgV f p hp`. Establish `hρA : ∀ f, ρ f ∈ A` using `fun f => by`. Establish `h1 : ρ f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)` using `(T.ring c hc _).2 fun p hp => ⟨_, hρ f p ((hmem _).2 ⟨p.2, hp⟩)⟩`. Generalize the expression as in `ρ f = t at h1`. Proceed by induction on `h1 using Algebra.adjoin_induction with`.

Consider the case `mem a ha => obtain ⟨j, rfl⟩ := ha`. Conclude with `hA j`. Consider the case `algebraMap r => simpa using intCast_mem A r`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`.

Set `φ : Γ(X, V) ⟶ CommRingCat.of A` to `CommRingCat.ofHom (ρ.codRestrict A hρA)`. Establish `hz : centre (Spec.map φ ≫ hV.fromSpec) ∈ V`. Express the relevant statement in the definitionally equal form `_ ∈ (V : Set X)`. Rewrite using `[← hV.range_fromSpec]`. Conclude with `⟨_, rfl⟩`.

Take `⟨hs, hin⟩` from `(hmem _).1 hz`. Establish `hfac : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ Spec.map φ ≫ hV.fromSpec = ξ`. Establish `e1 : φ ≫ CommRingCat.ofHom (algebraMap A Ω) = X.presheaf.germ V (genPt ξ) hgV ≫ Scheme.stalkClosedPointTo ξ` using `rfl`. Establish `e2 : Spec.map (X.presheaf.germ V (genPt ξ) hgV) ≫ hV.fromSpec = X.fromSpecStalk (genPt ξ)` using `hV.fromSpecStalk_eq_fromSpecStalk hgV`. Rewrite using `[← Category.assoc, ← Spec.map_comp, e1]`.

Conclude with `(congrArg (· ≫ hV.fromSpec) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans ((congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e2).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))`. Establish `hg` using `genMap_eq_of_factor (algebraMap A Ω) _ hfac hs`. Use `⟨Spec.map φ ≫ hV.fromSpec, hs, hfac, hin, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[hg]`.

Conclude with `Subtype.property _`. Conclude with `inv_mem_range_of_local A (Scheme.stalkClosedPointTo (Spec.map φ ≫ hV.fromSpec)).hom (Scheme.isLocalHom_stalkClosedPointTo _) _ hg`.
-/
theorem exists_local_chart_centre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ (A : Subring Ω) [IsLocalRing A] (c : κ), x c ≠ 0 → (∀ c', x c' / x c ∈ A) → ∃ (zq : Spec (CommRingCat.of A) ⟶ X) (hc : genPt ξ ⤳ centre zq), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq = ξ ∧ InChart ξ x c ⟨centre zq, hc⟩ ∧ (∀ a ∈ regAt ξ ⟨centre zq, hc⟩, a ∈ A) ∧ (∀ a ∈ regAt ξ ⟨centre zq, hc⟩, a ≠ 0 → a⁻¹ ∈ A → a⁻¹ ∈ regAt ξ ⟨centre zq, hc⟩) := by
  intro X Ω _ ξ κ x T A _ c hc hA
  obtain ⟨V, hV, hmem⟩ := T.affine c hc
  have hgV : genPt ξ ∈ V := by
    refine (hmem _).2 ⟨specializes_rfl, hc, fun j => ?_⟩
    obtain ⟨s, hs⟩ := T.gen.bij.2 (x j / x c)
    refine ⟨s, ?_⟩
    rw [← hs]
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  let ρ : Γ(X, V) →+* Ω := (X.presheaf.germ V (genPt ξ) hgV ≫ Scheme.stalkClosedPointTo ξ).hom
  have hρ : ∀ (f : Γ(X, V)) (p : Cpt ξ) (hp : p.1 ∈ V), genMap ξ p (X.presheaf.germ V p.1 hp f) = ρ f :=
    fun f p hp => genMap_germ' V hgV f p hp
  have hρA : ∀ f, ρ f ∈ A := fun f => by
    have h1 : ρ f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (T.ring c hc _).2 fun p hp => ⟨_, hρ f p ((hmem _).2 ⟨p.2, hp⟩)⟩
    generalize ρ f = t at h1
    induction h1 using Algebra.adjoin_induction with
    | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hA j
    | algebraMap r => simpa using intCast_mem A r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  let φ : Γ(X, V) ⟶ CommRingCat.of A := CommRingCat.ofHom (ρ.codRestrict A hρA)
  have hz : centre (Spec.map φ ≫ hV.fromSpec) ∈ V := by
    change _ ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨hs, hin⟩ := (hmem _).1 hz
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ Spec.map φ ≫ hV.fromSpec = ξ := by
    have e1 : φ ≫ CommRingCat.ofHom (algebraMap A Ω) =
        X.presheaf.germ V (genPt ξ) hgV ≫ Scheme.stalkClosedPointTo ξ := rfl
    have e2 : Spec.map (X.presheaf.germ V (genPt ξ) hgV) ≫ hV.fromSpec = X.fromSpecStalk (genPt ξ) :=
      hV.fromSpecStalk_eq_fromSpecStalk hgV
    rw [← Category.assoc, ← Spec.map_comp, e1]
    exact (congrArg (· ≫ hV.fromSpec) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e2).trans
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))
  have hg := genMap_eq_of_factor (algebraMap A Ω) _ hfac hs
  refine ⟨Spec.map φ ≫ hV.fromSpec, hs, hfac, hin, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [hg]
    exact Subtype.property _
  · exact inv_mem_range_of_local A (Scheme.stalkClosedPointTo (Spec.map φ ≫ hV.fromSpec)).hom
      (Scheme.isLocalHom_stalkClosedPointTo _) _ hg

end ModelDimension
