import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Substitute `hc` using the available equality. Simplify using `[TopCat.Presheaf.stalkSpecializes_refl]`.
-/
theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c)
    (h' : genPt ξ ⤳ c') (s : X.presheaf.stalk c) :
    genMap ξ ⟨c', h'⟩ (X.presheaf.stalkSpecializes (specializes_of_eq hc) s) = genMap ξ ⟨c, h⟩ s := by
  subst hc
  simp [TopCat.Presheaf.stalkSpecializes_refl]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `X.fromSpecStalk x ((Spec.map φ) (IsLocalRing.closedPoint R)) = x`. Rewrite using `[Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]`.
-/
theorem closedPoint_specMap_fromSpecStalk {R : CommRingCat.{0}} [IsLocalRing R] (x : X)
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x ((Spec.map φ) (IsLocalRing.closedPoint R)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/- English proof (translation)
Substitute `hxy` using the available equality. Simplify using `only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]`.
-/
private theorem stalkSpecializes_comp_comp_eq_of_eq {x y : X} (h1 : x ⤳ y) (h2 : y ⤳ x) (hxy : x = y)
    {R : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ R) :
    X.presheaf.stalkSpecializes h2 ≫ X.presheaf.stalkSpecializes h1 ≫ g = g := by
  subst hxy
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/- English proof (translation)
Establish `key` using `(SpecToEquivOfLocalRing (X := X) (R := CommRingCat.of K)).apply_symm_apply ⟨x, ⟨φ, inferInstance⟩⟩`. Take `⟨h, h2⟩` from `SpecToEquivOfLocalRing_eq_iff.mp key`. Rewrite using `[show Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = _ from h2, TopCat.Presheaf.stalkCongr_hom]`. Conclude with `stalkSpecializes_comp_comp_eq_of_eq _ _ hc.symm φ`.
-/
theorem stalkSpecializes_stalkClosedPointTo {K : Type} [Field K] (x : X)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom φ.hom]
    (hc : (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint (CommRingCat.of K)) = x) :
    X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = φ := by
  have key := (SpecToEquivOfLocalRing (X := X) (R := CommRingCat.of K)).apply_symm_apply ⟨x, ⟨φ, inferInstance⟩⟩
  obtain ⟨h, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp key
  rw [show Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = _ from h2,
    TopCat.Presheaf.stalkCongr_hom]
  exact stalkSpecializes_comp_comp_eq_of_eq _ _ hc.symm φ

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a ha => by rcases eq_or_ne a 0 with rfl | h · simp at ha · exact h.isUnit⟩`.
-/
private theorem isLocalHom_of_field' {K K' : Type} [Field K] [Field K'] (f : K →+* K') : IsLocalHom f :=
  ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩

/- English proof (translation)
Take `⟨h, s, hs, hr⟩` from `hv`. Substitute `e` using the available equality. Take `⟨ψ, hψ⟩ : ∃ ψ : X.presheaf.stalk (centre w) ⟶ CommRingCat.of K', ψ = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f` from `⟨_, rfl⟩`. Use `haveI : IsLocalHom ψ.hom := by haveI := isLocalHom_of_field' f`. Establish `hh : ψ.hom = f.comp (Scheme.stalkClosedPointTo w).hom`.

Substitute `hψ` using the available equality. Both sides reduce to the same expression. Rewrite using `[hh]`. Conclude with `@RingHom.isLocalHom_comp _ _ _ _ _ _ f (Scheme.stalkClosedPointTo w).hom (isLocalHom_of_field' f) (Scheme.isLocalHom_stalkClosedPointTo w)`. Establish `hφ` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk w`.

Establish `hw' : Spec.map (CommRingCat.ofHom f) ≫ w = Spec.map ψ ≫ X.fromSpecStalk (centre w)`. Rewrite using `[hψ]`. Use `erw [Spec.map_comp, Category.assoc]`. Conclude with `congrArg (Spec.map (CommRingCat.ofHom f) ≫ ·) hφ.symm`. Rewrite using `[hw']`.

Establish `hc` using `closedPoint_specMap_fromSpecStalk (centre w) ψ`. Establish `hc' : centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) = centre w` using `hc`. Establish `h' : genPt ξ ⤳ centre (Spec.map ψ ≫ X.fromSpecStalk (centre w))`. Rewrite using `[hc']`. Conclude with `h`.

Use `⟨h', X.presheaf.stalkSpecializes (specializes_of_eq hc') s, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(genMap_stalkSpecializes ξ hc' h h' s).trans hs`. Establish `H3` using `stalkSpecializes_stalkClosedPointTo (centre w) ψ hc`. Establish `H : (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫ Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk (centre w))).hom s = ψ.hom s` using `congrArg (fun g => g.hom s) H3`. Establish `hψs : ψ.hom s = f u`.

Rewrite using `[← hr]`. Substitute `hψ` using the available equality. Both sides reduce to the same expression. Conclude with `H.trans hψs`.
-/
theorem valAt_of_field_map {K K' : Type} [Field K] [Field K'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (w : Spec (CommRingCat.of K) ⟶ X) (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K')
    (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') {a : Ω} {u : K} (hv : ValAt ξ w a u) :
    ValAt ξ w' a (f u) := by
  obtain ⟨h, s, hs, hr⟩ := hv
  subst e
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X.presheaf.stalk (centre w) ⟶ CommRingCat.of K',
      ψ = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := ⟨_, rfl⟩
  haveI : IsLocalHom ψ.hom := by
    haveI := isLocalHom_of_field' f
    have hh : ψ.hom = f.comp (Scheme.stalkClosedPointTo w).hom := by
      subst hψ
      rfl
    rw [hh]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ f (Scheme.stalkClosedPointTo w).hom (isLocalHom_of_field' f)
      (Scheme.isLocalHom_stalkClosedPointTo w)
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk w
  have hw' : Spec.map (CommRingCat.ofHom f) ≫ w = Spec.map ψ ≫ X.fromSpecStalk (centre w) := by
    rw [hψ]
    erw [Spec.map_comp, Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom f) ≫ ·) hφ.symm
  rw [hw']
  have hc := closedPoint_specMap_fromSpecStalk (centre w) ψ
  have hc' : centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) = centre w := hc
  have h' : genPt ξ ⤳ centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) := by
    rw [hc']
    exact h
  refine ⟨h', X.presheaf.stalkSpecializes (specializes_of_eq hc') s, ?_, ?_⟩
  · exact (genMap_stalkSpecializes ξ hc' h h' s).trans hs
  · have H3 := stalkSpecializes_stalkClosedPointTo (centre w) ψ hc
    have H : (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
        Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk (centre w))).hom s = ψ.hom s :=
      congrArg (fun g => g.hom s) H3
    have hψs : ψ.hom s = f u := by
      rw [← hr]
      subst hψ
      rfl
    exact H.trans hψs

/- English proof (translation)
Introduce `X Ω _ ξ L _ _ z σ a u hv`. Conclude with `valAt_of_field_map ξ _ _ σ (by rw [← Category.assoc]; congr 1; exact (Spec.map_comp _ _).symm) hv`.
-/
theorem valAt_complex : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  intro X Ω _ ξ L _ _ z σ a u hv
  exact valAt_of_field_map ξ _ _ σ (by rw [← Category.assoc]; congr 1; exact (Spec.map_comp _ _).symm) hv

end GlobalTheory.CompanionTheory.Ar.RootHt.PullVal
