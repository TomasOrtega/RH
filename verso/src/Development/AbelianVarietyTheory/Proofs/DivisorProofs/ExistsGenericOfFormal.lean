import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenericEnd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Use `U.smooth` as an intermediate fact. Use `U.separated` as an intermediate fact. Establish `: IsSchemeTheoreticallyDominant (jK R)` using `schDom_spec_map _ (IsFractionRing.injective R (FractionRing R))`. Establish `: QuasiCompact (jK R)` using `inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))`. Establish `: IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R))` using `.of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip`.

Use `ext1`. Use `ext_of_schDom G.hom (by rw [Over.w g, Over.w g']) (pullback.fst G.hom (jK R)) ?_` and prove the remaining obligations. Establish `e` using `congrArg (fun k => k.left ≫ pullback.fst G.hom (jK R)) h`. Simplify using `only [Over.pullback_map_left] at e`. Use `erw [pullback.lift_fst, pullback.lift_fst] at e`.

Conclude with `e`.
-/
theorem eq_of_generic (U : UnifPre I D A G) {g g' : G ⟶ G}
    (h : (Over.pullback (jK R)).map g = (Over.pullback (jK R)).map g') : g = g' := by
  have := U.smooth
  have := U.separated
  have : IsSchemeTheoreticallyDominant (jK R) :=
    schDom_spec_map _ (IsFractionRing.injective R (FractionRing R))
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  ext1
  refine ext_of_schDom G.hom (by rw [Over.w g, Over.w g']) (pullback.fst G.hom (jK R)) ?_
  have e := congrArg (fun k => k.left ≫ pullback.fst G.hom (jK R)) h
  simp only [Over.pullback_map_left] at e
  erw [pullback.lift_fst, pullback.lift_fst] at e
  exact e

/- English proof (translation)
Use `U.gen_hom` as an intermediate fact. Use `⟨U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom, inferInstance, fun g' _ hg' => ?_⟩` and prove the remaining obligations. Take `rfl : g' = g` from `eq_of_generic U (by`. Rewrite using `[← cancel_mono U.gen.hom, hg', Iso.hom_inv_id_assoc])`. Introduce `e`.

Take `⟨t, ht, hi⟩` from `hb.2.2.2 e`. Conclude with `⟨by rw [hgb]; exact hb.2.2.1 e, t, ht, by rw [hgb]; exact hi⟩`.
-/
theorem exists_generic_of_formal (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) (hb : FormalEnd U a h' b) (g : G ⟶ G) (hg : IsMonHom g)
    (hgb : ∀ e, (Over.pullback (thick R I e)).map g = b e) :
    ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g' : G ⟶ G, IsMonHom g' →
      (Over.pullback (jK R)).map g' ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U a h' g' := by
  have := U.gen_hom
  refine ⟨U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom, inferInstance, fun g' _ hg' => ?_⟩
  obtain rfl : g' = g := eq_of_generic U (by
    rw [← cancel_mono U.gen.hom, hg', Iso.hom_inv_id_assoc])
  intro e
  obtain ⟨t, ht, hi⟩ := hb.2.2.2 e
  exact ⟨by rw [hgb]; exact hb.2.2.1 e, t, ht, by rw [hgb]; exact hi⟩

end GlobalTheory.Mum.GenericEnd
