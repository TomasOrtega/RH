import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDedFracLocalizationAway
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Models

namespace GlobalTheory.ModelRestrict

set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c R _ ω C g hd hg`. Set `R'` to `Localization.Away g`. Set `e : R →+* R'` to `algebraMap R R'`. Establish `hu : IsUnit (ω g)` using `IsUnit.mk0 _ hg`. Set `ω' : R' →+* c.F` to `IsLocalization.Away.lift g hu`.

Establish `hω : ω'.comp e = ω` using `IsLocalization.Away.lift_comp g hu`. Establish `hω' : spMap ω' ≫ spMap e = spMap ω`. Rewrite using `[← hω]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Use `haveI he : IsOpenImmersion (spMap e) := IsOpenImmersion.of_isLocalization g`.

Use `haveI : Flat C.s := C.flat`. Set `X'` to `pullback C.s (spMap e)`. Set `v : X' ⟶ C.X` to `pullback.fst C.s (spMap e)`. Set `s' : X' ⟶ Sp R'` to `pullback.snd C.s (spMap e)`. Use `haveI hv : IsOpenImmersion v := inferInstance`.

Establish `P : IsPullback (pullback.fst s' (spMap ω') ≫ v) (pullback.snd s' (spMap ω')) C.s (spMap ω)`. Use `(IsPullback.of_hasPullback s' (spMap ω')).paste_horiz (IsPullback.of_hasPullback C.s (spMap e))` as an intermediate fact. Rewrite `this` using `[hω']`. Then use the resulting hypothesis. Set `I` to `P.isoPullback`. Establish `hIf : I.inv ≫ pullback.fst s' (spMap ω') ≫ v = pullback.fst C.s (spMap ω)` using `P.isoPullback_inv_fst`.

Establish `hIs : I.inv ≫ pullback.snd s' (spMap ω') = pullback.snd C.s (spMap ω)` using `P.isoPullback_inv_snd`. Take `⟨t', ⟨mv⟩⟩` from `GlobalTheory.Models.Inhab.exists_pull v C.t`. Establish `hjv : (C.jQ ≫ I.inv ≫ pullback.fst s' (spMap ω')) ≫ v = C.jQ ≫ pullback.fst C.s (spMap ω)`. Simplify using `only [Category.assoc, hIf]`. Take `⟨m, -⟩` from `GlobalTheory.LevelCover.sab_cancel mv C.m (C.jQ ≫ I.inv ≫ pullback.fst s' (spMap ω')) hjv`.

Establish `hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X'`. Introduce `x`. Take `⟨h1, h2⟩` from `C.normal (v x)`. Set `e` to `(asIso (v.stalkMap x)).commRingCatIsoToRingEquiv`. Conclude with `⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩`.

Use `haveI := C.jQ_open`. Establish `hx : ∀ x, I.inv (I.hom x) = x` using `fun x => by`. Rewrite using `[← Scheme.Hom.comp_apply, I.hom_inv_id]`. Both sides reduce to the same expression. Establish `hy : ∀ y, I.hom (I.inv y) = y` using `fun y => by`.

Rewrite using `[← Scheme.Hom.comp_apply, I.inv_hom_id]`. Both sides reduce to the same expression. Establish `key : ∀ x, pullback.fst s' (spMap ω') x ∈ abLocus t'.G ↔ pullback.fst C.s (spMap ω) (I.hom x) ∈ abLocus C.t.G`. Introduce `x`. Establish `h` using `abLocus_pullback abLocusOne C.t.semi mv.cart.1 (pullback.fst s' (spMap ω') x)`.

Establish `h1 : (I.hom ≫ pullback.fst C.s (spMap ω)) x = (pullback.fst s' (spMap ω') ≫ v) x`. Rewrite using `[P.isoPullback_hom_fst]`. Simplify using `only [Scheme.Hom.comp_apply] at h1`. Rewrite using `[h1]`. Conclude with `h.symm`.

Set `C' : Model Xo c ω'` to `{ X := X' s := s' normal := hnorm proj := GlobalTheory.ProjSpace.isProjOver_pullback_snd e C.proj flat := inferInstance jQ := C.jQ ≫ I.inv jQ_over := by rw [Category.assoc, hIs, C.jQ_over] jQ_open := inferInstance jQ_dense := by`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]`. Conclude with `(Function.Surjective.denseRange fun y => ⟨I.hom y, hx y⟩).dense_image I.inv.continuous C.jQ_dense`. Use `t := t'`. Use `oF := C.oF`.

Use `m0 := C.m0`. Use `m := by`. Rewrite `m` using `[← Category.assoc]`. Conclude with `m`. Use `ab_gen := by`.

Use extensionality with `x`. Rewrite using `[Set.mem_preimage, key]`. Express the relevant statement in the definitionally equal form `I.hom x ∈ pullback.fst C.s (spMap ω) ⁻¹' abLocus C.t.G ↔ _`. Rewrite using `[C.ab_gen]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy'⟩`. Conclude with `⟨y, by rw [Scheme.Hom.comp_apply, hy', hx]⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, by rw [Scheme.Hom.comp_apply, hy]⟩ }`. Use `⟨R', inferInstance, e, ω', C', v, ?_, hω, GlobalTheory.Member.isDedFrac_away R c.F ω g hg hd ω' hω, hv, pullback.condition, ?_, ?_, ⟨mv⟩⟩` and prove the remaining obligations.

Establish `h0 : IsLocalization.Away g (Localization.Away g)` using `inferInstance`. Establish `h2 : (algebraMap R (Localization.Away g)).toAlgebra = (inferInstance : Algebra R (Localization.Away g))` using `Algebra.algebra_ext _ _ fun _ => rfl`. Conclude with `h2 ▸ h0`. Rewrite using `[Scheme.Pullback.range_fst] erw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]`. Both sides reduce to the same expression.

Use `show (C.jQ ≫ I.inv ≫ pullback.fst s' (spMap ω')) ≫ v = C.jQ ≫ pullback.fst _ _`. Conclude with `hjv`.
-/
theorem exists_restrict : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F} (C : Model Xo c ω) (g : R), IsDedFrac ω → ω g ≠ 0 → ∃ (R' : Type) (_ : CommRing R') (e : R →+* R') (ω' : R' →+* c.F) (C' : Model Xo c ω') (v : C'.X ⟶ C.X), @IsLocalization.Away R _ g R' _ e.toAlgebra ∧ ω'.comp e = ω ∧ IsDedFrac ω' ∧ IsOpenImmersion v ∧ v ≫ C.s = C'.s ≫ spMap e ∧ Set.range v = C.s ⁻¹' {x | g ∉ x.asIdeal} ∧ C'.j ≫ v = C.j ∧ Nonempty (SABMap C'.t C.t v) := by
  intro E _ _ _ H D l Xo c R _ ω C g hd hg
  let R' := Localization.Away g
  let e : R →+* R' := algebraMap R R'
  have hu : IsUnit (ω g) := IsUnit.mk0 _ hg
  let ω' : R' →+* c.F := IsLocalization.Away.lift g hu
  have hω : ω'.comp e = ω := IsLocalization.Away.lift_comp g hu
  have hω' : spMap ω' ≫ spMap e = spMap ω := by
    rw [← hω]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI he : IsOpenImmersion (spMap e) := IsOpenImmersion.of_isLocalization g
  haveI : Flat C.s := C.flat
  let X' := pullback C.s (spMap e)
  let v : X' ⟶ C.X := pullback.fst C.s (spMap e)
  let s' : X' ⟶ Sp R' := pullback.snd C.s (spMap e)
  haveI hv : IsOpenImmersion v := inferInstance

  have P : IsPullback (pullback.fst s' (spMap ω') ≫ v) (pullback.snd s' (spMap ω')) C.s (spMap ω) := by
    have := (IsPullback.of_hasPullback s' (spMap ω')).paste_horiz (IsPullback.of_hasPullback C.s (spMap e))
    rwa [hω'] at this
  let I := P.isoPullback
  have hIf : I.inv ≫ pullback.fst s' (spMap ω') ≫ v = pullback.fst C.s (spMap ω) := P.isoPullback_inv_fst
  have hIs : I.inv ≫ pullback.snd s' (spMap ω') = pullback.snd C.s (spMap ω) := P.isoPullback_inv_snd
  obtain ⟨t', ⟨mv⟩⟩ := GlobalTheory.Models.Inhab.exists_pull v C.t
  have hjv : (C.jQ ≫ I.inv ≫ pullback.fst s' (spMap ω')) ≫ v = C.jQ ≫ pullback.fst C.s (spMap ω) := by
    simp only [Category.assoc, hIf]
  obtain ⟨m, -⟩ := GlobalTheory.LevelCover.sab_cancel mv C.m (C.jQ ≫ I.inv ≫ pullback.fst s' (spMap ω')) hjv
  have hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' := by
    intro x
    obtain ⟨h1, h2⟩ := C.normal (v x)
    let e := (asIso (v.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  haveI := C.jQ_open
  have hx : ∀ x, I.inv (I.hom x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, I.hom_inv_id]; rfl
  have hy : ∀ y, I.hom (I.inv y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, I.inv_hom_id]; rfl
  have key : ∀ x, pullback.fst s' (spMap ω') x ∈ abLocus t'.G ↔ pullback.fst C.s (spMap ω) (I.hom x) ∈ abLocus C.t.G := by
    intro x
    have h := abLocus_pullback abLocusOne C.t.semi mv.cart.1 (pullback.fst s' (spMap ω') x)
    have h1 : (I.hom ≫ pullback.fst C.s (spMap ω)) x = (pullback.fst s' (spMap ω') ≫ v) x := by
      rw [P.isoPullback_hom_fst]
    simp only [Scheme.Hom.comp_apply] at h1
    rw [h1]; exact h.symm
  let C' : Model Xo c ω' :=
    { X := X'
      s := s'
      normal := hnorm
      proj := GlobalTheory.ProjSpace.isProjOver_pullback_snd e C.proj
      flat := inferInstance
      jQ := C.jQ ≫ I.inv
      jQ_over := by rw [Category.assoc, hIs, C.jQ_over]
      jQ_open := inferInstance
      jQ_dense := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
        exact (Function.Surjective.denseRange fun y => ⟨I.hom y, hx y⟩).dense_image I.inv.continuous C.jQ_dense
      t := t'
      oF := C.oF
      m0 := C.m0
      m := by
        rw [← Category.assoc] at m
        exact m
      ab_gen := by
        ext x
        rw [Set.mem_preimage, key]
        change I.hom x ∈ pullback.fst C.s (spMap ω) ⁻¹' abLocus C.t.G ↔ _
        rw [C.ab_gen]
        constructor
        · rintro ⟨y, hy'⟩
          exact ⟨y, by rw [Scheme.Hom.comp_apply, hy', hx]⟩
        · rintro ⟨y, rfl⟩
          exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]⟩ }
  refine ⟨R', inferInstance, e, ω', C', v, ?_, hω, GlobalTheory.Member.isDedFrac_away R c.F ω g hg hd ω' hω, hv,
    pullback.condition, ?_, ?_, ⟨mv⟩⟩
  · have h0 : IsLocalization.Away g (Localization.Away g) := inferInstance
    have h2 : (algebraMap R (Localization.Away g)).toAlgebra = (inferInstance : Algebra R (Localization.Away g)) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    exact h2 ▸ h0
  · rw [Scheme.Pullback.range_fst]
    erw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    rfl
  · show (C.jQ ≫ I.inv ≫ pullback.fst s' (spMap ω')) ≫ v = C.jQ ≫ pullback.fst _ _
    exact hjv

end GlobalTheory.ModelRestrict
