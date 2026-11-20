import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SameGenericPointCharts

/- English proof (translation)
Establish `h' : ξ (IsLocalRing.closedPoint Ω) ⤳ w (IsLocalRing.closedPoint R)` using `h`. Establish `key : X.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom φ`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono (X.fromSpecStalk (w (IsLocalRing.closedPoint R)))]`. Rewrite using `[Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hw, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`.

Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ`. Conclude with `congrArg CommRingCat.Hom.hom key`.
-/
theorem genMap_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {R : Type} [CommRing R] [IsLocalRing R] (φ : R →+* Ω) (w : Spec (CommRingCat.of R) ⟶ X)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫ w = ξ) (h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ w (IsLocalRing.closedPoint R)) :
    genMap ξ ⟨_, h⟩ = φ.comp (Scheme.stalkClosedPointTo w).hom := by
  have h' : ξ (IsLocalRing.closedPoint Ω) ⤳ w (IsLocalRing.closedPoint R) := h
  have key : X.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ
      = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (w (IsLocalRing.closedPoint R)))]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hw, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  exact congrArg CommRingCat.Hom.hom key

/- English proof (translation)
Substitute `hw` using the available equality. Use `(IsLocalRing.specializes_closedPoint (R := R) (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint Ω))).map w.continuous` as an intermediate fact. Conclude with `this`.
-/
theorem spec_closed {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {R : Type} [CommRing R] [IsLocalRing R] (φ : R →+* Ω) (w : Spec (CommRingCat.of R) ⟶ X)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫ w = ξ) : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ w (IsLocalRing.closedPoint R) := by
  subst hw
  have := (IsLocalRing.specializes_closedPoint (R := R)
    (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint Ω))).map w.continuous
  exact this

/- English proof (translation)
Establish `h` using `spec_closed ξ φ w hw`. Use `⟨h, hc, fun c' => ?_⟩` and prove the remaining obligations. Take `⟨c₀, h0, hreg⟩` from `T.cover ⟨_, h⟩`. Take `⟨a, ha⟩` from `hreg c`. Take `⟨b, hb⟩` from `hx c₀`.

Establish `ha' : φ ((Scheme.stalkClosedPointTo w).hom a) = x c / x c₀`. Rewrite using `[← ha, genMap_eq ξ φ w hw h]`. Both sides reduce to the same expression. Establish `hu : IsUnit ((Scheme.stalkClosedPointTo w).hom a)`. Use `IsUnit.of_mul_eq_one b (hφ ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, ha', hb, map_one]`. Clear the denominators using the available nonvanishing facts. Establish `hu' : IsUnit a` using `IsLocalHom.map_nonunit _ hu`. Take `⟨a', haa⟩` from `hu'.exists_right_inv`. Establish `h1 : genMap ξ ⟨_, h⟩ a' = x c₀ / x c`.

Use `congrArg (genMap ξ ⟨_, h⟩) haa` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, ha]`. Rewrite using `[eq_inv_of_mul_eq_one_right this, inv_div]`. Establish `: x c' / x c = x c' / x c₀ * (x c₀ / x c)` using `by field_simp`. Rewrite using `[this]`.

Conclude with `mul_mem (hreg c') ⟨a', h1⟩`.
-/
theorem chart_local {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {κ : Type} (x : κ → Ω) (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    {R : Type} [CommRing R] [IsLocalRing R] (φ : R →+* Ω) (hφ : Function.Injective φ)
    (hx : ∀ c', x c' / x c ∈ φ.range) (w : Spec (CommRingCat.of R) ⟶ X)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫ w = ξ) :
    ∃ h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ w (IsLocalRing.closedPoint R), InChart ξ x c ⟨_, h⟩ := by
  have h := spec_closed ξ φ w hw
  refine ⟨h, hc, fun c' => ?_⟩
  obtain ⟨c₀, h0, hreg⟩ := T.cover ⟨_, h⟩
  obtain ⟨a, ha⟩ := hreg c
  obtain ⟨b, hb⟩ := hx c₀
  have ha' : φ ((Scheme.stalkClosedPointTo w).hom a) = x c / x c₀ := by
    rw [← ha, genMap_eq ξ φ w hw h]; rfl
  have hu : IsUnit ((Scheme.stalkClosedPointTo w).hom a) := by
    refine IsUnit.of_mul_eq_one b (hφ ?_)
    rw [map_mul, ha', hb, map_one]
    field_simp
  have hu' : IsUnit a := IsLocalHom.map_nonunit _ hu
  obtain ⟨a', haa⟩ := hu'.exists_right_inv
  have h1 : genMap ξ ⟨_, h⟩ a' = x c₀ / x c := by
    have := congrArg (genMap ξ ⟨_, h⟩) haa
    rw [map_mul, map_one, ha] at this
    rw [eq_inv_of_mul_eq_one_right this, inv_div]
  have : x c' / x c = x c' / x c₀ * (x c₀ / x c) := by field_simp
  rw [this]
  exact mul_mem (hreg c') ⟨a', h1⟩

/- English proof (translation)
Set `Q : PrimeSpectrum B` to `P`. Establish `hun : ∀ y : Q.asIdeal.primeCompl, IsUnit (i y)`. Introduce `y`. Use `isUnit_iff_ne_zero.2 fun h => y.2 ?_` and prove the remaining obligations. Establish `: (y : B) = 0` using `hi (by rw [h, map_zero])`.

Rewrite using `[this]`. Conclude with `Q.asIdeal.zero_mem`. Set `R` to `Localization.AtPrime Q.asIdeal`. Set `φ : R →+* Ω` to `IsLocalization.lift hun`. Establish `hφi : φ.comp (algebraMap B R) = i` using `IsLocalization.lift_comp hun`.

Establish `hφ : Function.Injective φ`. Rewrite using `[IsLocalization.lift_injective_iff]`. Introduce `a b`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[← hφi]`. Conclude with `congrArg φ h`. Introduce `h`. Rewrite using `[hi h]`. Establish `hx' : ∀ c', x c' / x c ∈ φ.range`.

Introduce `c'`. Take `⟨b, hb⟩` from `hx c'`. Conclude with `⟨algebraMap B R b, by rw [← hb, ← hφi]; rfl⟩`. Use `chart_local ξ x T c hc φ hφ hx' (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (by` as an intermediate fact. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφi, hz])`.

Establish `e : (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (IsLocalRing.closedPoint R) = z P`. Establish `e1 : Spec.map (CommRingCat.ofHom (algebraMap B R)) (IsLocalRing.closedPoint R) = P` using `PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := Q.asIdeal))`. Rewrite using `[← e1]`. Both sides reduce to the same expression. Generalize the expression as in `(Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (IsLocalRing.closedPoint R) = q at this e`.

Substitute `e` using the available equality. Conclude with `this`.
-/
theorem chart_pt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {κ : Type} (x : κ → Ω) (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    {B : Type} [CommRing B] [IsDomain B] (i : B →+* Ω) (hi : Function.Injective i)
    (hx : ∀ c', x c' / x c ∈ i.range) (z : Spec (CommRingCat.of B) ⟶ X)
    (hz : Spec.map (CommRingCat.ofHom i) ≫ z = ξ) (P : Spec (CommRingCat.of B)) :
    ∃ h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ z P, InChart ξ x c ⟨_, h⟩ := by
  let Q : PrimeSpectrum B := P
  have hun : ∀ y : Q.asIdeal.primeCompl, IsUnit (i y) := by
    intro y
    refine isUnit_iff_ne_zero.2 fun h => y.2 ?_
    have : (y : B) = 0 := hi (by rw [h, map_zero])
    rw [this]; exact Q.asIdeal.zero_mem
  let R := Localization.AtPrime Q.asIdeal
  let φ : R →+* Ω := IsLocalization.lift hun
  have hφi : φ.comp (algebraMap B R) = i := IsLocalization.lift_comp hun
  have hφ : Function.Injective φ := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro h
      rw [← hφi]; exact congrArg φ h
    · intro h; rw [hi h]
  have hx' : ∀ c', x c' / x c ∈ φ.range := by
    intro c'
    obtain ⟨b, hb⟩ := hx c'
    exact ⟨algebraMap B R b, by rw [← hb, ← hφi]; rfl⟩
  have := chart_local ξ x T c hc φ hφ hx' (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφi, hz])
  have e : (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (IsLocalRing.closedPoint R) = z P := by
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap B R)) (IsLocalRing.closedPoint R) = P :=
      PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := Q.asIdeal))
    rw [← e1]; rfl
  generalize (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (IsLocalRing.closedPoint R) = q at this e
  subst e
  exact this

/- English proof (translation)
Rewrite using `[← cancel_mono Y.isoSpec.hom]`. Take `⟨f, hf⟩` from `Spec.map_surjective (l ≫ Y.isoSpec.hom)`. Take `⟨g, hg⟩` from `Spec.map_surjective (l' ≫ Y.isoSpec.hom)`. Establish `: f ≫ CommRingCat.ofHom i = g ≫ CommRingCat.ofHom i`. Apply `Spec.map_injective` to reduce the goal to its premises.

Rewrite using `[Spec.map_comp, Spec.map_comp, hf, hg, reassoc_of% h]`. Establish `hfg : f = g`. Use extensionality with `a`. Conclude with `hi (congrArg (fun t => CommRingCat.Hom.hom t a) this)`. Rewrite using `[← hf, ← hg, hfg]`.
-/
theorem eq_of_affine {Y : Scheme.{0}} [IsAffine Y] {Ω B : Type} [CommRing Ω] [CommRing B] (i : B →+* Ω)
    (hi : Function.Injective i) (l l' : Spec (CommRingCat.of B) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom i) ≫ l = Spec.map (CommRingCat.ofHom i) ≫ l') : l = l' := by
  rw [← cancel_mono Y.isoSpec.hom]
  obtain ⟨f, hf⟩ := Spec.map_surjective (l ≫ Y.isoSpec.hom)
  obtain ⟨g, hg⟩ := Spec.map_surjective (l' ≫ Y.isoSpec.hom)
  have : f ≫ CommRingCat.ofHom i = g ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hf, hg, reassoc_of% h]
  have hfg : f = g := by
    ext a
    exact hi (congrArg (fun t => CommRingCat.Hom.hom t a) this)
  rw [← hf, ← hg, hfg]

end PositivityTheory.Xgn.SameGenericPointCharts

open PositivityTheory.Xgn.SameGenericPointCharts in
/- English proof (translation)
Introduce `X Ω _ ξ κ x T c hc B _ _ _ hi hx z z' hz hz'`. Take `⟨U, hU, hmem⟩` from `T.affine c hc`. Establish `hr : ∀ w : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ w = ξ → Set.range w ⊆ Set.range U.ι`. Introduce and unpack `w hw _ ⟨P, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `(hmem _).2 (chart_pt ξ x T c hc _ hi hx w hw P)`. Use `haveI : IsAffine U := hU`. Use `eq_of_affine _ hi (IsOpenImmersion.lift U.ι z (hr z hz)) (IsOpenImmersion.lift U.ι z' (hr z' hz')) (by` as an intermediate fact. Rewrite using `[← cancel_mono U.ι, Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, hz, hz'])`. Rewrite using `[← IsOpenImmersion.lift_fac U.ι z (hr z hz), this, IsOpenImmersion.lift_fac]`.
-/
theorem PositivityTheory.Xgn.same_generic_point_charts : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B Ω], Function.Injective (algebraMap B Ω) → (∀ c', x c' / x c ∈ (algebraMap B Ω).range) → ∀ z z' : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z = ξ → Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z' = ξ → z = z' := by
  intro X Ω _ ξ κ x T c hc B _ _ _ hi hx z z' hz hz'
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hr : ∀ w : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ w = ξ →
      Set.range w ⊆ Set.range U.ι := by
    rintro w hw _ ⟨P, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hmem _).2 (chart_pt ξ x T c hc _ hi hx w hw P)
  haveI : IsAffine U := hU
  have := eq_of_affine _ hi (IsOpenImmersion.lift U.ι z (hr z hz)) (IsOpenImmersion.lift U.ι z' (hr z' hz')) (by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac,
      hz, hz'])
  rw [← IsOpenImmersion.lift_fac U.ι z (hr z hz), this, IsOpenImmersion.lift_fac]
