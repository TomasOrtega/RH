import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `k K _ _ _ _ _ C _ x hx c hc`. Take `⟨hC, hg, hstr⟩` from `hx`. Use `haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2`. Use `haveI := hC.1`. Use `haveI : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _`.

Use `haveI : GlobalTheory.IsNormalScheme C := isNormalScheme_of_smooth (strHom k C)`. Use `haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)`. Use `haveI := hg.2`. Use `set p : Sp K := IsLocalRing.closedPoint K with hp`. Establish `hη : x p = genericPoint C`.

Establish `hd : Dense (Set.range x)` using `hg.1.denseRange`. Establish `hr : Set.range x = {x p}`. Use extensionality with `y`. Conclude with `⟨by rintro ⟨q, rfl⟩; rw [Subsingleton.elim q p]; rfl, by rintro rfl; exact ⟨p, rfl⟩⟩`. Rewrite `hd` using `[hr]`.

Conclude with `(IsGenericPoint.eq (isGenericPoint_def.2 hd.closure_eq) (genericPoint_spec C))`. Establish `hco : Order.coheight c = 1`. Establish `hne : Order.coheight c ≠ 0`. Introduce `h0`. Establish `hm : IsMax c` using `Order.coheight_eq_zero.1 h0`.

Establish `h3 : genericPoint C ⤳ c` using `genericPoint_specializes c`. Apply `hc` to reduce the goal to its premises. Rewrite using `[hη]`. Conclude with `((show c ⤳ genericPoint C from hm (show c ≤ genericPoint C from h3)).antisymm h3).eq`. Establish `hle : (Order.coheight c : WithBot ℕ∞) ≤ 1` using `by haveI : Nonempty C := ⟨c⟩`.

Establish `hd` using `GlobalTheory.LieSemineg.dim_curve (k := k) (C := C) hC.1`. Establish `h1` using `(Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge`. Rewrite `hd` using `[topologicalKrullDim]`. Rewrite `h1` using `[hd]`. Conclude with `h1`.

Establish `hle' : Order.coheight c ≤ 1` using `by exact_mod_cast hle`. Conclude with `le_antisymm hle' (ENat.one_le_iff_ne_zero.2 hne)`. Use `haveI hdvr := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hco`. Use `set A := C.presheaf.stalk c`. Set `P : IsDedekindDomain.HeightOneSpectrum A` to `IsDiscreteValuationRing.maximalIdeal A`.

Set `ic` to `C.presheaf.stalkCongr (Inseparable.of_eq hη.symm)`. Set `ψ : C.functionField →+* K` to `(ic.hom ≫ Scheme.stalkClosedPointTo x).hom`. Establish `hψ : Function.Bijective ψ`. Use `⟨RingHom.injective ψ, ?_⟩` and prove the remaining obligations. Establish `h1 : Function.Surjective ic.hom.hom` using `((ConcreteCategory.isIso_iff_bijective ic.hom).1 inferInstance).2`.

Establish `h2 : Function.Surjective (Scheme.stalkClosedPointTo x).hom`. Establish `h3` using `x.stalkMap_surjective p`. Establish `h4 : Function.Surjective (stalkClosedPointIso (CommRingCat.of K)).hom.hom` using `((ConcreteCategory.isIso_iff_bijective (stalkClosedPointIso (CommRingCat.of K)).hom).1 inferInstance).2`. Conclude with `h4.comp h3`. Conclude with `h2.comp h1`.

Set `e : C.functionField ≃+* K` to `RingEquiv.ofBijective ψ hψ`. Set `φ : A →+* K` to `ψ.comp (algebraMap A C.functionField)`. Establish `hφ : spMap φ ≫ C.fromSpecStalk c = x`. Establish `h1 : φ = (C.presheaf.stalkSpecializes (hη ▸ genericPoint_specializes c : x p ⤳ c) ≫ Scheme.stalkClosedPointTo x).hom` using `by show ψ.comp (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom = _`. Express the relevant statement in the definitionally equal form `(C.presheaf.stalkSpecializes _ ≫ ic.hom ≫ Scheme.stalkClosedPointTo x).hom = _`.

Rewrite using `[TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]`. Use `erw [TopCat.Presheaf.stalkSpecializes_comp]`. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom _) ≫ _ = x`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`.

Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk x`. Establish `hval : ∀ a : A, (P.valuation C.functionField) (e.symm (φ a)) = P.intValuation a`. Introduce `a`. Establish `: e.symm (φ a) = algebraMap A C.functionField a` using `e.symm_apply_apply _`. Rewrite using `[this]`.

Conclude with `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P a`. Establish `hk : ∀ t : k, algebraMap k K t = φ (C.presheaf.germ ⊤ c trivial (algebraMap k Γ(C, ⊤) t))`. Establish `h1 : x ≫ strHom k C = spMap ((φ.comp (C.presheaf.germ ⊤ c trivial).hom).comp (algebraMap k Γ(C, ⊤)))`. Rewrite using `[← hφ, Category.assoc, strHom, ← Category.assoc (C.fromSpecStalk c), Scheme.fromSpecStalk_toSpecΓ]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]`.

Establish `h2` using `Spec.map_injective (hstr.symm.trans h1)`. Introduce `t`. Conclude with `congrArg (fun f => f.hom t) h2`. Set `vK : Valuation K (WithZero (Multiplicative ℤ))` to `(P.valuation C.functionField).comap e.symm.toRingHom`. Establish `hvφ : ∀ a, vK (φ a) = P.intValuation a` using `fun a => hval a`.

Establish `hunit : ∀ a : A, IsUnit a → P.intValuation a = 1`. Introduce `a ha`. Use `le_antisymm (P.intValuation_le_one a) (not_lt.1 fun h => ?_)` and prove the remaining obligations. Conclude with `P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((P.intValuation_lt_one_iff_mem a).1 h) ha)`. Set `v : Place k K` to `⟨vK, fun g => by`.

Take `⟨y, hy⟩` from `P.valuation_surjective C.functionField g`. Conclude with `⟨e y, by`. Express the relevant statement in the definitionally equal form `P.valuation C.functionField (e.symm (e y)) = g`. Rewrite using `[e.symm_apply_apply]`. Conclude with `hy⟩,`.

Use `fun t ht => by`. Rewrite using `[hk, hvφ]`. Conclude with `hunit _ (((Ne.isUnit ht).map (algebraMap k Γ(C, ⊤))).map _)⟩`. Establish `hle : ∀ a : A, φ a ∈ v.O` using `fun a => by show vK (φ a) ≤ 1`. Rewrite using `[hvφ]`.

Conclude with `P.intValuation_le_one a`. Set `ψO : A →+* v.O` to `φ.codRestrict v.O hle`. Establish `hPm : P.asIdeal = IsLocalRing.maximalIdeal A` using `rfl`. Use `haveI : IsLocalHom ψO := ⟨fun a ha => by`. Assume the negation of the conclusion as `hna`.

Establish `hm : a ∈ P.asIdeal` using `by rw [hPm]; exact hna`. Establish `hlt : vK (φ a) < 1` using `by rw [hvφ]; exact (P.intValuation_lt_one_iff_mem a).2 hm`. Take `⟨u, hu⟩` from `ha`. Set `w : v.O` to `((u⁻¹ : v.Oˣ) : v.O)`. Establish `hinv : vK (w : K) ≤ 1` using `w.2`.

Establish `h1 : φ a * (w : K) = 1`. Use `congrArg (fun z : v.O => (z : K)) u.mul_inv` as an intermediate fact. Establish `e1 : φ a = ((u : v.O) : K)` using `by rw [hu]; rfl`. Rewrite using `[e1]`. Conclude with `this`.

Establish `h2` using `congrArg vK h1`. Rewrite `h2` using `[map_mul, map_one]`. Establish `: vK (φ a) * vK (w : K) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' hinv) hlt`. Conclude with `absurd h2 this.ne⟩`. Use `⟨v, spMap ψO ≫ C.fromSpecStalk c, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, ← hφ]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `: spMap ψO (IsLocalRing.closedPoint v.O) = IsLocalRing.closedPoint A` using `IsLocalRing.comap_closedPoint ψO`. Express the relevant statement in the definitionally equal form `C.fromSpecStalk c (spMap ψO (IsLocalRing.closedPoint v.O)) = c`. Rewrite using `[this, Scheme.fromSpecStalk_closedPoint]`.
-/
theorem centre_place : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
    ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  intro k K _ _ _ _ _ C _ x hx c hc
  obtain ⟨hC, hg, hstr⟩ := hx
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  haveI := hC.1
  haveI : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  haveI : GlobalTheory.IsNormalScheme C := isNormalScheme_of_smooth (strHom k C)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  haveI := hg.2
  set p : Sp K := IsLocalRing.closedPoint K with hp
  have hη : x p = genericPoint C := by
    have hd : Dense (Set.range x) := hg.1.denseRange
    have hr : Set.range x = {x p} := by
      ext y
      exact ⟨by rintro ⟨q, rfl⟩; rw [Subsingleton.elim q p]; rfl, by rintro rfl; exact ⟨p, rfl⟩⟩
    rw [hr] at hd
    exact (IsGenericPoint.eq (isGenericPoint_def.2 hd.closure_eq) (genericPoint_spec C))
  have hco : Order.coheight c = 1 := by
    have hne : Order.coheight c ≠ 0 := by
      intro h0
      have hm : IsMax c := Order.coheight_eq_zero.1 h0
      have h3 : genericPoint C ⤳ c := genericPoint_specializes c
      apply hc
      rw [hη]
      exact ((show c ⤳ genericPoint C from hm (show c ≤ genericPoint C from h3)).antisymm h3).eq
    have hle : (Order.coheight c : WithBot ℕ∞) ≤ 1 := by
      haveI : Nonempty C := ⟨c⟩
      have hd := GlobalTheory.LieSemineg.dim_curve (k := k) (C := C) hC.1
      have h1 := (Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge
      rw [topologicalKrullDim] at hd
      rw [hd] at h1
      exact h1
    have hle' : Order.coheight c ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (ENat.one_le_iff_ne_zero.2 hne)
  haveI hdvr := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hco

  set A := C.presheaf.stalk c
  let P : IsDedekindDomain.HeightOneSpectrum A := IsDiscreteValuationRing.maximalIdeal A
  let ic := C.presheaf.stalkCongr (Inseparable.of_eq hη.symm)
  let ψ : C.functionField →+* K := (ic.hom ≫ Scheme.stalkClosedPointTo x).hom
  have hψ : Function.Bijective ψ := by
    refine ⟨RingHom.injective ψ, ?_⟩
    have h1 : Function.Surjective ic.hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective ic.hom).1 inferInstance).2
    have h2 : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
      have h3 := x.stalkMap_surjective p
      have h4 : Function.Surjective (stalkClosedPointIso (CommRingCat.of K)).hom.hom :=
        ((ConcreteCategory.isIso_iff_bijective (stalkClosedPointIso (CommRingCat.of K)).hom).1 inferInstance).2
      exact h4.comp h3
    exact h2.comp h1
  let e : C.functionField ≃+* K := RingEquiv.ofBijective ψ hψ
  let φ : A →+* K := ψ.comp (algebraMap A C.functionField)
  have hφ : spMap φ ≫ C.fromSpecStalk c = x := by
    have h1 : φ = (C.presheaf.stalkSpecializes (hη ▸ genericPoint_specializes c : x p ⤳ c) ≫ Scheme.stalkClosedPointTo x).hom := by
      show ψ.comp (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom = _
      change (C.presheaf.stalkSpecializes _ ≫ ic.hom ≫ Scheme.stalkClosedPointTo x).hom = _
      rw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
      erw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [h1]
    change Spec.map (CommRingCat.ofHom _) ≫ _ = x
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have hval : ∀ a : A, (P.valuation C.functionField) (e.symm (φ a)) = P.intValuation a := by
    intro a
    have : e.symm (φ a) = algebraMap A C.functionField a := e.symm_apply_apply _
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P a

  have hk : ∀ t : k, algebraMap k K t = φ (C.presheaf.germ ⊤ c trivial (algebraMap k Γ(C, ⊤) t)) := by
    have h1 : x ≫ strHom k C = spMap ((φ.comp (C.presheaf.germ ⊤ c trivial).hom).comp (algebraMap k Γ(C, ⊤))) := by
      rw [← hφ, Category.assoc, strHom, ← Category.assoc (C.fromSpecStalk c), Scheme.fromSpecStalk_toSpecΓ]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    have h2 := Spec.map_injective (hstr.symm.trans h1)
    intro t
    exact congrArg (fun f => f.hom t) h2
  let vK : Valuation K (WithZero (Multiplicative ℤ)) := (P.valuation C.functionField).comap e.symm.toRingHom
  have hvφ : ∀ a, vK (φ a) = P.intValuation a := fun a => hval a
  have hunit : ∀ a : A, IsUnit a → P.intValuation a = 1 := by
    intro a ha
    refine le_antisymm (P.intValuation_le_one a) (not_lt.1 fun h => ?_)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((P.intValuation_lt_one_iff_mem a).1 h) ha)
  let v : Place k K := ⟨vK, fun g => by
      obtain ⟨y, hy⟩ := P.valuation_surjective C.functionField g
      exact ⟨e y, by
        change P.valuation C.functionField (e.symm (e y)) = g
        rw [e.symm_apply_apply]; exact hy⟩,
    fun t ht => by
      rw [hk, hvφ]
      exact hunit _ (((Ne.isUnit ht).map (algebraMap k Γ(C, ⊤))).map _)⟩
  have hle : ∀ a : A, φ a ∈ v.O := fun a => by
    show vK (φ a) ≤ 1
    rw [hvφ]; exact P.intValuation_le_one a
  let ψO : A →+* v.O := φ.codRestrict v.O hle
  have hPm : P.asIdeal = IsLocalRing.maximalIdeal A := rfl
  haveI : IsLocalHom ψO := ⟨fun a ha => by
    by_contra hna
    have hm : a ∈ P.asIdeal := by rw [hPm]; exact hna
    have hlt : vK (φ a) < 1 := by rw [hvφ]; exact (P.intValuation_lt_one_iff_mem a).2 hm
    obtain ⟨u, hu⟩ := ha
    let w : v.O := ((u⁻¹ : v.Oˣ) : v.O)
    have hinv : vK (w : K) ≤ 1 := w.2
    have h1 : φ a * (w : K) = 1 := by
      have := congrArg (fun z : v.O => (z : K)) u.mul_inv
      have e1 : φ a = ((u : v.O) : K) := by rw [hu]; rfl
      rw [e1]
      exact this
    have h2 := congrArg vK h1
    rw [map_mul, map_one] at h2
    have : vK (φ a) * vK (w : K) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' hinv) hlt
    exact absurd h2 this.ne⟩
  refine ⟨v, spMap ψO ≫ C.fromSpecStalk c, ?_, ?_⟩
  · rw [← Category.assoc, ← hφ]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · have : spMap ψO (IsLocalRing.closedPoint v.O) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint ψO
    change C.fromSpecStalk c (spMap ψO (IsLocalRing.closedPoint v.O)) = c
    rw [this, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.Nef
