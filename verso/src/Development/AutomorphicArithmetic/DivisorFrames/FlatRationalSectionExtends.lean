import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

/- English proof (translation)
Establish `h (s : S) : ψ s ∈ (ψ.comp φ).range`. Distinguish the cases in `h0 : ψ s = 0`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Break down `hv (ψ s) with h | ⟨a, ha⟩` into its components or cases.

Conclude with `h`. Establish `ha' : ψ (φ a) = (ψ s)⁻¹` using `ha`. Establish `hu : IsUnit (s * φ a)`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self (s * φ a) with h | h` into its components or cases. Conclude with `h`.

Use `h.map ψ` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, map_mul, ha', mul_inv_cancel₀ h0, sub_self]`. Conclude with `absurd this not_isUnit_zero`. Take `⟨u, rfl⟩ : IsUnit a` from `IsLocalHom.map_nonunit (f := φ) a (isUnit_of_mul_isUnit_right hu)`. Use `⟨(u⁻¹ : Rˣ), ?_⟩` and prove the remaining obligations.

Rewrite using `[← inv_inv (ψ s), ← ha]`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Use `choose r hr using h`. Establish `hr' (s : S) : ψ (φ (r s)) = ψ s` using `hr s`.

Use `⟨⟨⟨⟨r, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, RingHom.ext fun a => hi ?_, fun s hs => ?_⟩` and prove the remaining obligations. Simplify using `[hr']`. Simplify using `[hr']`. Simplify using `[hr']`. Simplify using `[hr']`.

Conclude with `hr' _`. Use `(show IsUnit (s - φ (r s)) from hs).map ψ` as an intermediate fact. Rewrite `this` using `[map_sub, hr', sub_self]`. Conclude with `not_isUnit_zero this`.
-/
private theorem exists_retr {R S K : Type} [CommRing R] [CommRing S] [Field K] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (ψ : S →+* K) (hi : Function.Injective (ψ.comp φ))
    (hv : ∀ t : K, t ∈ (ψ.comp φ).range ∨ t⁻¹ ∈ (ψ.comp φ).range) :
    ∃ r : S →+* R, r.comp φ = RingHom.id R ∧ ∀ s, ¬ IsUnit (s - φ (r s)) := by
  have h (s : S) : ψ s ∈ (ψ.comp φ).range := by
    by_cases h0 : ψ s = 0
    · rw [h0]; exact zero_mem _
    rcases hv (ψ s) with h | ⟨a, ha⟩
    · exact h
    have ha' : ψ (φ a) = (ψ s)⁻¹ := ha
    have hu : IsUnit (s * φ a) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (s * φ a) with h | h
      · exact h
      · have := h.map ψ
        rw [map_sub, map_one, map_mul, ha', mul_inv_cancel₀ h0, sub_self] at this
        exact absurd this not_isUnit_zero
    obtain ⟨u, rfl⟩ : IsUnit a := IsLocalHom.map_nonunit (f := φ) a (isUnit_of_mul_isUnit_right hu)
    refine ⟨(u⁻¹ : Rˣ), ?_⟩
    rw [← inv_inv (ψ s), ← ha]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  choose r hr using h
  have hr' (s : S) : ψ (φ (r s)) = ψ s := hr s
  refine ⟨⟨⟨⟨r, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, RingHom.ext fun a => hi ?_, fun s hs => ?_⟩
  · simp [hr']
  · simp [hr']
  · simp [hr']
  · simp [hr']
  · exact hr' _
  · have := (show IsUnit (s - φ (r s)) from hs).map ψ
    rw [map_sub, hr', sub_self] at this
    exact not_isUnit_zero this

/- English proof (translation)
Establish `: Smooth (strHom k C)` using `have := h.1`. Use the proof step `SmoothOfRelativeDimension.smooth 1 _`. Establish `hn` using `(GlobalTheory.isNormalScheme_iff C).1 (GlobalTheory.isNormalScheme_of_smooth (strHom k C))`. Establish `: IsLocallyNoetherian C` using `LocallyOfFiniteType.isLocallyNoetherian (strHom k C)`. Establish `hd : ringKrullDim (C.presheaf.stalk c) ≤ 1`.

Rewrite using `[← LieSemineg.dim_curve h.1, ringKrullDim_stalk_eq_coheight]`. Conclude with `(Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge`. Establish `h1 : Ring.KrullDimLE 1 (C.presheaf.stalk c)` using `Ring.krullDimLE_iff.2 (by exact_mod_cast hd)`. Establish `h3 : IsIntegrallyClosed (C.presheaf.stalk c) ∧ ∀ P : Ideal (C.presheaf.stalk c), P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _` using `⟨(hn c).2, fun P h₁ h₂ ↦ IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h₁ h₂)⟩`. Conclude with `((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (C.presheaf.stalk c)).out 1 3).mpr h3`.
-/
private theorem valuationRing_stalk {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (h : IsCurve k C)
    [IsIntegral C] (c : C) : ValuationRing (C.presheaf.stalk c) := by
  have : Smooth (strHom k C) := have := h.1; SmoothOfRelativeDimension.smooth 1 _
  have hn := (GlobalTheory.isNormalScheme_iff C).1 (GlobalTheory.isNormalScheme_of_smooth (strHom k C))
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  have hd : ringKrullDim (C.presheaf.stalk c) ≤ 1 := by
    rw [← LieSemineg.dim_curve h.1, ringKrullDim_stalk_eq_coheight]
    exact (Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge
  have h1 : Ring.KrullDimLE 1 (C.presheaf.stalk c) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have h3 : IsIntegrallyClosed (C.presheaf.stalk c) ∧
      ∀ P : Ideal (C.presheaf.stalk c), P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _ :=
    ⟨(hn c).2, fun P h₁ h₂ ↦ IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h₁ h₂)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (C.presheaf.stalk c)).out 1 3).mpr h3

/- English proof (translation)
Substitute `hξ` using the available equality. Set `e' : C.functionField →+* K` to `e`. Use `⟨e'.injective.comp (IsFractionRing.injective (C.presheaf.stalk c) C.functionField), fun t => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `(show Function.Surjective e' from he) t`. Break down `ValuationRing.isInteger_or_isInteger (C.presheaf.stalk c) t with ⟨a, ha⟩ | ⟨a, ha⟩` into its components or cases.

Conclude with `Or.inl ⟨a, congrArg e' ha⟩`. Conclude with `Or.inr ⟨a, (congrArg e' ha).trans (map_inv₀ e' t)⟩`.
-/
private theorem val_specializes {C : Scheme.{0}} [IsIntegral C] {c ξ : C} [ValuationRing (C.presheaf.stalk c)]
    (hξ : ξ = genericPoint C) (hs : ξ ⤳ c) {K : Type} [Field K] (e : C.presheaf.stalk ξ →+* K)
    (he : Function.Surjective e) :
    Function.Injective (e.comp (C.presheaf.stalkSpecializes hs).hom) ∧
      ∀ t : K, t ∈ (e.comp (C.presheaf.stalkSpecializes hs).hom).range ∨
        t⁻¹ ∈ (e.comp (C.presheaf.stalkSpecializes hs).hom).range := by
  subst hξ
  let e' : C.functionField →+* K := e
  refine ⟨e'.injective.comp (IsFractionRing.injective (C.presheaf.stalk c) C.functionField), fun t => ?_⟩
  obtain ⟨t, rfl⟩ := (show Function.Surjective e' from he) t
  rcases ValuationRing.isInteger_or_isInteger (C.presheaf.stalk c) t with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact Or.inl ⟨a, congrArg e' ha⟩
  · exact Or.inr ⟨a, (congrArg e' ha).trans (map_inv₀ e' t)⟩

/- English proof (translation)
Introduce `k _ _ C _ hC K _ x hx Z hfl hft hrat Ω _ p g`. Use `LieSemineg.isIntegral_curve hC.1 hC.2.2` as an intermediate fact. Use `hx.1` as an intermediate fact. Use `hx.2` as an intermediate fact. Set `g' : Spec (.of Ω) ⟶ Z.left` to `g.left`.

Establish `hg' : g' ≫ Z.hom = p` using `Over.w g`. Set `z : Z.left` to `g' (IsLocalRing.closedPoint Ω)`. Set `c : C` to `Z.hom z`. Use `valuationRing_stalk hC c` as an intermediate fact. Establish `hg : x (IsLocalRing.closedPoint K) = genericPoint C`.

Rewrite using `[Subsingleton.elim (α := Sp K) (IsLocalRing.closedPoint K) (genericPoint (Sp K))]`. Use `((genericPoint_spec (Sp K)).image x.continuous).eq ?_` and prove the remaining obligations. Rewrite using `[Set.image_univ, x.denseRange.closure_range]`. Conclude with `genericPoint_spec C`. Take `⟨ζ, hζ, hζ'⟩` from `Flat.generalizingMap Z.hom (genericPoint_specializes c)`.

Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := Z.hom) (g := x) ζ (IsLocalRing.closedPoint K) (hζ'.trans hg.symm)`. Take `⟨y₁, hy₁, hy₂⟩` from `hrat ((pullback Z.hom x).residueField w) (Spec.preimage ((pullback Z.hom x).fromSpecResidueField w ≫ pullback.snd Z.hom x)).hom ((pullback Z.hom x).fromSpecResidueField w ≫ pullback.fst Z.hom x) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Conclude with `congrArg (· ≫ x) (Spec.map_preimage _).symm)`. Establish `hy₃ : y₁ (IsLocalRing.closedPoint K) = ζ`.

Use `congrArg (fun f => f (IsLocalRing.closedPoint _)) hy₂` as an intermediate fact. Use `Eq.trans ?_ (this.trans ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg (pullback.fst Z.hom x) (Scheme.fromSpecResidueField_apply _ _)).trans hw)))` and prove the remaining obligations. Conclude with `(congrArg y₁ (Subsingleton.elim (α := Sp K) _ _)).trans (Scheme.Hom.comp_apply _ _ _).symm`. Establish `hs : y₁ (IsLocalRing.closedPoint K) ⤳ z` using `hy₃ ▸ hζ`. Establish `hs' : x (IsLocalRing.closedPoint K) ⤳ c` using `hg ▸ genericPoint_specializes c`.

Set `φ` to `Z.hom.stalkMap z`. Set `ψ` to `Z.left.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of K) y₁`. Establish `hφψ : φ ≫ ψ = C.presheaf.stalkSpecializes hs' ≫ Scheme.stalkClosedPointTo (R` using `.of K) x := by`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono (C.fromSpecStalk c)]`.

Simplify using `only [φ, ψ, c, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]`. Conclude with `(Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc (R := .of K) y₁ _).trans (hy₁.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) x).symm)`. Establish `hsurj : Function.Surjective (Scheme.stalkClosedPointTo (R` using `.of K) x).hom := (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.surjective.comp (x.stalkMap_surjective _)`. Establish `hv` using `val_specializes hg hs' _ hsurj`. Establish `e : (Scheme.stalkClosedPointTo (R` using `.of K) x).hom.comp (C.presheaf.stalkSpecializes hs').hom = ψ.hom.comp φ.hom := (congrArg CommRingCat.Hom.hom hφψ).symm`.

Rewrite `hv` using `[e]`. Take `⟨r, hr₁, hr₂⟩` from `exists_retr φ.hom ψ.hom hv.1 hv.2`. Set `r' : Z.left.presheaf.stalk z ⟶ C.presheaf.stalk c` to `CommRingCat.ofHom r`. Establish `hr : φ ≫ r' = 𝟙 _` using `CommRingCat.hom_ext hr₁`. Take `⟨U, hcU, σ, hσ₁, hσ₂⟩` from `spread_out_of_isGermInjective' (𝟙 C) Z.hom (x := c) (Spec.map r' ≫ Z.left.fromSpecStalk z) (by`.

Rewrite using `[Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]`. Use `erw [hr]`. Simplify using `[c])`. Set `δ` to `Scheme.stalkClosedPointTo g'`. Establish `hδ : Spec.map δ ≫ Z.left.fromSpecStalk z = g'` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk g'`.

Establish `hδ' : r' ≫ φ ≫ δ = δ`. Use extensionality with `s`. Establish `h0 : δ.hom (s - φ.hom (r s)) = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hr₂ s (IsLocalHom.map_nonunit (f := δ.hom) _ (Ne.isUnit h0))`.

Rewrite `h0` using `[map_sub, sub_eq_zero]`. Conclude with `h0.symm`. Establish `key : (Spec.map (φ ≫ δ) ≫ U.fromSpecStalkOfMem c hcU) ≫ σ = g'`. Rewrite using `[Category.assoc, ← hσ₁, ← Spec.map_comp_assoc, hδ', hδ]`. Rewrite `hσ₂` using `[Category.comp_id]`.

Use `⟨U, Over.homMk σ hσ₂, Over.homMk (Spec.map (φ ≫ δ) ≫ U.fromSpecStalkOfMem c hcU) ?_, Over.OverMorphism.ext key⟩` and prove the remaining obligations. Use `show _ ≫ U.ι = p`. Rewrite using `[← hσ₂, ← Category.assoc, key, hg']`.
-/
theorem UpperTheory.flat_rational_section_extends :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
        ∀ Z : Over C, Flat Z.hom → LocallyOfFiniteType Z.hom → RatOver Z x →
        ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ C) (g : Over.mk p ⟶ Z),
        ∃ (U : C.Opens) (σ : Over.mk U.ι ⟶ Z) (p' : Over.mk p ⟶ Over.mk U.ι), p' ≫ σ = g := by
  intro k _ _ C _ hC K _ x hx Z hfl hft hrat Ω _ p g
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have := hx.1
  have := hx.2
  let g' : Spec (.of Ω) ⟶ Z.left := g.left
  have hg' : g' ≫ Z.hom = p := Over.w g
  let z : Z.left := g' (IsLocalRing.closedPoint Ω)
  let c : C := Z.hom z
  have := valuationRing_stalk hC c
  have hg : x (IsLocalRing.closedPoint K) = genericPoint C := by
    rw [Subsingleton.elim (α := Sp K) (IsLocalRing.closedPoint K) (genericPoint (Sp K))]
    refine ((genericPoint_spec (Sp K)).image x.continuous).eq ?_
    rw [Set.image_univ, x.denseRange.closure_range]
    exact genericPoint_spec C
  obtain ⟨ζ, hζ, hζ'⟩ := Flat.generalizingMap Z.hom (genericPoint_specializes c)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Z.hom) (g := x) ζ
    (IsLocalRing.closedPoint K) (hζ'.trans hg.symm)
  obtain ⟨y₁, hy₁, hy₂⟩ := hrat ((pullback Z.hom x).residueField w)
    (Spec.preimage ((pullback Z.hom x).fromSpecResidueField w ≫ pullback.snd Z.hom x)).hom
    ((pullback Z.hom x).fromSpecResidueField w ≫ pullback.fst Z.hom x) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ x) (Spec.map_preimage _).symm)
  have hy₃ : y₁ (IsLocalRing.closedPoint K) = ζ := by
    have := congrArg (fun f => f (IsLocalRing.closedPoint _)) hy₂
    refine Eq.trans ?_ (this.trans ((Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (pullback.fst Z.hom x) (Scheme.fromSpecResidueField_apply _ _)).trans hw)))
    exact (congrArg y₁ (Subsingleton.elim (α := Sp K) _ _)).trans (Scheme.Hom.comp_apply _ _ _).symm
  have hs : y₁ (IsLocalRing.closedPoint K) ⤳ z := hy₃ ▸ hζ
  have hs' : x (IsLocalRing.closedPoint K) ⤳ c := hg ▸ genericPoint_specializes c
  let φ := Z.hom.stalkMap z
  let ψ := Z.left.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of K) y₁
  have hφψ : φ ≫ ψ = C.presheaf.stalkSpecializes hs' ≫ Scheme.stalkClosedPointTo (R := .of K) x := by
    apply Spec.map_injective
    rw [← cancel_mono (C.fromSpecStalk c)]
    simp only [φ, ψ, c, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc (R := .of K) y₁ _).trans
      (hy₁.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) x).symm)
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo (R := .of K) x).hom :=
    (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.surjective.comp (x.stalkMap_surjective _)
  have hv := val_specializes hg hs' _ hsurj
  have e : (Scheme.stalkClosedPointTo (R := .of K) x).hom.comp (C.presheaf.stalkSpecializes hs').hom =
      ψ.hom.comp φ.hom := (congrArg CommRingCat.Hom.hom hφψ).symm
  rw [e] at hv
  obtain ⟨r, hr₁, hr₂⟩ := exists_retr φ.hom ψ.hom hv.1 hv.2
  let r' : Z.left.presheaf.stalk z ⟶ C.presheaf.stalk c := CommRingCat.ofHom r
  have hr : φ ≫ r' = 𝟙 _ := CommRingCat.hom_ext hr₁
  obtain ⟨U, hcU, σ, hσ₁, hσ₂⟩ := spread_out_of_isGermInjective' (𝟙 C) Z.hom (x := c)
    (Spec.map r' ≫ Z.left.fromSpecStalk z) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
      erw [hr]
      simp [c])
  let δ := Scheme.stalkClosedPointTo g'
  have hδ : Spec.map δ ≫ Z.left.fromSpecStalk z = g' := Scheme.Spec_stalkClosedPointTo_fromSpecStalk g'
  have hδ' : r' ≫ φ ≫ δ = δ := by
    ext s
    have h0 : δ.hom (s - φ.hom (r s)) = 0 := by
      by_contra h0
      exact hr₂ s (IsLocalHom.map_nonunit (f := δ.hom) _ (Ne.isUnit h0))
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm
  have key : (Spec.map (φ ≫ δ) ≫ U.fromSpecStalkOfMem c hcU) ≫ σ = g' := by
    rw [Category.assoc, ← hσ₁, ← Spec.map_comp_assoc, hδ', hδ]
  rw [Category.comp_id] at hσ₂
  refine ⟨U, Over.homMk σ hσ₂, Over.homMk (Spec.map (φ ≫ δ) ≫ U.fromSpecStalkOfMem c hcU) ?_,
    Over.OverMorphism.ext key⟩
  show _ ≫ U.ι = p
  rw [← hσ₂, ← Category.assoc, key, hg']
