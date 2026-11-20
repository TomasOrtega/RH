import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGeneric

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

/- English proof (translation)
Establish `e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ)` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2`. Establish `e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ`. Establish `e2 : spMap (genMap ξ q) = Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2)`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[e2, Category.assoc]`. Conclude with `(congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4`.
-/
theorem genMap_fromSpec {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) :
    spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 = ξ := by
  have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
  have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 : spMap (genMap ξ q) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
    rw [← Spec.map_comp]
    rfl
  rw [e2, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4

/- English proof (translation)
Take `⟨p, hp⟩` from `q`. Substitute `e` using the available equality. Establish `: X.presheaf.stalkSpecializes hp = 𝟙 _` using `X.presheaf.stalkSpecializes_refl _`. Unfold `genMap`. Simplify using `only [this]`.

Conclude with `h.bij`.
-/
theorem genMap_bij {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (h : IsCptGen ξ) (q : Cpt ξ) (e : q.1 = genPt ξ) :
    Function.Bijective (genMap ξ q) := by
  obtain ⟨p, hp⟩ := q
  subst e
  have : X.presheaf.stalkSpecializes hp = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  simp only [this]
  exact h.bij

/- English proof (translation)
Introduce `X Ω Ω' _ _ ξ ξ' h h' e`. Set `q : Cpt ξ` to `⟨genPt ξ, specializes_rfl⟩`. Set `q' : Cpt ξ'` to `⟨genPt ξ, e ▸ specializes_rfl⟩`. Set `a` to `RingEquiv.ofBijective _ (genMap_bij h q rfl)`. Set `a'` to `RingEquiv.ofBijective _ (genMap_bij h' q' e)`.

Use `⟨a'.symm.trans a, ?_⟩` and prove the remaining obligations. Establish `hc : (a'.symm.trans a).toRingHom.comp (genMap ξ' q') = genMap ξ q`. Use extensionality with `x`. Use `show a (a'.symm (a' x)) = a x`. Rewrite using `[a'.symm_apply_apply]`.

Establish `h1` using `genMap_fromSpec ξ q`. Establish `h2` using `genMap_fromSpec ξ' q'`. Rewrite `h1` using `[← hc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, ← Spec.map_comp]`.

Both sides reduce to the same expression. Use `_ = _ := by rw [h2]`.
-/
theorem genIso : GenIso := by
  intro X Ω Ω' _ _ ξ ξ' h h' e
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  let q' : Cpt ξ' := ⟨genPt ξ, e ▸ specializes_rfl⟩
  let a := RingEquiv.ofBijective _ (genMap_bij h q rfl)
  let a' := RingEquiv.ofBijective _ (genMap_bij h' q' e)
  refine ⟨a'.symm.trans a, ?_⟩
  have hc : (a'.symm.trans a).toRingHom.comp (genMap ξ' q') = genMap ξ q := by
    ext x
    show a (a'.symm (a' x)) = a x
    rw [a'.symm_apply_apply]
  have h1 := genMap_fromSpec ξ q
  have h2 := genMap_fromSpec ξ' q'
  rw [← hc] at h1
  calc ξ = _ := h1.symm
    _ = spMap (a'.symm.trans a).toRingHom ≫ spMap (genMap ξ' q') ≫ X.fromSpecStalk q'.1 := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    _ = _ := by rw [h2]

/- English proof (translation)
Rewrite `h` using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun k' => y ⟨k', ch k'⟩) (Finset.mem_univ k), Function.update_self, Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')], mul_div_mul_right _ _ (right_ne_zero_of …`.
-/
theorem seg_ratio {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (ch : ∀ k, J k) (h : ∏ k, y ⟨k, ch k⟩ ≠ 0) (k : K) (j : J k) :
    (∏ k', y ⟨k', Function.update ch k j k'⟩) / ∏ k', y ⟨k', ch k'⟩ = y ⟨k, j⟩ / y ⟨k, ch k⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)] at h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun k' => y ⟨k', ch k'⟩) (Finset.mem_univ k),
    Function.update_self, Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')],
    mul_div_mul_right _ _ (right_ne_zero_of_mul h)]

/- English proof (translation)
Introduce `X Ω Ω₃ _ _ O i ξ q K _ J _ y ch a hD hc`. Unfold `vdeg`. Rewrite using `[map_prod, map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, map_zpow₀]`.

Use `congr 1`. Use `le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j => O.valuation (i (y ⟨k, j⟩))) (Finset.mem_univ _))` and prove the remaining obligations. Establish `h0 : y ⟨k, ch k⟩ ≠ 0` using `Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _)`. Establish `h1` using `hD.1 _ (hc.2 (Function.update ch k j))`. Rewrite `h1` using `[seg_ratio y ch hc.1, ← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using h0))]`.

Conclude with `h1`.
-/
theorem chartVal : ChartVal := by
  intro X Ω Ω₃ _ _ O i ξ q K _ J _ y ch a hD hc
  classical
  unfold vdeg
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow₀, map_zpow₀]
  congr 1
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j => O.valuation (i (y ⟨k, j⟩))) (Finset.mem_univ _))
  have h0 : y ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _)
  have h1 := hD.1 _ (hc.2 (Function.update ch k j))
  rw [seg_ratio y ch hc.1, ← O.valuation_le_one_iff, map_div₀, map_div₀,
    div_le_one₀ (zero_lt_iff.2 (by simpa using h0))] at h1
  exact h1

/- English proof (translation)
Set `q : Cpt ξ` to `⟨z (IsLocalRing.closedPoint O), ha _⟩`. Set `φ : X.presheaf.stalk q.1 →+* O` to `(Scheme.stalkClosedPointTo z).hom`. Establish `hl : IsLocalHom φ` using `inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)`. Establish `e1 : spMap φ ≫ X.fromSpecStalk q.1 = z` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk z`. Establish `e2 : spMap (O.subtype.comp φ) = spMap (i.comp (genMap ξ q))`.

Rewrite using `[← cancel_mono (X.fromSpecStalk q.1)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Use `_ = spMap i ≫ spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [e1, genMap_fromSpec, hz]`.

Use `_ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl`. Establish `e3 : ∀ s, ((φ s : O) : Ω₃) = i (genMap ξ q s)` using `fun s => congrArg (fun f => f.hom s) (Spec.map_injective e2)`. Use `⟨q, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[← e3]`.

Conclude with `(φ s).2`. Introduce and unpack `_ ⟨s, rfl⟩ h0 h1`. Establish `hu : IsUnit (φ s)` using `IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by show ((φ s : O) : Ω₃) * _ = 1`. Rewrite using `[e3, mul_inv_cancel₀ ((map_ne_zero i).2 h0)]))`. Take `⟨t, ht⟩` from `(hl.1 s hu).exists_right_inv`.

Use `⟨t, eq_inv_of_mul_eq_one_right ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ht, map_one]`.
-/
theorem dom_of_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) (ha : ∀ q : X, genPt ξ ⤳ q) (z : Sp O ⟶ X) (hz : spMap O.subtype ≫ z = spMap i ≫ ξ) :
    ∃ q : Cpt ξ, Dom O i ξ q := by
  let q : Cpt ξ := ⟨z (IsLocalRing.closedPoint O), ha _⟩
  let φ : X.presheaf.stalk q.1 →+* O := (Scheme.stalkClosedPointTo z).hom
  have hl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have e1 : spMap φ ≫ X.fromSpecStalk q.1 = z := Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have e2 : spMap (O.subtype.comp φ) = spMap (i.comp (genMap ξ q)) := by
    rw [← cancel_mono (X.fromSpecStalk q.1)]
    calc _ = spMap O.subtype ≫ spMap φ ≫ X.fromSpecStalk q.1 := by
          rw [← Category.assoc, ← Spec.map_comp]; rfl
      _ = spMap i ≫ spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [e1, genMap_fromSpec, hz]
      _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl
  have e3 : ∀ s, ((φ s : O) : Ω₃) = i (genMap ξ q s) := fun s =>
    congrArg (fun f => f.hom s) (Spec.map_injective e2)
  refine ⟨q, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← e3]
    exact (φ s).2
  · rintro _ ⟨s, rfl⟩ h0 h1
    have hu : IsUnit (φ s) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
      show ((φ s : O) : Ω₃) * _ = 1
      rw [e3, mul_inv_cancel₀ ((map_ne_zero i).2 h0)]))
    obtain ⟨t, ht⟩ := (hl.1 s hu).exists_right_inv
    refine ⟨t, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← map_mul, ht, map_one]

/- English proof (translation)
Take `⟨U, hU, hm⟩` from `ht.affine c hc`. Set `q : Cpt ξ` to `⟨genPt ξ, specializes_rfl⟩`. Establish `hq : q.1 ∈ U` using `(hm _).2 ⟨q.2, hc, fun c' => (genMap_bij ht.gen q rfl).2 _⟩`. Set `φ : Γ(X, U) →+* Ω` to `(genMap ξ q).comp (X.presheaf.germ U q.1 hq).hom`. Establish `h1 : ∀ s, i (φ s) ∈ O` using `fun s => by`.

Establish `: φ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)` using `(ht.ring c hc _).2 fun p hp => by`. Establish `hpU : p.1 ∈ U` using `(hm _).2 ⟨p.2, hp⟩`. Use `⟨X.presheaf.germ U p.1 hpU s, ?_⟩` and prove the remaining obligations. Use `show Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes p.2 _) = Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes q.2 _)`. Rewrite using `[TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]`.

Generalize the expression as in `φ s = a at this`. Proceed by induction on `this using Algebra.adjoin_induction with`. Consider the case `mem a h => obtain ⟨j, rfl⟩ := h`. Conclude with `hO j`. Consider the case `algebraMap n => simp`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`. Set `ψ : Γ(X, U) →+* O` to `(i.comp φ).codRestrict O.toSubring h1`.

Use `⟨spMap ψ ≫ hU.fromSpec, ?_⟩` and prove the remaining obligations. Establish `e : Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec = X.fromSpecStalk q.1` using `hU.fromSpecStalk_eq_fromSpecStalk hq`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.

Use `_ = _ := by rw [e, genMap_fromSpec]`.
-/
theorem exists_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {κ : Type} (x : κ → Ω) (ht : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (hO : ∀ j, i (x j / x c) ∈ O) :
    ∃ z : Sp O ⟶ X, spMap O.subtype ≫ z = spMap i ≫ ξ := by
  obtain ⟨U, hU, hm⟩ := ht.affine c hc
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hq : q.1 ∈ U := (hm _).2 ⟨q.2, hc, fun c' => (genMap_bij ht.gen q rfl).2 _⟩
  let φ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hq).hom
  have h1 : ∀ s, i (φ s) ∈ O := fun s => by
    have : φ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := (ht.ring c hc _).2 fun p hp => by
      have hpU : p.1 ∈ U := (hm _).2 ⟨p.2, hp⟩
      refine ⟨X.presheaf.germ U p.1 hpU s, ?_⟩
      show Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes p.2 _) =
        Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes q.2 _)
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
    generalize φ s = a at this
    induction this using Algebra.adjoin_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hO j
    | algebraMap n => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let ψ : Γ(X, U) →+* O := (i.comp φ).codRestrict O.toSubring h1
  refine ⟨spMap ψ ≫ hU.fromSpec, ?_⟩
  have e : Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec = X.fromSpecStalk q.1 := hU.fromSpecStalk_eq_fromSpecStalk hq
  calc _ = spMap i ≫ spMap (genMap ξ q) ≫ Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec := by
        simp only [← Category.assoc, ← Spec.map_comp]
        rfl
    _ = _ := by rw [e, genMap_fromSpec]

/- English proof (translation)
Take `⟨c₀, hc₀, -⟩` from `ht.cover ⟨genPt ξ, specializes_rfl⟩`. Establish `hm : ∀ k, ∃ j : J k, ∀ j', O.valuation (i (y ⟨k, j'⟩)) ≤ O.valuation (i (y ⟨k, j⟩))` using `fun k => by`. Take `⟨j, -, hj⟩` from `Finset.exists_max_image Finset.univ (fun j => O.valuation (i (y ⟨k, j⟩))) ⟨c₀ k, Finset.mem_univ _⟩`. Conclude with `⟨j, fun j' => hj j' (Finset.mem_univ _)⟩`. Use `choose ch hch using hm`.

Establish `hp : ∀ k, 0 < O.valuation (i (y ⟨k, ch k⟩))` using `fun k => lt_of_lt_of_le (zero_lt_iff.2 (by simpa using Finset.prod_ne_zero_iff.1 hc₀ k (Finset.mem_univ _))) (hch k (c₀ k))`. Establish `h0 : ∀ k, y ⟨k, ch k⟩ ≠ 0` using `fun k h => by simpa [h] using hp k`. Take `⟨z, hz⟩` from `exists_point O i ξ _ ht ch (Finset.prod_ne_zero_iff.2 fun k _ => h0 k) fun j => by`. Rewrite using `[← Finset.prod_div_distrib, map_prod]`. Use `prod_mem fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (hp k)]`. Conclude with `hch k (j k)`. Conclude with `dom_of_point O i ξ ha z hz`.
-/
theorem exists_dom {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ha : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) : ∃ q : Cpt ξ, Dom O i ξ q := by
  obtain ⟨c₀, hc₀, -⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
  have hm : ∀ k, ∃ j : J k, ∀ j', O.valuation (i (y ⟨k, j'⟩)) ≤ O.valuation (i (y ⟨k, j⟩)) := fun k => by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => O.valuation (i (y ⟨k, j⟩))) ⟨c₀ k, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose ch hch using hm
  have hp : ∀ k, 0 < O.valuation (i (y ⟨k, ch k⟩)) := fun k =>
    lt_of_lt_of_le (zero_lt_iff.2 (by simpa using Finset.prod_ne_zero_iff.1 hc₀ k (Finset.mem_univ _))) (hch k (c₀ k))
  have h0 : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k h => by simpa [h] using hp k
  obtain ⟨z, hz⟩ := exists_point O i ξ _ ht ch (Finset.prod_ne_zero_iff.2 fun k _ => h0 k) fun j => by
    rw [← Finset.prod_div_distrib, map_prod]
    refine prod_mem fun k _ => ?_
    rw [← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (hp k)]
    exact hch k (j k)
  exact dom_of_point O i ξ ha z hz

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S S' Ω Ω' Ω₃ _ _ _ K K' _ _ J J' _ _ y y' 𝔐 𝔐' i i' W hξ`. Take `⟨q, hq⟩` from `exists_dom W i 𝔐.ξ y 𝔐.all 𝔐.tie`. Take `⟨q', hq'⟩` from `exists_dom W i' 𝔐'.ξ y' 𝔐'.all 𝔐'.tie`. Use `⟨q, q', hq, hq', ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hzc⟩` from `exists_valPoint 𝔐.ξ W i q (𝔐.tie.gen.inj q) hq`.

Take `⟨z₀, hz₀, hzc₀⟩` from `exists_valPoint 𝔐'.ξ W i' q' (𝔐'.tie.gen.inj q') hq'`. Establish `hsep : IsSeparated Y.s` using `isSeparated_of_isProjOver' Y.proj`. Establish `hinj : Function.Injective W.subtype` using `Subtype.val_injective`. Establish `hdom : IsDominant (spMap W.subtype)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]`.

Conclude with `bot_le)⟩`. Establish `hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐'.f`. Rewrite using `[← Category.assoc, hz, ← Category.assoc, hz₀]`. Simplify `hξ` using `only [Category.assoc]`. Establish `hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐'.f) ≫ Y.s`.

Establish `hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F)))` using `inferInstance`. Use `ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F))) (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_` and prove the remaining obligations. Simplify using `only [← Category.assoc] at hgen ⊢`. Rewrite using `[hgen]`. Establish `heq : z ≫ 𝔐.f = z₀ ≫ 𝔐'.f` using `ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen`.

Use `congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq` as an intermediate fact. Express the relevant statement in the definitionally equal form `𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐'.f (z₀ (IsLocalRing.closedPoint W)) at this`. Rewrite `this` using `[hzc, hzc₀]`. Then use the resulting hypothesis.
-/
theorem centre : Centre := by
  intro E _ _ _ H D l Xo c Y S S' Ω Ω' Ω₃ _ _ _ K K' _ _ J J' _ _ y y' 𝔐 𝔐' i i' W hξ
  obtain ⟨q, hq⟩ := exists_dom W i 𝔐.ξ y 𝔐.all 𝔐.tie
  obtain ⟨q', hq'⟩ := exists_dom W i' 𝔐'.ξ y' 𝔐'.all 𝔐'.tie
  refine ⟨q, q', hq, hq', ?_⟩
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W i q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐'.ξ W i' q' (𝔐'.tie.gen.inj q') hq'
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐'.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    simpa only [Category.assoc] using hξ
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐'.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐'.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐'.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end SheetDecomposition
