import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

/- English proof (translation)
Take `⟨v, hv⟩` from `i.app_surjective W hW u.val`. Establish `hunit : IsUnit v` using `X.toRingedSpace.isUnit_of_isUnit_germ W v fun x hx => by`. Take `⟨y, rfl⟩` from `Surjective.surj (f := i) x`. Establish `h1 : IsUnit ((i.stalkMap y).hom ((X.presheaf.germ W (i y) hx).hom v))`. Rewrite using `[Scheme.Hom.germ_stalkMap_apply, hv]`.

Conclude with `u.isUnit.map _`. Conclude with `isUnit_of_map_unit _ _ h1`. Conclude with `⟨hunit.unit, Units.ext hv⟩`.
-/
theorem exists_unit_lift_of_surj_closedImm {X X₀ : Scheme.{0}} (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i]
    (W : X.Opens) (hW : IsAffineOpen W) (u : Γ(X₀, i ⁻¹ᵁ W)ˣ) : ∃ s : Γ(X, W)ˣ, pullU i W s = u := by
  obtain ⟨v, hv⟩ := i.app_surjective W hW u.val
  have hunit : IsUnit v := X.toRingedSpace.isUnit_of_isUnit_germ W v fun x hx => by
    obtain ⟨y, rfl⟩ := Surjective.surj (f := i) x
    have h1 : IsUnit ((i.stalkMap y).hom ((X.presheaf.germ W (i y) hx).hom v)) := by
      rw [Scheme.Hom.germ_stalkMap_apply, hv]; exact u.isUnit.map _
    exact isUnit_of_map_unit _ _ h1
  exact ⟨hunit.unit, Units.ext hv⟩

/- English proof (translation)
Rewrite using `[eq_mul_inv_of_mul_eq h1, eq_mul_inv_of_mul_eq h2]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem mul_twist_eq_of_cocycle {G : Type*} [CommGroup G] (A B C E F S T : G) (h1 : A * B = F) (h2 : C * E = F) :
    A * S = C * (S⁻¹ * B * T)⁻¹ * (E * T) := by
  rw [eq_mul_inv_of_mul_eq h1, eq_mul_inv_of_mul_eq h2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Introduce `X X₀ i _ _ c hc`. Take `⟨L, hL, rfl⟩` from `cls_surj c`. Rewrite `hc` using `[← cls_pull hL i (pull_isLB hL i)]`. Take `⟨t, ht⟩` from `(cls_eq_zero_iff _).1 hc`. Set `ι'` to `{q : X.affineOpens × L.ι // (q.1 : X.Opens) ≤ L.U q.2}`.

Set `W : ι' → X.Opens` to `fun q => q.1.1`. Set `J : ι' → L.ι` to `fun q => q.1.2`. Establish `hle : ∀ q : ι', i ⁻¹ᵁ W q ≤ (L.pull i).U (fun _ => J q)` using `fun q y hy => mem_pull.2 (q.2 hy)`. Use `choose s hs using fun q : ι' => exists_unit_lift_of_surj_closedImm i (W q) q.1.1.2 (res (hle q) (t.s (fun _ => J q)))`. Establish `l1 : ∀ q q' : ι', W q ⊓ W q' ≤ L.U (J q) ⊓ L.U (J q')` using `fun q q' => inf_le_inf q.2 q'.2`.

Set `gg : ∀ q q' : ι', Γ(X, W q ⊓ W q')ˣ` to `fun q q' => (res inf_le_left (s q))⁻¹ * res (l1 q q') (L.g (J q) (J q')) * res inf_le_right (s q')`. Set `D : LB X` to `⟨ι', W, gg⟩`. Establish `gD : ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (q q' : ι'), f y ∈ W q → f y ∈ W q' → gm f y (W q ⊓ W q') (D.g q q') = (gm f y (W q) (s q))⁻¹ * gm f y (L.U (J q) ⊓ L.U (J q')) (L.g (J q) (J q')) * gm f y (W q') (s q')`. Introduce `Y f y q q' h h'`. Establish `hm : f y ∈ W q ⊓ W q'` using `⟨h, h'⟩`.

Use `show gm f y _ ((res _ (s q))⁻¹ * res _ (L.g (J q) (J q')) * res _ (s q')) = _`. Rewrite using `[map_mul, map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm, gm_res f y _ hm]`. Establish `hD : D.IsLB` using `{ cover := by`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Take `⟨j, hj⟩` from `exists_chart hL x`. Take `⟨V, hV, hxV, hVle⟩` from `(Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hj`. Conclude with `Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, j), hVle⟩, hxV⟩`. Use `g_self := fun q => unit_ext fun y hy => by`. Rewrite using `[gm_res _ y _ hy, gD X (𝟙 X) y q q hy hy, gm_self hL (𝟙 X) y (q.2 hy), map_one]`.

Use `group`. Use `cocycle := fun a b c => unit_ext fun y hy => by`. Establish `ha : y ∈ W a` using `hy.1.1`. Establish `hb : y ∈ W b` using `hy.1.2`. Establish `hc : y ∈ W c` using `hy.2`.

Rewrite using `[map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gD X (𝟙 X) y a b ha hb, gD X (𝟙 X) y b c hb hc, gD X (𝟙 X) y a c ha hc, ← gm_cocycle hL (𝟙 X) y (a.2 ha) (b.2 hb) (c.2 hc)]`. Use `group`. Use `rfl }`. Use `⟨D, hD, ?_, fun a b => ?_⟩` and prove the remaining obligations. Use `(cls_eq_iff hD hL).2 ⟨⟨fun p => res (le_inf inf_le_left (inf_le_right.trans p.2.2) : L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2)) (L.g p.1 (J p.2)) * res inf_le_right (s p.2)⟩, ?_⟩` and prove the remaining obligations.

Use `(isGen_iff_germ _).2 fun y p p' hp hp' => ?_` and prove the remaining obligations. Establish `val : ∀ p : L.ι × ι', y ∈ L.U p.1 ⊓ W p.2 → gm (𝟙 X) y (L.U p.1 ⊓ W p.2) (res (le_inf inf_le_left (inf_le_right.trans p.2.2) : L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2)) (L.g p.1 (J p.2)) * res inf_le_right (s p.2)) = gm (𝟙 X) y _ (L.g p.1 (J p.2)) * gm (𝟙 X) y (W p.2) (s p.2)` using `fun p h => by`. Rewrite using `[map_mul, gm_res _ y _ h, gm_res _ y _ h]`. Use `show gm (𝟙 X) y (L.U p.1 ⊓ W p.2) _ = gm (𝟙 X) y (L.U p.1 ⊓ W p.2 ⊓ (L.U p'.1 ⊓ W p'.2)) ((LB.div L D).g p p') * gm (𝟙 X) y (L.U p'.1 ⊓ W p'.2) _`. Simplify using `only`.

Use `erw [val p hp, val p' hp', gm_div D L (𝟙 X) y p p' ⟨hp, hp'⟩, gD X (𝟙 X) y p.2 p'.2 hp.2 hp'.2]`. Conclude with `mul_twist_eq_of_cocycle _ _ _ _ _ _ _ (gm_cocycle hL (𝟙 X) y hp.1 (p.2.2 hp.2) (p'.2.2 hp'.2)) (gm_cocycle hL (𝟙 X) y hp.1 hp'.1 (p'.2.2 hp'.2))`. Apply `unit_ext` to reduce the goal to its premises. Introduce `y hy`. Establish `hsa : ∀ q : ι', i y ∈ W q → gm i y (W q) (s q) = gm (𝟙 X₀) y _ (t.s (fun _ => J q))` using `fun q h => by`.

Establish `e` using `gm_pull (𝟙 X₀) i y (W q) h (s q)`. Rewrite `e` using `[Category.id_comp]`. Rewrite using `[← e, hs q, gm_res (𝟙 X₀) y (hle q) h]`. Establish `ha : i y ∈ W a` using `hy.1`. Establish `hb : i y ∈ W b` using `hy.2`.

Establish `eg` using `gm_pull_g L i (𝟙 X₀) y (fun _ => J a) (fun _ => J b) (hle a ha) (hle b hb)`. Rewrite `eg` using `[Category.id_comp]`. Establish `e` using `gm_pull (𝟙 X₀) i y (W a ⊓ W b) hy (D.g a b)`. Rewrite `e` using `[Category.id_comp]`. Rewrite using `[e, gD X₀ i y a b ha hb, map_one, hsa a ha, hsa b hb, ← eg, (isGen_iff_germ t).1 ht y _ _ (hle a ha) (hle b hb)]`.

Use `group`.
-/
theorem exists_cocycle_one_on_thickening : ∀ (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i]
    (c : Pic X), GlobalTheory.CechPic.pull i c = 0 →
    ∃ (D : LB X) (hD : D.IsLB), cls D hD = c ∧ ∀ a b, pullU i _ (D.g a b) = 1 := by
  intro X X₀ i _ _ c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL i (pull_isLB hL i)] at hc
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  let ι' := {q : X.affineOpens × L.ι // (q.1 : X.Opens) ≤ L.U q.2}
  let W : ι' → X.Opens := fun q => q.1.1
  let J : ι' → L.ι := fun q => q.1.2
  have hle : ∀ q : ι', i ⁻¹ᵁ W q ≤ (L.pull i).U (fun _ => J q) := fun q y hy => mem_pull.2 (q.2 hy)
  choose s hs using fun q : ι' =>
    exists_unit_lift_of_surj_closedImm i (W q) q.1.1.2 (res (hle q) (t.s (fun _ => J q)))
  have l1 : ∀ q q' : ι', W q ⊓ W q' ≤ L.U (J q) ⊓ L.U (J q') := fun q q' => inf_le_inf q.2 q'.2
  let gg : ∀ q q' : ι', Γ(X, W q ⊓ W q')ˣ := fun q q' =>
    (res inf_le_left (s q))⁻¹ * res (l1 q q') (L.g (J q) (J q')) * res inf_le_right (s q')
  let D : LB X := ⟨ι', W, gg⟩
  have gD : ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (q q' : ι'), f y ∈ W q → f y ∈ W q' →
      gm f y (W q ⊓ W q') (D.g q q') =
        (gm f y (W q) (s q))⁻¹ * gm f y (L.U (J q) ⊓ L.U (J q')) (L.g (J q) (J q')) * gm f y (W q') (s q') := by
    intro Y f y q q' h h'
    have hm : f y ∈ W q ⊓ W q' := ⟨h, h'⟩
    show gm f y _ ((res _ (s q))⁻¹ * res _ (L.g (J q) (J q')) * res _ (s q')) = _
    rw [map_mul, map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm, gm_res f y _ hm]
  have hD : D.IsLB := {
    cover := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨j, hj⟩ := exists_chart hL x
      obtain ⟨V, hV, hxV, hVle⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hj
      exact Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, j), hVle⟩, hxV⟩
    g_self := fun q => unit_ext fun y hy => by
      rw [gm_res _ y _ hy, gD X (𝟙 X) y q q hy hy, gm_self hL (𝟙 X) y (q.2 hy), map_one]
      group
    cocycle := fun a b c => unit_ext fun y hy => by
      have ha : y ∈ W a := hy.1.1
      have hb : y ∈ W b := hy.1.2
      have hc : y ∈ W c := hy.2
      rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gD X (𝟙 X) y a b ha hb,
        gD X (𝟙 X) y b c hb hc, gD X (𝟙 X) y a c ha hc,
        ← gm_cocycle hL (𝟙 X) y (a.2 ha) (b.2 hb) (c.2 hc)]
      group
      rfl }
  refine ⟨D, hD, ?_, fun a b => ?_⟩
  · refine (cls_eq_iff hD hL).2 ⟨⟨fun p => res (le_inf inf_le_left (inf_le_right.trans p.2.2) :
        L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2)) (L.g p.1 (J p.2)) * res inf_le_right (s p.2)⟩, ?_⟩
    refine (isGen_iff_germ _).2 fun y p p' hp hp' => ?_
    have val : ∀ p : L.ι × ι', y ∈ L.U p.1 ⊓ W p.2 → gm (𝟙 X) y (L.U p.1 ⊓ W p.2)
        (res (le_inf inf_le_left (inf_le_right.trans p.2.2) : L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2))
          (L.g p.1 (J p.2)) * res inf_le_right (s p.2)) =
        gm (𝟙 X) y _ (L.g p.1 (J p.2)) * gm (𝟙 X) y (W p.2) (s p.2) := fun p h => by
      rw [map_mul, gm_res _ y _ h, gm_res _ y _ h]
    show gm (𝟙 X) y (L.U p.1 ⊓ W p.2) _ = gm (𝟙 X) y (L.U p.1 ⊓ W p.2 ⊓ (L.U p'.1 ⊓ W p'.2)) ((LB.div L D).g p p') *
      gm (𝟙 X) y (L.U p'.1 ⊓ W p'.2) _
    dsimp only
    erw [val p hp, val p' hp', gm_div D L (𝟙 X) y p p' ⟨hp, hp'⟩, gD X (𝟙 X) y p.2 p'.2 hp.2 hp'.2]
    exact mul_twist_eq_of_cocycle _ _ _ _ _ _ _ (gm_cocycle hL (𝟙 X) y hp.1 (p.2.2 hp.2) (p'.2.2 hp'.2))
      (gm_cocycle hL (𝟙 X) y hp.1 hp'.1 (p'.2.2 hp'.2))
  · apply unit_ext
    intro y hy
    have hsa : ∀ q : ι', i y ∈ W q → gm i y (W q) (s q) = gm (𝟙 X₀) y _ (t.s (fun _ => J q)) := fun q h => by
      have e := gm_pull (𝟙 X₀) i y (W q) h (s q)
      rw [Category.id_comp] at e
      rw [← e, hs q, gm_res (𝟙 X₀) y (hle q) h]
    have ha : i y ∈ W a := hy.1
    have hb : i y ∈ W b := hy.2
    have eg := gm_pull_g L i (𝟙 X₀) y (fun _ => J a) (fun _ => J b) (hle a ha) (hle b hb)
    rw [Category.id_comp] at eg
    have e := gm_pull (𝟙 X₀) i y (W a ⊓ W b) hy (D.g a b)
    rw [Category.id_comp] at e
    rw [e, gD X₀ i y a b ha hb, map_one, hsa a ha, hsa b hb, ← eg,
      (isGen_iff_germ t).1 ht y _ _ (hle a ha) (hle b hb)]
    group

end GlobalTheory.CechPic
