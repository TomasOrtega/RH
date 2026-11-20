import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

section Loc

variable {S T : Type} [CommRing S] [CommRing T] [Algebra S T] (Sg : Submonoid S) [IsLocalization Sg T] {X X' : Scheme.{0}}
  {p : X ⟶ Sp S} {p' : X' ⟶ Sp T} {φ : X' ⟶ X} (H : IsPullback φ p' p (spMap (algebraMap S T)))
include H

/- English proof (translation)
Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) le_top le_top (UY := φ ⁻¹ᵁ V) (by simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hV)`. Establish `hx : x ∈ (⊤ : Subring Γ(X', φ ⁻¹ᵁ V))` using `trivial`. Rewrite `hx` using `[← CommRingCat.closure_range_union_range_eq_top_of_isPushout po]`. Establish `one : ∀ z, φ z ∈ V → gs φ z V 1 = 1` using `fun z hz => by rw [gs_eq φ z V hz, map_one, map_one]`. Proceed by induction on `hx using Subring.closure_induction with`.

Consider the case `mem x hx`. Break down `hx with ⟨d, rfl⟩ | ⟨c, rfl⟩` into its components or cases. Conclude with `⟨1, Sg.one_mem, d, fun z hz => by`. Rewrite using `[cst_one, _root_.one_mul]`. Conclude with `((gs_appLE φ V _ _ (𝟙 X') z hz d).trans (by rw [Category.id_comp])).symm⟩`.

Take `⟨⟨a, s⟩, e⟩` from `IsLocalization.surj Sg ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom c)`. Use `⟨s, s.2, constFn p V a, fun z hz => ?_⟩` and prove the remaining obligations. Establish `e₁ : gs (𝟙 X') z _ ((p'.appLE ⊤ (φ ⁻¹ᵁ V) le_top).hom c) = cst p' z ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom c)`. Rewrite using `[cst, Iso.hom_inv_id_apply]`. Conclude with `(gs_appLE p' ⊤ _ _ (𝟙 X') z hz c).trans (by rw [Category.id_comp])`.

Rewrite using `[gs_constFn p V φ z hz, H.w, cst_comp, cst_comp, ← e, cst_mul, mul_comm]`. Conclude with `congrArg₂ (· * ·) rfl e₁.symm`. Consider the case `zero => exact ⟨1, Sg.one_mem, 0, fun z hz => by rw [gs_zero φ z V hz, gs_zero (𝟙 X') z _ hz, mul_zero]⟩`. Consider the case `one => exact ⟨1, Sg.one_mem, 1, fun z hz => by`. Rewrite using `[one z hz, cst_one, _root_.one_mul, gs_eq (𝟙 X') z _ hz, map_one, map_one]⟩`.

Consider the case `add x x' _ _ h h'`. Take `⟨s, hs, y, e⟩` from `h`. Take `⟨s', hs', y', e'⟩` from `h'`. Use `⟨s * s', Sg.mul_mem hs hs', constFn p V s' * y + constFn p V s * y', fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[gs_add φ z V hz, gs_mul φ z V hz, gs_mul φ z V hz, gs_constFn p V φ z hz, gs_constFn p V φ z hz, e z hz, e' z hz, gs_add (𝟙 X') z _ hz, cst_mul]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x _ h`. Take `⟨s, hs, y, e⟩` from `h`. Use `⟨s, hs, -y, fun z hz => ?_⟩` and prove the remaining obligations. Use `e z hz` as an intermediate fact.

Rewrite `this`, the goal using `[gs_eq φ z V hz, gs_eq (𝟙 X') z _ hz]`. Rewrite using `[map_neg, map_neg, this, map_neg, map_neg, mul_neg]`. Consider the case `mul x x' _ _ h h'`. Take `⟨s, hs, y, e⟩` from `h`. Take `⟨s', hs', y', e'⟩` from `h'`.

Use `⟨s * s', Sg.mul_mem hs hs', y * y', fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[gs_mul φ z V hz, e z hz, e' z hz, gs_mul (𝟙 X') z _ hz, cst_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem loc_surj {V : X.Opens} (hV : IsAffineOpen V) (x : Γ(X', φ ⁻¹ᵁ V)) : ∃ s ∈ Sg, ∃ y : Γ(X, V),
    ∀ z, φ z ∈ V → gs φ z V y = cst (φ ≫ p) z s * gs (𝟙 X') z _ x := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) le_top le_top (UY := φ ⁻¹ᵁ V) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hV)
  have hx : x ∈ (⊤ : Subring Γ(X', φ ⁻¹ᵁ V)) := trivial
  rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout po] at hx
  have one : ∀ z, φ z ∈ V → gs φ z V 1 = 1 := fun z hz => by rw [gs_eq φ z V hz, map_one, map_one]
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨d, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨1, Sg.one_mem, d, fun z hz => by
        rw [cst_one, _root_.one_mul]
        exact ((gs_appLE φ V _ _ (𝟙 X') z hz d).trans (by rw [Category.id_comp])).symm⟩
    · obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj Sg ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom c)
      refine ⟨s, s.2, constFn p V a, fun z hz => ?_⟩
      have e₁ : gs (𝟙 X') z _ ((p'.appLE ⊤ (φ ⁻¹ᵁ V) le_top).hom c) =
          cst p' z ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom c) := by
        rw [cst, Iso.hom_inv_id_apply]
        exact (gs_appLE p' ⊤ _ _ (𝟙 X') z hz c).trans (by rw [Category.id_comp])
      rw [gs_constFn p V φ z hz, H.w, cst_comp, cst_comp, ← e, cst_mul, mul_comm]
      exact congrArg₂ (· * ·) rfl e₁.symm
  | zero => exact ⟨1, Sg.one_mem, 0, fun z hz => by rw [gs_zero φ z V hz, gs_zero (𝟙 X') z _ hz, mul_zero]⟩
  | one => exact ⟨1, Sg.one_mem, 1, fun z hz => by
      rw [one z hz, cst_one, _root_.one_mul, gs_eq (𝟙 X') z _ hz, map_one, map_one]⟩
  | add x x' _ _ h h' =>
    obtain ⟨s, hs, y, e⟩ := h
    obtain ⟨s', hs', y', e'⟩ := h'
    refine ⟨s * s', Sg.mul_mem hs hs', constFn p V s' * y + constFn p V s * y', fun z hz => ?_⟩
    rw [gs_add φ z V hz, gs_mul φ z V hz, gs_mul φ z V hz, gs_constFn p V φ z hz, gs_constFn p V φ z hz, e z hz, e' z hz,
      gs_add (𝟙 X') z _ hz, cst_mul]
    ring
  | neg x _ h =>
    obtain ⟨s, hs, y, e⟩ := h
    refine ⟨s, hs, -y, fun z hz => ?_⟩
    have := e z hz
    rw [gs_eq φ z V hz, gs_eq (𝟙 X') z _ hz] at this ⊢
    rw [map_neg, map_neg, this, map_neg, map_neg, mul_neg]
  | mul x x' _ _ h h' =>
    obtain ⟨s, hs, y, e⟩ := h
    obtain ⟨s', hs', y', e'⟩ := h'
    refine ⟨s * s', Sg.mul_mem hs hs', y * y', fun z hz => ?_⟩
    rw [gs_mul φ z V hz, e z hz, e' z hz, gs_mul (𝟙 X') z _ hz, cst_mul]
    ring

/- English proof (translation)
Set `alg : S →+* Γ(X, V)` to `(p.appLE ⊤ V (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom`. Establish `s₀ : hV.fromSpec ≫ p = spMap alg`. Rewrite using `[← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hV (fun _ _ => trivial), IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`. Both sides reduce to the same expression. Set `C` to `Localization (Sg.map alg)`.

Set `g : T →+* C` to `IsLocalization.map C alg Sg.le_comap_map`. Establish `sq : (spMap (algebraMap Γ(X, V) C) ≫ hV.fromSpec) ≫ p = spMap g ≫ spMap (algebraMap S T)`. Rewrite using `[Category.assoc, s₀, ← spMap_comp, ← spMap_comp, IsLocalization.map_comp]`. Establish `r₂ : H.lift _ _ sq ≫ φ = spMap (algebraMap Γ(X, V) C) ≫ hV.fromSpec` using `H.lift_fst _ _ _`. Establish `z₀ : algebraMap Γ(X, V) C y = 0` using `cst_ext fun z => by`.

Establish `hm : φ (H.lift _ _ sq z) ∈ V` using `(congrArg (fun q => q z ∈ V) r₂).mpr (hV.range_fromSpec.le ⟨spMap (algebraMap Γ(X, V) C) z, rfl⟩)`. Establish `e` using `(gs_fromSpec hV le_rfl (spMap (algebraMap Γ(X, V) C)) z y).trans (gs_spec _ z _)`. Establish `e₀` using `(gs_pull (𝟙 X') φ (H.lift _ _ sq z) V hm y).trans ((congrArg (fun q => gs q _ V y) (Category.id_comp φ)).trans (h _ hm))`. Rewrite `e` using `[← r₂, ← gs_pull _ φ z V hm, gs_stalkMap _ z _ hm, e₀, map_zero]`. Simplify using `only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] at e`.

Rewrite using `[← e, cst, map_zero, gs_zero _ z ⊤ trivial]`. Take `⟨⟨_, s, hs, rfl⟩, e⟩` from `(IsLocalization.map_eq_zero_iff (Sg.map alg) C y).1 z₀`. Use `⟨s, hs, fun x hx => ?_⟩` and prove the remaining obligations. Use `congrArg (gs (𝟙 X) x V) e` as an intermediate fact. Rewrite `this` using `[gs_mul _ x V hx, gs_zero _ x V hx]`.

Conclude with `(congrArg₂ (· * ·) ((gs_constFn p V (𝟙 X) x hx s).trans (by rw [Category.id_comp])).symm rfl).trans this`.
-/
theorem loc_ker {V : X.Opens} (hV : IsAffineOpen V) (y : Γ(X, V)) (h : ∀ z, φ z ∈ V → gs φ z V y = 0) :
    ∃ s ∈ Sg, ∀ x ∈ V, cst p x s * gs (𝟙 X) x V y = 0 := by
  let alg : S →+* Γ(X, V) := (p.appLE ⊤ V (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  have s₀ : hV.fromSpec ≫ p = spMap alg := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hV (fun _ _ => trivial),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
  let C := Localization (Sg.map alg)
  let g : T →+* C := IsLocalization.map C alg Sg.le_comap_map
  have sq : (spMap (algebraMap Γ(X, V) C) ≫ hV.fromSpec) ≫ p = spMap g ≫ spMap (algebraMap S T) := by
    rw [Category.assoc, s₀, ← spMap_comp, ← spMap_comp, IsLocalization.map_comp]
  have r₂ : H.lift _ _ sq ≫ φ = spMap (algebraMap Γ(X, V) C) ≫ hV.fromSpec := H.lift_fst _ _ _
  have z₀ : algebraMap Γ(X, V) C y = 0 := cst_ext fun z => by
    have hm : φ (H.lift _ _ sq z) ∈ V := (congrArg (fun q => q z ∈ V) r₂).mpr
      (hV.range_fromSpec.le ⟨spMap (algebraMap Γ(X, V) C) z, rfl⟩)
    have e := (gs_fromSpec hV le_rfl (spMap (algebraMap Γ(X, V) C)) z y).trans (gs_spec _ z _)
    have e₀ := (gs_pull (𝟙 X') φ (H.lift _ _ sq z) V hm y).trans ((congrArg (fun q => gs q _ V y) (Category.id_comp φ)).trans (h _ hm))
    rw [← r₂, ← gs_pull _ φ z V hm, gs_stalkMap _ z _ hm, e₀, map_zero] at e
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] at e
    rw [← e, cst, map_zero, gs_zero _ z ⊤ trivial]
  obtain ⟨⟨_, s, hs, rfl⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Sg.map alg) C y).1 z₀
  refine ⟨s, hs, fun x hx => ?_⟩
  have := congrArg (gs (𝟙 X) x V) e
  rw [gs_mul _ x V hx, gs_zero _ x V hx] at this
  exact (congrArg₂ (· * ·) ((gs_constFn p V (𝟙 X) x hx s).trans (by rw [Category.id_comp])).symm rfl).trans this

/- English proof (translation)
Establish `: IsSeparated (terminal.from X)` using `by rw [← terminal.comp_from p]; infer_instance`. Establish `tr : ∀ (y : X') j j' k k', φ y ∈ L.U j → φ y ∈ L.U j' → y ∈ L'.U k → y ∈ L'.U k' → (gw w (𝟙 X') y j k).val * gs (𝟙 X') y _ (τ.f k) = (gm φ y _ (L.g j j')).val * ((gw w (𝟙 X') y j' k').val * gs (𝟙 X') y _ (τ.f k'))` using `fun y j j' k k' a b c d => by`. Use `hw _ (𝟙 X') y j j' k k' a b c d` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Rewrite using `[this, gs_compat τ (𝟙 X') y c d, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]`.

Use `choose j hj using fun x : X => exists_chart hL x`. Use `choose V hV hxV hle using fun x : X => exists_isAffineOpen_mem_and_subset (hj x)`. Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)`. Establish `cov : ∀ x, ∃ a : F, x ∈ V a` using `fun x => by`. Take `⟨a, ha, h⟩` from `Set.mem_iUnion₂.1 (hF (Set.mem_univ x))`.

Conclude with `⟨⟨a, ha⟩, h⟩`. Establish `up : ∀ a : F, ∃ t : Γ(X', φ ⁻¹ᵁ V a), ∀ z k, φ z ∈ V a → z ∈ L'.U k → gs (𝟙 X') z _ t = (gw w (𝟙 X') z (j a) k).val * gs (𝟙 X') z _ (τ.f k)` using `fun a => by`. Establish `le : ∀ k, φ ⁻¹ᵁ V a ⊓ L'.U k ≤ (L.pull φ).U (fun _ => j a) ⊓ L'.U k` using `fun k y hy => ⟨mem_pull.2 (hle a hy.1), hy.2⟩`. Take `⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', φ ⁻¹ᵁ V a ⊓ L'.U k), ∀ z k, z ∈ φ ⁻¹ᵁ V a ⊓ L'.U k → gs (𝟙 X') z _ (u k) = (gw w (𝟙 X') z (j a) k).val * gs (𝟙 X') z _ (τ.f k)` from `⟨fun k => (res (le k) (w.s (fun _ => j a, k))).val * resG X' inf_le_right (τ.f k), fun z k hz => (gs_mul _ z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit _ z _ hz _).trans (congrArg Units.val (gm_res _ z (le k) hz _))) (gs_res _ z _ hz _))⟩`. Take `⟨t, ht, -⟩` from `X'.sheaf.existsUnique_gluing' (fun k => φ ⁻¹ᵁ V a ⊓ L'.U k) (φ ⁻¹ᵁ V a) (fun k => homOfLE inf_le_left) (fun y hy => by`.

Take `⟨k, hk⟩` from `exists_chart hL' y`. Conclude with `Opens.mem_iSup.2 ⟨k, hy, hk⟩) u`. Use the proof step `(fun k k' => fn_ext (V := (φ ⁻¹ᵁ V a ⊓ L'.U k) ⊓ (φ ⁻¹ᵁ V a ⊓ L'.U k')) fun y hy => by`. Use `(gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)` and prove the remaining obligations. Rewrite using `[hu y k hy.1, hu y k' hy.2, tr y _ _ k k' (hle a hy.1.1) (hle a hy.1.1) hy.1.2 hy.2.2, gm_self hL φ y (hle a hy.1.1), Units.val_one, _root_.one_mul])`.

Use `⟨t, fun z k h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `hz : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ V a ⊓ L'.U k` using `⟨h₁, h₂⟩`. Conclude with `(gs_res _ z inf_le_left hz t).symm.trans ((congrArg (gs _ z _) (ht k)).trans (hu z k hz))`. Use `choose t ht using up`. Use `choose s hs y hy using fun a : F => loc_surj Sg H (hV a) (t a)`.

Set `y₁ : ∀ a : F, Γ(X, V a)` to `fun a => constFn p _ (∏ b ∈ Finset.univ.erase a, s b) * y a`. Establish `hy₁ : ∀ (a : F) z k, φ z ∈ V a → z ∈ L'.U k → gs φ z _ (y₁ a) = cst (φ ≫ p) z (∏ b, s b) * ((gw w (𝟙 X') z (j a) k).val * gs (𝟙 X') z _ (τ.f k))` using `fun a z k h₁ h₂ => by`. Rewrite using `[gs_mul φ z _ h₁, gs_constFn p _ φ z h₁, hy a z h₁, ht a z k h₁ h₂, ← _root_.mul_assoc, ← cst_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ a)]`. Establish `le₂ : ∀ a b : F, V a ⊓ V b ≤ L.U (j a) ⊓ L.U (j b)` using `fun a b x hx => ⟨hle a hx.1, hle b hx.2⟩`. Establish `dv : ∀ (a b : F) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ V a ⊓ V b → gs r z (V a ⊓ V b) (resG X inf_le_left (y₁ a) - resG X (le₂ a b) (L.g (j a) (j b)).val * resG X inf_le_right (y₁ b)) = gs r z _ (y₁ a) - (gm r z _ (L.g (j a) (j b))).val * gs r z _ (y₁ b)` using `fun a b Z r z hz => by`.

Rewrite using `[← gs_res r z inf_le_left hz, ← gs_res r z inf_le_right hz, ← gs_unit r z _ (le₂ a b hz), ← gs_res r z (le₂ a b) hz, ← gs_mul r z _ hz]`. Simplify using `only [gs_eq r z _ hz, map_sub]`. Use `choose s' hs' hk using fun ab : F × F => loc_ker Sg H ((hV ab.1).inf (hV ab.2)) _ fun z hz => by`. Take `⟨k, hk⟩` from `exists_chart hL' z`. Rewrite using `[dv ab.1 ab.2 φ z hz, hy₁ _ z k hz.1 hk, hy₁ _ z k hz.2 hk, tr z _ _ k k (hle _ hz.1) (hle _ hz.2) hk hk, mul_left_comm, sub_self]`.

Establish `cmp : ∀ (a b : F) x, x ∈ V a → x ∈ V b → cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ a) = (gm (𝟙 X) x _ (L.g (j a) (j b))).val * (cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ b))` using `fun a b x ha hb => by`. Establish `e` using `hk (a, b) x ⟨ha, hb⟩`. Rewrite `e` using `[dv a b (𝟙 X) x ⟨ha, hb⟩, mul_sub, sub_eq_zero]`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ (a, b)), cst_mul, _root_.mul_assoc, e]`. Expand and normalize the polynomial expressions, which then agree.

Establish `glue : ∀ i, ∃ q : Γ(X, L.U i), ∀ (a : F) x, x ∈ L.U i → x ∈ V a → gs (𝟙 X) x _ q = (gm (𝟙 X) x _ (L.g i (j a))).val * (cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ a))` using `fun i => by`. Establish `le : ∀ a : F, L.U i ⊓ V a ≤ L.U i ⊓ L.U (j a)` using `fun a x hx => ⟨hx.1, hle a hx.2⟩`. Take `⟨u, hu⟩ : ∃ u : ∀ a : F, Γ(X, L.U i ⊓ V a), ∀ (a : F) x, x ∈ L.U i ⊓ V a → gs (𝟙 X) x _ (u a) = (gm (𝟙 X) x _ (L.g i (j a))).val * (cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ a))` from `⟨fun a => resG X (le a) (L.g i (j a)).val * (constFn p _ (∏ ab, s' ab) * resG X inf_le_right (y₁ a)), fun a x hx => by`. Rewrite using `[gs_mul _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ (le a hx), gs_constFn p _ _ x hx, Category.id_comp]⟩`. Take `⟨q, hq, -⟩` from `X.sheaf.existsUnique_gluing' (fun a : F => L.U i ⊓ V a) (L.U i) (fun a => homOfLE inf_le_left) (fun x hx => by`.

Take `⟨a, ha⟩` from `cov x`. Conclude with `Opens.mem_iSup.2 ⟨a, hx, ha⟩) u`. Use the proof step `(fun a b => fn_ext (V := (L.U i ⊓ V a) ⊓ (L.U i ⊓ V b)) fun x hx => by`. Use `(gs_res (𝟙 X) x inf_le_left hx _).trans (Eq.trans ?_ (gs_res (𝟙 X) x inf_le_right hx _).symm)` and prove the remaining obligations. Rewrite using `[hu a x hx.1, hu b x hx.2, cmp a b x hx.1.2 hx.2.2, ← _root_.mul_assoc, ← Units.val_mul, gm_cocycle hL (𝟙 X) x hx.1.1 (hle a hx.1.2) (hle b hx.2.2)])`.

Use `⟨q, fun a x h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `hz : (𝟙 X : X ⟶ X) x ∈ L.U i ⊓ V a` using `⟨h₁, h₂⟩`. Conclude with `(gs_res _ x inf_le_left hz q).symm.trans ((congrArg (gs _ x _) (hq a)).trans (hu a x hz))`. Use `choose q hq using glue`. Use `⟨(∏ ab, s' ab) * ∏ b, s b, Sg.mul_mem (Sg.prod_mem fun _ _ => hs' _) (Sg.prod_mem fun _ _ => hs _), ⟨q, fun i i' => fn_ext fun x hx => ?_⟩, fun z i k h₁ h₂ => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `cov x`. Rewrite using `[gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx, hq i a x hx.1 ha, hq i' a x hx.2 ha, ← gm_cocycle hL (𝟙 X) x hx.1 hx.2 (hle a ha), Units.val_mul, _root_.mul_assoc]`. Take `⟨a, ha⟩` from `cov (φ z)`. Establish `hm : φ z ∈ L.U i ⊓ L.U (j a)` using `⟨h₁, hle a ha⟩`. Use `show gs φ z _ (q i) = _`.

Rewrite using `[gs_stalkMap φ z _ h₁, hq i a _ h₁ ha, map_mul, map_mul, cst_stalkMap, ← gs_stalkMap φ z _ ha, ← gs_unit (𝟙 X) (φ z) _ hm, ← gs_stalkMap φ z _ hm, gs_unit φ z _ hm, hy₁ a z k ha h₂, tr z i (j a) k k h₁ (hle a ha) h₂ h₂, cst_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_extend [CompactSpace X] [IsSeparated p] {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w) (τ : LB.Sec L') : ∃ s ∈ Sg, ∃ σ : LB.Sec L, ∀ z j k, φ z ∈ L.U j → z ∈ L'.U k →
      gs φ z _ (σ.f j) = cst (φ ≫ p) z s * ((gw w (𝟙 X') z j k).val * gs (𝟙 X') z _ (τ.f k)) := by
  classical
  have : IsSeparated (terminal.from X) := by rw [← terminal.comp_from p]; infer_instance
  have tr : ∀ (y : X') j j' k k', φ y ∈ L.U j → φ y ∈ L.U j' → y ∈ L'.U k → y ∈ L'.U k' →
      (gw w (𝟙 X') y j k).val * gs (𝟙 X') y _ (τ.f k) =
        (gm φ y _ (L.g j j')).val * ((gw w (𝟙 X') y j' k').val * gs (𝟙 X') y _ (τ.f k')) := fun y j j' k k' a b c d => by
    have := hw _ (𝟙 X') y j j' k k' a b c d
    rw [Category.id_comp] at this
    rw [this, gs_compat τ (𝟙 X') y c d, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul,
      mul_right_comm, inv_mul_cancel_right]
  choose j hj using fun x : X => exists_chart hL x
  choose V hV hxV hle using fun x : X => exists_isAffineOpen_mem_and_subset (hj x)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have cov : ∀ x, ∃ a : F, x ∈ V a := fun x => by
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x)); exact ⟨⟨a, ha⟩, h⟩
  have up : ∀ a : F, ∃ t : Γ(X', φ ⁻¹ᵁ V a), ∀ z k, φ z ∈ V a → z ∈ L'.U k →
      gs (𝟙 X') z _ t = (gw w (𝟙 X') z (j a) k).val * gs (𝟙 X') z _ (τ.f k) := fun a => by
    have le : ∀ k, φ ⁻¹ᵁ V a ⊓ L'.U k ≤ (L.pull φ).U (fun _ => j a) ⊓ L'.U k := fun k y hy =>
      ⟨mem_pull.2 (hle a hy.1), hy.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', φ ⁻¹ᵁ V a ⊓ L'.U k), ∀ z k, z ∈ φ ⁻¹ᵁ V a ⊓ L'.U k →
        gs (𝟙 X') z _ (u k) = (gw w (𝟙 X') z (j a) k).val * gs (𝟙 X') z _ (τ.f k) :=
      ⟨fun k => (res (le k) (w.s (fun _ => j a, k))).val * resG X' inf_le_right (τ.f k), fun z k hz =>
        (gs_mul _ z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit _ z _ hz _).trans (congrArg Units.val
          (gm_res _ z (le k) hz _))) (gs_res _ z _ hz _))⟩
    obtain ⟨t, ht, -⟩ := X'.sheaf.existsUnique_gluing' (fun k => φ ⁻¹ᵁ V a ⊓ L'.U k) (φ ⁻¹ᵁ V a)
      (fun k => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' y
        exact Opens.mem_iSup.2 ⟨k, hy, hk⟩) u
      (fun k k' => fn_ext (V := (φ ⁻¹ᵁ V a ⊓ L'.U k) ⊓ (φ ⁻¹ᵁ V a ⊓ L'.U k')) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu y k hy.1, hu y k' hy.2, tr y _ _ k k' (hle a hy.1.1) (hle a hy.1.1) hy.1.2 hy.2.2,
          gm_self hL φ y (hle a hy.1.1), Units.val_one, _root_.one_mul])
    refine ⟨t, fun z k h₁ h₂ => ?_⟩
    have hz : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ V a ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res _ z inf_le_left hz t).symm.trans ((congrArg (gs _ z _) (ht k)).trans (hu z k hz))
  choose t ht using up
  choose s hs y hy using fun a : F => loc_surj Sg H (hV a) (t a)
  let y₁ : ∀ a : F, Γ(X, V a) := fun a => constFn p _ (∏ b ∈ Finset.univ.erase a, s b) * y a
  have hy₁ : ∀ (a : F) z k, φ z ∈ V a → z ∈ L'.U k → gs φ z _ (y₁ a) =
      cst (φ ≫ p) z (∏ b, s b) * ((gw w (𝟙 X') z (j a) k).val * gs (𝟙 X') z _ (τ.f k)) := fun a z k h₁ h₂ => by
    rw [gs_mul φ z _ h₁, gs_constFn p _ φ z h₁, hy a z h₁, ht a z k h₁ h₂, ← _root_.mul_assoc, ← cst_mul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  have le₂ : ∀ a b : F, V a ⊓ V b ≤ L.U (j a) ⊓ L.U (j b) := fun a b x hx => ⟨hle a hx.1, hle b hx.2⟩
  have dv : ∀ (a b : F) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ V a ⊓ V b →
      gs r z (V a ⊓ V b) (resG X inf_le_left (y₁ a) - resG X (le₂ a b) (L.g (j a) (j b)).val * resG X inf_le_right (y₁ b)) =
        gs r z _ (y₁ a) - (gm r z _ (L.g (j a) (j b))).val * gs r z _ (y₁ b) := fun a b Z r z hz => by
    rw [← gs_res r z inf_le_left hz, ← gs_res r z inf_le_right hz, ← gs_unit r z _ (le₂ a b hz), ← gs_res r z (le₂ a b) hz,
      ← gs_mul r z _ hz]
    simp only [gs_eq r z _ hz, map_sub]
  choose s' hs' hk using fun ab : F × F => loc_ker Sg H ((hV ab.1).inf (hV ab.2)) _ fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [dv ab.1 ab.2 φ z hz, hy₁ _ z k hz.1 hk, hy₁ _ z k hz.2 hk, tr z _ _ k k (hle _ hz.1) (hle _ hz.2) hk hk, mul_left_comm,
      sub_self]
  have cmp : ∀ (a b : F) x, x ∈ V a → x ∈ V b → cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ a) =
      (gm (𝟙 X) x _ (L.g (j a) (j b))).val * (cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ b)) := fun a b x ha hb => by
    have e := hk (a, b) x ⟨ha, hb⟩
    rw [dv a b (𝟙 X) x ⟨ha, hb⟩, mul_sub, sub_eq_zero] at e
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (a, b)), cst_mul, _root_.mul_assoc, e]
    ring
  have glue : ∀ i, ∃ q : Γ(X, L.U i), ∀ (a : F) x, x ∈ L.U i → x ∈ V a → gs (𝟙 X) x _ q =
      (gm (𝟙 X) x _ (L.g i (j a))).val * (cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ a)) := fun i => by
    have le : ∀ a : F, L.U i ⊓ V a ≤ L.U i ⊓ L.U (j a) := fun a x hx => ⟨hx.1, hle a hx.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ a : F, Γ(X, L.U i ⊓ V a), ∀ (a : F) x, x ∈ L.U i ⊓ V a → gs (𝟙 X) x _ (u a) =
        (gm (𝟙 X) x _ (L.g i (j a))).val * (cst p x (∏ ab, s' ab) * gs (𝟙 X) x _ (y₁ a)) :=
      ⟨fun a => resG X (le a) (L.g i (j a)).val * (constFn p _ (∏ ab, s' ab) * resG X inf_le_right (y₁ a)), fun a x hx => by
        rw [gs_mul _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ (le a hx),
          gs_constFn p _ _ x hx, Category.id_comp]⟩
    obtain ⟨q, hq, -⟩ := X.sheaf.existsUnique_gluing' (fun a : F => L.U i ⊓ V a) (L.U i) (fun a => homOfLE inf_le_left)
      (fun x hx => by
        obtain ⟨a, ha⟩ := cov x
        exact Opens.mem_iSup.2 ⟨a, hx, ha⟩) u
      (fun a b => fn_ext (V := (L.U i ⊓ V a) ⊓ (L.U i ⊓ V b)) fun x hx => by
        refine (gs_res (𝟙 X) x inf_le_left hx _).trans (Eq.trans ?_ (gs_res (𝟙 X) x inf_le_right hx _).symm)
        rw [hu a x hx.1, hu b x hx.2, cmp a b x hx.1.2 hx.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hL (𝟙 X) x hx.1.1 (hle a hx.1.2) (hle b hx.2.2)])
    refine ⟨q, fun a x h₁ h₂ => ?_⟩
    have hz : (𝟙 X : X ⟶ X) x ∈ L.U i ⊓ V a := ⟨h₁, h₂⟩
    exact (gs_res _ x inf_le_left hz q).symm.trans ((congrArg (gs _ x _) (hq a)).trans (hu a x hz))
  choose q hq using glue
  refine ⟨(∏ ab, s' ab) * ∏ b, s b, Sg.mul_mem (Sg.prod_mem fun _ _ => hs' _) (Sg.prod_mem fun _ _ => hs _),
    ⟨q, fun i i' => fn_ext fun x hx => ?_⟩, fun z i k h₁ h₂ => ?_⟩
  · obtain ⟨a, ha⟩ := cov x
    rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx, hq i a x hx.1 ha, hq i' a x hx.2 ha,
      ← gm_cocycle hL (𝟙 X) x hx.1 hx.2 (hle a ha), Units.val_mul, _root_.mul_assoc]
  · obtain ⟨a, ha⟩ := cov (φ z)
    have hm : φ z ∈ L.U i ⊓ L.U (j a) := ⟨h₁, hle a ha⟩
    show gs φ z _ (q i) = _
    rw [gs_stalkMap φ z _ h₁, hq i a _ h₁ ha, map_mul, map_mul, cst_stalkMap, ← gs_stalkMap φ z _ ha, ← gs_unit (𝟙 X) (φ z) _ hm,
      ← gs_stalkMap φ z _ hm, gs_unit φ z _ hm, hy₁ a z k ha h₂, tr z i (j a) k k h₁ (hle a ha) h₂ h₂, cst_mul]
    ring

end Loc

/- English proof (translation)
Take `⟨V, hV, b, hb⟩` from `hS _ P 1 le_rfl (IsLocalRing.closedPoint R)`. Establish `all : ∀ y : Sp R, y ∈ V` using `fun y => (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (Sp R)) hV)).mpr trivial`. Take `⟨n, hn⟩ : ∃ n : Sp R ⟶ V.toScheme, n ≫ V.ι = 𝟙 _` from `⟨IsOpenImmersion.lift V.ι (𝟙 _) (by rintro _ ⟨y, rfl⟩; rw [Scheme.Opens.range_ι]; exact all _), IsOpenImmersion.lift_fac _ _ _⟩`. Set `T` to `overRes (T := baseOver (Sp R)) V`. Set `t : Sp K ⟶ T.left` to `spMap g ≫ n`.

Establish `ht : (baseAt t).hom = spMap g` using `(Category.assoc _ _ _).trans ((congrArg (spMap g ≫ ·) ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans hn))).trans (Category.comp_id _))`. Set `ρ : P.A ⟶ T ⊗ P.A` to `lift (Over.homMk (P.A.hom ≫ n) ((Category.assoc _ _ _).trans ((congrArg (P.A.hom ≫ ·) ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans hn))).trans (Category.comp_id _)))) (𝟙 _)`. Establish `ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _` using `congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)`. Establish `ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom ≫ n` using `congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)`. Establish `hM` using `linComb_isLB P.L P.isLB (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ))`.

Take `⟨w, hw⟩` from `exists_iso_linComb (F := (snd T P.A).left) P.isLB (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ)) (fun U _ k => by simp)`. Take `⟨w', hw₂⟩` from `LBIso.chartPull (chartPullSec P.L _ ρ.left ρ₂) (chartPullPull _ ρ.left ρ.left rfl) (LBIso.symm ⟨w, hw⟩)`. Establish `i₀ : Fin (1 ^ P.g)` using `⟨0, by simp⟩`. Take `⟨β, hβ⟩` from `sec_pull_down ((isGen_iff w').1 hw₂) hM P.isLB (b i₀)`. Use `⟨β, fun h0 => ?_⟩` and prove the remaining obligations.

Set `h` to `homAt t ▷ P.A`. Establish `hh` using `whiskerRight_snd (homAt t) P.A`. Establish `pv : ∀ i j z, z ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) (baseAt t)).U j → gs (𝟙 _) z _ (resG _ (chart_le_res P.A P.L h hh _ j) ((h.left.app _).hom ((b i).f j))) = gs h.left z ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U j) ((b i).f j)` using `fun i j z hz => (gs_res (𝟙 _) z _ hz _).trans ((gs_pull (𝟙 _) h.left z _ (chart_le_res P.A P.L h hh _ j hz) _).trans (by rw [Category.id_comp]))`. Establish `hl : h.left ≫ (snd T P.A).left = (snd (baseAt t) P.A).left` using `congrArg (fun q => q.left) hh`. Set `b' : Fin (1 ^ P.g) → LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseAt t))` to `fun i => ⟨fun j => resG _ (chart_le_res P.A P.L h hh _ j) ((h.left.app _).hom ((b i).f j)), fun j j' => fn_ext fun z hz => by`.

Use `((gs_res (𝟙 _) z _ hz _).trans (pv i j z hz.1)).trans ((sec_trans (b i) h.left z (chart_le_res P.A P.L h hh _ j hz.1) (chart_le_res P.A P.L h hh _ j' hz.2)).trans (Eq.symm ((gs_mul (𝟙 _) z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 _) z _ hz _).trans (congrArg Units.val ((gm …` and prove the remaining obligations. Rewrite using `[Category.id_comp, ← hl]`. Use the proof step `rfl⟩`. Establish `: Nontrivial Γ((baseAt t).left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial`. Use `(hb K t b' fun i j => rfl).1.ne_zero i₀ (Subtype.ext (funext fun j => fn_ext fun z hz => ?_))` and prove the remaining obligations.

Establish `sq : (snd (baseAt t) P.A).left ≫ P.A.hom = (fst (baseAt t) P.A).left ≫ spMap g` using `pullback.condition.symm.trans (congrArg (_ ≫ ·) ht)`. Establish `k₁ : H.lift _ _ sq ≫ φ = (snd (baseAt t) P.A).left` using `H.lift_fst _ _ _`. Establish `e₁ : (snd (baseAt t) P.A).left ≫ ρ.left = h.left`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ n) sq).trans ((Category.assoc _ _ _).trans ?_))))` and prove the remaining obligations.

Conclude with `(congrArg (fun q => q.left) (whiskerRight_fst (homAt t) P.A)).symm`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans hl.symm))`. Take `⟨k, hk⟩` from `exists_chart P.isLB ((snd (baseAt t) P.A).left z)`. Establish `m₁` using `chart_le_res P.A P.L h hh _ j hz`. Establish `e₂` using `hβ _ (snd (baseAt t) P.A).left z j k ((congrArg (fun q => q z ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U j) e₁).mpr m₁) hk`.

Establish `hk' : φ (H.lift _ _ sq z) ∈ P.L.U k` using `(congrArg (fun q => q z ∈ P.L.U k) k₁).mpr hk`. Establish `e₀` using `(gs_pull (𝟙 A') φ (H.lift _ _ sq z) _ hk' (β.f k)).trans ((congrArg (fun q => gs q _ _ (β.f k)) (Category.id_comp φ)).trans (h0 _ k hk'))`. Establish `e₃ : gs (snd (baseAt t) P.A).left z _ (β.f k) = 0`. Rewrite using `[← k₁, ← gs_pull _ φ z _ hk', gs_stalkMap _ z _ hk', e₀, map_zero]`. Rewrite `e₂` using `[e₁, e₃, mul_zero]`.

Conclude with `((pv i₀ j z hz).trans e₂).trans (gs_zero (𝟙 _) z _ hz).symm`.
-/
theorem exists_sec_ne (hS : SecBaseChangeAnySt) {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (P : PolAV (Sp R))
    (g : R →+* K) {A' : Scheme.{0}} {p' : A' ⟶ Sp K} {φ : A' ⟶ P.A.left} (H : IsPullback φ p' P.A.hom (spMap g)) :
    ∃ β : LB.Sec P.L, ¬ ∀ y j, φ y ∈ P.L.U j → gs φ y _ (β.f j) = 0 := by
  obtain ⟨V, hV, b, hb⟩ := hS _ P 1 le_rfl (IsLocalRing.closedPoint R)
  have all : ∀ y : Sp R, y ∈ V := fun y =>
    (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (Sp R)) hV)).mpr trivial
  obtain ⟨n, hn⟩ : ∃ n : Sp R ⟶ V.toScheme, n ≫ V.ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift V.ι (𝟙 _) (by rintro _ ⟨y, rfl⟩; rw [Scheme.Opens.range_ι]; exact all _),
      IsOpenImmersion.lift_fac _ _ _⟩
  let T := overRes (T := baseOver (Sp R)) V
  let t : Sp K ⟶ T.left := spMap g ≫ n
  have ht : (baseAt t).hom = spMap g :=
    (Category.assoc _ _ _).trans ((congrArg (spMap g ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((Category.comp_id _).trans hn))).trans (Category.comp_id _))
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk (P.A.hom ≫ n) ((Category.assoc _ _ _).trans ((congrArg (P.A.hom ≫ ·)
    ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans hn))).trans (Category.comp_id _)))) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom ≫ n := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have hM := linComb_isLB P.L P.isLB (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ))
  obtain ⟨w, hw⟩ := exists_iso_linComb (F := (snd T P.A).left) P.isLB (K := Fin 1) (fun _ => (snd T P.A).left)
    (fun _ => ((1 : ℕ) : ℤ)) (fun U _ k => by simp)
  obtain ⟨w', hw₂⟩ := LBIso.chartPull (chartPullSec P.L _ ρ.left ρ₂) (chartPullPull _ ρ.left ρ.left rfl) (LBIso.symm ⟨w, hw⟩)
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  obtain ⟨β, hβ⟩ := sec_pull_down ((isGen_iff w').1 hw₂) hM P.isLB (b i₀)
  refine ⟨β, fun h0 => ?_⟩
  let h := homAt t ▷ P.A
  have hh := whiskerRight_snd (homAt t) P.A
  have pv : ∀ i j z, z ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) (baseAt t)).U j → gs (𝟙 _) z _
      (resG _ (chart_le_res P.A P.L h hh _ j) ((h.left.app _).hom ((b i).f j))) =
      gs h.left z ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U j) ((b i).f j) := fun i j z hz =>
    (gs_res (𝟙 _) z _ hz _).trans ((gs_pull (𝟙 _) h.left z _ (chart_le_res P.A P.L h hh _ j hz) _).trans
      (by rw [Category.id_comp]))
  have hl : h.left ≫ (snd T P.A).left = (snd (baseAt t) P.A).left := congrArg (fun q => q.left) hh
  let b' : Fin (1 ^ P.g) → LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseAt t)) := fun i =>
    ⟨fun j => resG _ (chart_le_res P.A P.L h hh _ j) ((h.left.app _).hom ((b i).f j)), fun j j' => fn_ext fun z hz => by
      refine ((gs_res (𝟙 _) z _ hz _).trans (pv i j z hz.1)).trans ((sec_trans (b i) h.left z
        (chart_le_res P.A P.L h hh _ j hz.1) (chart_le_res P.A P.L h hh _ j' hz.2)).trans (Eq.symm
        ((gs_mul (𝟙 _) z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 _) z _ hz _).trans (congrArg Units.val
          ((gm_linComb P.L _ _ (𝟙 _) z j j' hz.1 hz.2).trans ?_))) ((gs_res (𝟙 _) z _ hz _).trans (pv i j' z hz.2))))))
      rw [Category.id_comp, ← hl]; rfl⟩
  have : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  refine (hb K t b' fun i j => rfl).1.ne_zero i₀ (Subtype.ext (funext fun j => fn_ext fun z hz => ?_))
  have sq : (snd (baseAt t) P.A).left ≫ P.A.hom = (fst (baseAt t) P.A).left ≫ spMap g :=
    pullback.condition.symm.trans (congrArg (_ ≫ ·) ht)
  have k₁ : H.lift _ _ sq ≫ φ = (snd (baseAt t) P.A).left := H.lift_fst _ _ _
  have e₁ : (snd (baseAt t) P.A).left ≫ ρ.left = h.left := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ n) sq).trans ((Category.assoc _ _ _).trans ?_))))
      exact (congrArg (fun q => q.left) (whiskerRight_fst (homAt t) P.A)).symm
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans hl.symm))
  obtain ⟨k, hk⟩ := exists_chart P.isLB ((snd (baseAt t) P.A).left z)
  have m₁ := chart_le_res P.A P.L h hh _ j hz
  have e₂ := hβ _ (snd (baseAt t) P.A).left z j k
    ((congrArg (fun q => q z ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U j) e₁).mpr m₁) hk
  have hk' : φ (H.lift _ _ sq z) ∈ P.L.U k := (congrArg (fun q => q z ∈ P.L.U k) k₁).mpr hk
  have e₀ := (gs_pull (𝟙 A') φ (H.lift _ _ sq z) _ hk' (β.f k)).trans
    ((congrArg (fun q => gs q _ _ (β.f k)) (Category.id_comp φ)).trans (h0 _ k hk'))
  have e₃ : gs (snd (baseAt t) P.A).left z _ (β.f k) = 0 := by
    rw [← k₁, ← gs_pull _ φ z _ hk', gs_stalkMap _ z _ hk', e₀, map_zero]
  rw [e₁, e₃, mul_zero] at e₂
  exact ((pv i₀ j z hz).trans e₂).trans (gs_zero (𝟙 _) z _ hz).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {B : Type} [CommRing B]
  {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B}

/- English proof (translation)
Use `t.semi.smooth` as an intermediate fact. Take `⟨w, gw', -⟩` from `m.lin`. Take `⟨U, hU, hp, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x (IsLocalRing.closedPoint R)) trivial`. Use `t.semi.geomConnected` as an intermediate fact. Establish `: ConnectedSpace (Sp R)` using `{ isPreconnected_univ := isPreconnected_of_forall (IsLocalRing.closedPoint R) fun y _ => ⟨closure {y}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl, isPreconnected_singleton.closure⟩ toNonempty := ⟨IsLocalRing.closedPoint R⟩ }`.

Establish `: ConnectedSpace t.G.left` using `GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap`. Take `⟨d, hd⟩` from `exists_dim_of_preconnected t.G.hom (eSec t.G (IsLocalRing.closedPoint R))`. Take `⟨-, ws, gs', -⟩` from `t.sym`. Conclude with `exists_sec_ne hS { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB ample := relAmple_pull m.cart.1 o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') U hU (fun y => (congrArg (fun W => y ∈ W) (Scheme.preimage_eq_top_of_closedPoint_mem x hp)).mpr trivial) o.ample ktriv …`.
-/
theorem exists_sec_ne_obj (hS : SecBaseChangeAnySt) (o : Obj D l b s) {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
    {x : Sp R ⟶ X} {t : SAB H (Sp R)} (m : SABMap t o.t x) (g : R →+* K) {A' : Scheme.{0}} {p' : A' ⟶ Sp K}
    {φ : A' ⟶ t.G.left} (Hp : IsPullback φ p' t.G.hom (spMap g)) :
    ∃ β : LB.Sec t.PP.L, ¬ ∀ y j, φ y ∈ t.PP.L.U j → gs φ y _ (β.f j) = 0 := by
  have := t.semi.smooth
  obtain ⟨w, gw', -⟩ := m.lin
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x (IsLocalRing.closedPoint R)) trivial
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) :=
    { isPreconnected_univ := isPreconnected_of_forall (IsLocalRing.closedPoint R) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
          isPreconnected_singleton.closure⟩
      toNonempty := ⟨IsLocalRing.closedPoint R⟩ }
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (IsLocalRing.closedPoint R))
  obtain ⟨-, ws, gs', -⟩ := t.sym
  exact exists_sec_ne hS
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB
      ample := relAmple_pull m.cart.1 o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') U hU (fun y =>
        (congrArg (fun W => y ∈ W) (Scheme.preimage_eq_top_of_closedPoint_mem x hp)).mpr trivial) o.ample
      ktriv := kTriv_pull m.cart o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') o.ktriv
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 o.proper, ‹_›⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } g Hp

/- English proof (translation)
Introduce `h0`. Establish `hp : (RingHom.ker ψ).IsPrime` using `RingHom.ker_isPrime ψ`. Set `R` to `Localization.AtPrime (RingHom.ker ψ)`. Establish `hu : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y)` using `fun y => (Ne.isUnit y.2)`. Set `g : R →+* K` to `IsLocalization.lift hu`.

Establish `hg : spMap ψ = spMap g ≫ spMap (algebraMap S R)` using `by rw [← spMap_comp, IsLocalization.lift_comp]`. Take `⟨PP', cub, sym, adj, prim, m₁, -⟩` from `sabPull proved_CubePullSt (spMap (algebraMap S R)) t`. Take `⟨n, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m₁`. Establish `H₂ : IsPullback (m₁.cart.1.lift m.φ (t'.G.hom ≫ spMap g) (by rw [m.cart.1.w, hg, Category.assoc])) t'.G.hom _ (spMap g)` using `IsPullback.of_right (by rw [m₁.cart.1.lift_fst, ← hg]; exact m.cart.1) (m₁.cart.1.lift_snd _ _ _) m₁.cart.1`. Take `⟨β, hβ⟩` from `exists_sec_ne_obj hS o n g H₂`.

Take `⟨w₁, g₁, -⟩` from `m₁.lin`. Establish `: IsProper t.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) m₀.cart.1 o.proper`. Establish `: CompactSpace t.G.left` using `QuasiCompact.compactSpace_of_compactSpace t.G.hom`. Take `⟨a, ha, σ, hσ⟩` from `exists_extend (RingHom.ker ψ).primeCompl m₁.cart.1 t.PP.isLB PP'.isLB ((isGen_iff w₁).1 g₁) β`. Take `⟨c, hc⟩` from `hθ σ`.

Use `hβ fun y k hk => ?_` and prove the remaining obligations. Establish `k₁` using `m₁.cart.1.lift_fst m.φ (t'.G.hom ≫ spMap g) (by rw [m.cart.1.w, hg, Category.assoc])`. Generalize the expression as in `m₁.cart.1.lift m.φ (t'.G.hom ≫ spMap g) _ = r at hk k₁ ⊢`. Take `⟨j, hj⟩` from `exists_chart t.PP.isLB (m₁.φ (r y))`. Establish `hj' : m.φ y ∈ t.PP.L.U j` using `(congrArg (fun q => q y ∈ t.PP.L.U j) k₁).mp hj`.

Establish `e` using `congrArg (r.stalkMap y).hom (hσ (r y) j k hj hk)`. Establish `e₁ : (r.stalkMap y).hom (gs m₁.φ (r y) _ (σ.f j)) = 0`. Establish `e₂` using `(gs_pull (𝟙 _) m₁.φ (r y) _ hj (σ.f j)).trans (congrArg (fun q => gs q _ _ (σ.f j)) (Category.id_comp _))`. Rewrite using `[← e₂, ← gs_stalkMap r y _ hj, gs_pull r m₁.φ y _ hj, k₁, hc, gs_mul _ y _ hj', h0 y j hj', mul_zero]`. Rewrite `e` using `[e₁, map_mul, map_mul, cst_stalkMap, ← gs_stalkMap r y _ hk, ← Category.assoc, k₁, m.cart.1.w, cst_comp]`.

Establish `u₁ : IsUnit (cst t'.G.hom y (ψ a))` using `IsUnit.of_mul_eq_one (cst t'.G.hom y (ψ a)⁻¹) (by`. Rewrite using `[← cst_mul, mul_inv_cancel₀ ha, cst_one])`. Conclude with `((Units.isUnit _).map _).mul_right_eq_zero.1 (u₁.mul_right_eq_zero.1 e.symm)`.
-/
theorem gen_ne_zero (hS : SecBaseChangeAnySt) (o : Obj D l b s) {S K : Type} [CommRing S] [Field K] {x : Sp S ⟶ X}
    {t : SAB H (Sp S)} (m₀ : SABMap t o.t x) (θ : LB.Sec t.PP.L)
    (hθ : ∀ σ : LB.Sec t.PP.L, ∃ a : S, ∀ i, σ.f i = constFn t.G.hom _ a * θ.f i) (ψ : S →+* K) {t' : SAB H (Sp K)}
    (m : SABMap t' t (spMap ψ)) : ¬ ∀ y j, m.φ y ∈ t.PP.L.U j → gs m.φ y _ (θ.f j) = 0 := by
  intro h0
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime (RingHom.ker ψ)
  have hu : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y => (Ne.isUnit y.2)
  let g : R →+* K := IsLocalization.lift hu
  have hg : spMap ψ = spMap g ≫ spMap (algebraMap S R) := by rw [← spMap_comp, IsLocalization.lift_comp]
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull proved_CubePullSt (spMap (algebraMap S R)) t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m₁
  have H₂ : IsPullback (m₁.cart.1.lift m.φ (t'.G.hom ≫ spMap g) (by rw [m.cart.1.w, hg, Category.assoc])) t'.G.hom _
      (spMap g) := IsPullback.of_right (by rw [m₁.cart.1.lift_fst, ← hg]; exact m.cart.1) (m₁.cart.1.lift_snd _ _ _) m₁.cart.1
  obtain ⟨β, hβ⟩ := exists_sec_ne_obj hS o n g H₂
  obtain ⟨w₁, g₁, -⟩ := m₁.lin
  have : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m₀.cart.1 o.proper
  have : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  obtain ⟨a, ha, σ, hσ⟩ := exists_extend (RingHom.ker ψ).primeCompl m₁.cart.1 t.PP.isLB PP'.isLB ((isGen_iff w₁).1 g₁) β
  obtain ⟨c, hc⟩ := hθ σ
  refine hβ fun y k hk => ?_
  have k₁ := m₁.cart.1.lift_fst m.φ (t'.G.hom ≫ spMap g) (by rw [m.cart.1.w, hg, Category.assoc])
  generalize m₁.cart.1.lift m.φ (t'.G.hom ≫ spMap g) _ = r at hk k₁ ⊢
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m₁.φ (r y))
  have hj' : m.φ y ∈ t.PP.L.U j := (congrArg (fun q => q y ∈ t.PP.L.U j) k₁).mp hj
  have e := congrArg (r.stalkMap y).hom (hσ (r y) j k hj hk)
  have e₁ : (r.stalkMap y).hom (gs m₁.φ (r y) _ (σ.f j)) = 0 := by
    have e₂ := (gs_pull (𝟙 _) m₁.φ (r y) _ hj (σ.f j)).trans (congrArg (fun q => gs q _ _ (σ.f j)) (Category.id_comp _))
    rw [← e₂, ← gs_stalkMap r y _ hj, gs_pull r m₁.φ y _ hj, k₁, hc, gs_mul _ y _ hj', h0 y j hj', mul_zero]
  rw [e₁, map_mul, map_mul, cst_stalkMap, ← gs_stalkMap r y _ hk, ← Category.assoc, k₁, m.cart.1.w, cst_comp] at e
  have u₁ : IsUnit (cst t'.G.hom y (ψ a)) := IsUnit.of_mul_eq_one (cst t'.G.hom y (ψ a)⁻¹) (by
    rw [← cst_mul, mul_inv_cancel₀ ha, cst_one])
  exact ((Units.isUnit _).map _).mul_right_eq_zero.1 (u₁.mul_right_eq_zero.1 e.symm)

/- English proof (translation)
Take `⟨n, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m`. Take `⟨β, hb⟩` from `globalSections_rank_one_fibre hT amplePt o n`. Take `⟨a₀, ha₀, -⟩` from `hb σ'`. Establish `h₀ : a₀ ≠ 0` using `fun h => gen_ne_zero hS o m₀ θ hθ ψ m fun y j hj => by`. Take `⟨k, hk⟩` from `exists_chart t'.PP.isLB y`.

Rewrite using `[hσ y j k hj hk, (sec_eq_iff _ _ _ _).1 ha₀ k y hk, h, cst, map_zero, gs_zero _ y ⊤ trivial, zero_mul, mul_zero]`. Take `⟨a, ha, hu⟩` from `hb s'`. Use `⟨a * a₀⁻¹, (sec_eq_iff _ _ _ _).2 fun k y hy => ?_, fun a' ha' => ?_⟩` and prove the remaining obligations. Rewrite using `[(sec_eq_iff _ _ _ _).1 ha k y hy, (sec_eq_iff _ _ _ _).1 ha₀ k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel_right₀ h₀]`. Rewrite using `[← hu (a' * a₀) ((sec_eq_iff _ _ _ _).2 fun k y hy => by`.

Rewrite using `[(sec_eq_iff _ _ _ _).1 ha' k y hy, (sec_eq_iff _ _ _ _).1 ha₀ k y hy, cst_mul, _root_.mul_assoc]),`. Use `mul_inv_cancel_right₀ h₀]`.
-/
theorem gen_baseChange (hS : SecBaseChangeAnySt) (hT : SecTwistSt) (o : Obj D l b s) {S K : Type} [CommRing S] [Field K]
    {x : Sp S ⟶ X} {t : SAB H (Sp S)} (m₀ : SABMap t o.t x) (θ : LB.Sec t.PP.L)
    (hθ : ∀ σ : LB.Sec t.PP.L, ∃ a : S, ∀ i, σ.f i = constFn t.G.hom _ a * θ.f i) (ψ : S →+* K) {t' : SAB H (Sp K)}
    (m : SABMap t' t (spMap ψ)) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} (σ' : LB.Sec t'.PP.L)
    (hσ : ∀ y j k, m.φ y ∈ t.PP.L.U j → y ∈ t'.PP.L.U k →
      gs m.φ y _ (θ.f j) = (gw w (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) (s' : LB.Sec t'.PP.L) :
    ∃! a : K, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := by
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m
  obtain ⟨β, hb⟩ := globalSections_rank_one_fibre hT amplePt o n
  obtain ⟨a₀, ha₀, -⟩ := hb σ'
  have h₀ : a₀ ≠ 0 := fun h => gen_ne_zero hS o m₀ θ hθ ψ m fun y j hj => by
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB y
    rw [hσ y j k hj hk, (sec_eq_iff _ _ _ _).1 ha₀ k y hk, h, cst, map_zero, gs_zero _ y ⊤ trivial, zero_mul, mul_zero]
  obtain ⟨a, ha, hu⟩ := hb s'
  refine ⟨a * a₀⁻¹, (sec_eq_iff _ _ _ _).2 fun k y hy => ?_, fun a' ha' => ?_⟩
  · rw [(sec_eq_iff _ _ _ _).1 ha k y hy, (sec_eq_iff _ _ _ _).1 ha₀ k y hy, ← _root_.mul_assoc, ← cst_mul,
      inv_mul_cancel_right₀ h₀]
  · rw [← hu (a' * a₀) ((sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 ha' k y hy, (sec_eq_iff _ _ _ _).1 ha₀ k y hy, cst_mul, _root_.mul_assoc]),
      mul_inv_cancel_right₀ h₀]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
