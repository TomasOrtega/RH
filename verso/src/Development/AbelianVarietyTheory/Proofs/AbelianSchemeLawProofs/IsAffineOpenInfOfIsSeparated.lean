import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeRTensorOfForallDual

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KuennethOne

section General

open TopologicalSpace TensorProduct

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem lid_rTensor_lTensor {R C A B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] A)
    (w : C ⊗[R] B) : TensorProduct.lid R A (l.rTensor A (f.lTensor C w)) =
      f (TensorProduct.lid R B (l.rTensor B w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [mul_comm]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem apply_lid_rTensor {R C B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] R) (w : C ⊗[R] B) :
    f (TensorProduct.lid R B (l.rTensor B w)) = l (TensorProduct.rid R C (f.lTensor C w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
  (H : IsPullback p q iX iY) {I : Type} {V : I → Z.Opens} {φ : ∀ a b, Γ(Z, V a ⊓ V b)}

include H

/- English proof (translation)
Establish `: IsAffine _` using `isAffineOpen_top S`. Establish `: IsAffine _` using `hU`. Establish `: IsAffine _` using `hW`. Conclude with `.of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl).isoPullback.hom`.
-/
theorem isAffineOpen_prod [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
  have : IsAffine _ := isAffineOpen_top S
  have : IsAffine _ := hU
  have : IsAffine _ := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
    rfl).isoPullback.hom

/- English proof (translation)
Take `⟨I₀, hI₀, e⟩` from `isCompact_iff_finite_and_eq_biUnion_affineOpens.mp (show IsCompact ((⊤ : X.Opens) : Set X) by simpa using isCompact_univ)`. Use `hI₀.to_subtype` as an intermediate fact. Set `U : I₀ → X.Opens` to `fun i => i.1.1`. Establish `hU : ∀ i, IsAffineOpen (U i)` using `fun i => i.1.2`. Establish `hUtop : iSup U = ⊤` using `by rw [e, iSup_subtype]`.

Set `U₂ : I₀ × I₀ → X.Opens` to `fun k => U k.1 ⊓ U k.2`. Establish `hU₂ : ∀ k, IsAffineOpen (U₂ k)` using `fun k => hX _ _ (hU _) (hU _)`. Establish `l1 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.1` using `fun k => p.preimage_mono inf_le_left`. Establish `l2 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.2` using `fun k => p.preimage_mono inf_le_right`. Use `choose σ hσ using fun (i : I₀) (j : Y.affineOpens) => exists_splits_of_isAffineOpen hV hφ (isAffineOpen_prod H (hU i) j.2)`.

Use `choose c hc using fun (j : Y.affineOpens) (k : I₀ × I₀) => exists_isDiff hV (hσ k.1 j) (hσ k.2 j) (P := p ⁻¹ᵁ U₂ k ⊓ q ⁻¹ᵁ j.1) (inf_le_inf_right _ (l1 k)) (inf_le_inf_right _ (l2 k))`. Use `choose z hz using fun j : Y.affineOpens => MM_surj H hU₂ j.2 (c j)`. Establish `hcompat : ∀ (j k : Y.affineOpens), ∃ w, (rsA iY (inf_le_left : j.1 ⊓ k.1 ≤ j.1)).toLinearMap.lTensor _ (z j) - (rsA iY inf_le_right).toLinearMap.lTensor _ (z k) - (dlt iX U).rTensor _ w = 0`. Introduce `j k`. Establish `hW'` using `hY _ _ j.2 k.2`.

Establish `m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1` using `q.preimage_mono inf_le_left`. Establish `m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1` using `q.preimage_mono inf_le_right`. Use `choose d hd using fun i : I₀ => exists_isDiff hV (hσ i j) (hσ i k) (P := p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1)) (inf_le_inf_left _ m1) (inf_le_inf_left _ m2)`. Take `⟨w, hw⟩` from `MM_surj H hU hW' d`. Use `⟨w, MM_inj H hU₂ hW' _ fun m => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_sub, MM_lTensor, MM_lTensor, MM_dlt]`. Establish `a1` using `congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m1)) (hz j m)`. Establish `a2` using `congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m2)) (hz k m)`. Establish `a3` using `congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l1 m))) (hw m.1)`. Establish `a4` using `congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l2 m))) (hw m.2)`.

Rewrite `a1`, `a2`, `a3`, `a4` using `[rs_MM]`. Rewrite using `[a1, a2, a3, a4]`. Use `loc V (by rw [hV]; exact le_top) _ _ fun a => ?_` and prove the remaining obligations. Establish `b1` using `hc j m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a) (inf_le_left.trans (inf_le_inf_left _ m1)) inf_le_right`. Establish `b2` using `hc k m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a) (inf_le_left.trans (inf_le_inf_left _ m2)) inf_le_right`.

Establish `b3` using `hd m.1 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a) (inf_le_left.trans (inf_le_inf_right _ (l1 m))) inf_le_right`. Establish `b4` using `hd m.2 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a) (inf_le_left.trans (inf_le_inf_right _ (l2 m))) inf_le_right`. Simplify using `only [map_sub, map_zero, rs_rs]`. Take the linear combination `b1 - b2 - b3 + b4`. Establish `hN : ∀ (N : X.Opens), N ≤ s ⁻¹ᵁ (p ⁻¹ᵁ N ⊓ q ⁻¹ᵁ W₀.1)`.

Introduce `N`. Rewrite using `[s.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hs, hs']`. Conclude with `le_inf le_rfl (le_top.trans (iX.preimage_mono hW₀))`. Take `⟨x, hx⟩` from `pull_coboundary hV s ρ hρ (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W₀.1) (fun i => σ i W₀) (fun i => hσ i W₀) U (fun i => hN _)`. Establish `hz₀ : TensorProduct.rid _ _ ((evA y hy W₀.1 hW₀).toLinearMap.lTensor _ (z W₀)) = dlt iX U x`.

Use function extensionality and compare the values at `m`. Use `(section_MM H hy hs hs' U₂ W₀.1 hW₀ m _ inf_le_left inf_le_right (hN _) (z W₀)).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hz W₀ m]`. Conclude with `hx m.1 m.2 _ _ _ _ (hc W₀ m) _ inf_le_left inf_le_right _`. Establish `hl : ∀ l : (∀ k, Fn iX (U₂ k)) →ₗ[Γ(S, ⊤)] Γ(S, ⊤), l ∘ₗ dlt iX U = 0 → TensorProduct.lid _ _ (l.rTensor _ (z W)) = 0`.

Introduce `l hl`. Set `b : ∀ j : Y.affineOpens, Fn iY j.1` to `fun j => TensorProduct.lid _ _ (l.rTensor _ (z j))`. Take `⟨β, hβ⟩` from `glue ⊤ (fun j : Y.affineOpens => j.1) (fun _ => le_top) (iSup_affineOpens_eq_top Y).ge b (by`. Introduce `j k`. Take `⟨w, hw⟩` from `hcompat j k`.

Use `congrArg (fun t => TensorProduct.lid _ _ (l.rTensor _ t)) hw` as an intermediate fact. Simplify using `only [map_sub, map_zero] at this`. Rewrite `this` using `[lid_rTensor_lTensor, lid_rTensor_lTensor, ← LinearMap.rTensor_comp_apply, hl]`. Simplify using `only [LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero, sub_zero] at this`. Conclude with `sub_eq_zero.mp this)`.

Take `⟨r, rfl⟩` from `hiY β`. Establish `hb : ∀ j : Y.affineOpens, b j = algebraMap Γ(S, ⊤) (Fn iY j.1) r`. Introduce `j`. Use `(hβ j).symm.trans ?_` and prove the remaining obligations. Establish `: iY.appTop = iY.appLE ⊤ ⊤ le_top` using `iY.app_eq_appLE (U := ⊤)`.

Rewrite using `[this]`. Conclude with `rs_appLE iY _ _ r`. Establish `hr : r = 0`. Establish `h1` using `apply_lid_rTensor l (evA y hy W₀.1 hW₀).toLinearMap (z W₀)`. Rewrite `h1` using `[hz₀, show l (dlt iX U x) = 0 from LinearMap.congr_fun hl x]`.

Establish `h2 : evA y hy W₀.1 hW₀ (b W₀) = 0` using `h1`. Rewrite `h2` using `[hb, AlgHom.commutes]`. Then use the resulting hypothesis. Use `hb W` as an intermediate fact. Rewrite `this` using `[hr, map_zero]`. Then use the resulting hypothesis. Take `⟨w, hw⟩` from `mem_range_rTensor_of_forall_dual hR (dlt iX U) (z W) hl`.

Use `splits_glue (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W.1) (fun i => σ i W) (fun i => hσ i W) (fun i => MM H U W.1 i _ inf_le_left inf_le_right w) ?_ _ ?_` and prove the remaining obligations. Introduce `i k a M hi hk ha`. Establish `hM : M ≤ p ⁻¹ᵁ U₂ (i, k) ⊓ q ⁻¹ᵁ W.1`. Use `le_inf ?_ (hi.trans inf_le_right)` and prove the remaining obligations. Rewrite using `[p.preimage_inf]`.

Conclude with `le_inf (hi.trans inf_le_left) (hk.trans inf_le_left)`. Establish `b1` using `hc W (i, k) a M hM ha`. Rewrite `b1` using `[← hz W (i, k), rs_MM, ← hw, MM_dlt]`. Rewrite using `[rs_MM, rs_MM]`. Conclude with `b1.symm`.

Rewrite using `[← iSup_inf_eq, ← p.preimage_iSup, hUtop]`. Conclude with `le_inf le_top le_rfl`.
-/
theorem exists_splits_preimage [IsAffine S] (hR : IsField Γ(S, ⊤)) [CompactSpace X]
    (hX : ∀ U U' : X.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiY : Function.Surjective iY.appTop.hom)
    {y : S ⟶ Y} (hy : y ≫ iY = 𝟙 S) {s : X ⟶ Z} (hs : s ≫ p = 𝟙 X) (hs' : s ≫ q = iX ≫ y)
    (W₀ : Y.affineOpens) (hW₀ : ⊤ ≤ y ⁻¹ᵁ W₀.1)
    (hV : ⨆ a, V a = ⊤) (hφ : IsCocycle V φ) (ρ : ∀ a, Γ(X, s ⁻¹ᵁ V a))
    (hρ : ∀ a b, (s.app (V a ⊓ V b)).hom (φ a b) =
      rs (s.preimage_mono inf_le_left) (ρ a) - rs (s.preimage_mono inf_le_right) (ρ b))
    (W : Y.affineOpens) : ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ := by
  obtain ⟨I₀, hI₀, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact ((⊤ : X.Opens) : Set X) by simpa using isCompact_univ)
  have := hI₀.to_subtype
  let U : I₀ → X.Opens := fun i => i.1.1
  have hU : ∀ i, IsAffineOpen (U i) := fun i => i.1.2
  have hUtop : iSup U = ⊤ := by rw [e, iSup_subtype]
  let U₂ : I₀ × I₀ → X.Opens := fun k => U k.1 ⊓ U k.2
  have hU₂ : ∀ k, IsAffineOpen (U₂ k) := fun k => hX _ _ (hU _) (hU _)
  have l1 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.1 := fun k => p.preimage_mono inf_le_left
  have l2 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.2 := fun k => p.preimage_mono inf_le_right
  choose σ hσ using fun (i : I₀) (j : Y.affineOpens) =>
    exists_splits_of_isAffineOpen hV hφ (isAffineOpen_prod H (hU i) j.2)
  choose c hc using fun (j : Y.affineOpens) (k : I₀ × I₀) =>
    exists_isDiff hV (hσ k.1 j) (hσ k.2 j) (P := p ⁻¹ᵁ U₂ k ⊓ q ⁻¹ᵁ j.1)
      (inf_le_inf_right _ (l1 k)) (inf_le_inf_right _ (l2 k))
  choose z hz using fun j : Y.affineOpens => MM_surj H hU₂ j.2 (c j)
  have hcompat : ∀ (j k : Y.affineOpens), ∃ w,
      (rsA iY (inf_le_left : j.1 ⊓ k.1 ≤ j.1)).toLinearMap.lTensor _ (z j) -
        (rsA iY inf_le_right).toLinearMap.lTensor _ (z k) - (dlt iX U).rTensor _ w = 0 := by
    intro j k
    have hW' := hY _ _ j.2 k.2
    have m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    choose d hd using fun i : I₀ => exists_isDiff hV (hσ i j) (hσ i k)
      (P := p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1)) (inf_le_inf_left _ m1) (inf_le_inf_left _ m2)
    obtain ⟨w, hw⟩ := MM_surj H hU hW' d
    refine ⟨w, MM_inj H hU₂ hW' _ fun m => ?_⟩
    rw [map_sub, map_sub, MM_lTensor, MM_lTensor, MM_dlt]
    have a1 := congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m1)) (hz j m)
    have a2 := congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m2)) (hz k m)
    have a3 := congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l1 m))) (hw m.1)
    have a4 := congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l2 m))) (hw m.2)
    rw [rs_MM] at a1 a2 a3 a4
    rw [a1, a2, a3, a4]
    refine loc V (by rw [hV]; exact le_top) _ _ fun a => ?_
    have b1 := hc j m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_left _ m1)) inf_le_right
    have b2 := hc k m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_left _ m2)) inf_le_right
    have b3 := hd m.1 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_right _ (l1 m))) inf_le_right
    have b4 := hd m.2 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_right _ (l2 m))) inf_le_right
    simp only [map_sub, map_zero, rs_rs]
    linear_combination b1 - b2 - b3 + b4
  have hN : ∀ (N : X.Opens), N ≤ s ⁻¹ᵁ (p ⁻¹ᵁ N ⊓ q ⁻¹ᵁ W₀.1) := by
    intro N
    rw [s.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hs, hs']
    exact le_inf le_rfl (le_top.trans (iX.preimage_mono hW₀))
  obtain ⟨x, hx⟩ := pull_coboundary hV s ρ hρ (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W₀.1)
    (fun i => σ i W₀) (fun i => hσ i W₀) U (fun i => hN _)
  have hz₀ : TensorProduct.rid _ _ ((evA y hy W₀.1 hW₀).toLinearMap.lTensor _ (z W₀)) =
      dlt iX U x := by
    funext m
    refine (section_MM H hy hs hs' U₂ W₀.1 hW₀ m _ inf_le_left inf_le_right (hN _) (z W₀)).symm.trans ?_
    rw [hz W₀ m]
    exact hx m.1 m.2 _ _ _ _ (hc W₀ m) _ inf_le_left inf_le_right _
  have hl : ∀ l : (∀ k, Fn iX (U₂ k)) →ₗ[Γ(S, ⊤)] Γ(S, ⊤), l ∘ₗ dlt iX U = 0 →
      TensorProduct.lid _ _ (l.rTensor _ (z W)) = 0 := by
    intro l hl
    let b : ∀ j : Y.affineOpens, Fn iY j.1 := fun j => TensorProduct.lid _ _ (l.rTensor _ (z j))
    obtain ⟨β, hβ⟩ := glue ⊤ (fun j : Y.affineOpens => j.1) (fun _ => le_top)
      (iSup_affineOpens_eq_top Y).ge b (by
        intro j k
        obtain ⟨w, hw⟩ := hcompat j k
        have := congrArg (fun t => TensorProduct.lid _ _ (l.rTensor _ t)) hw
        simp only [map_sub, map_zero] at this
        rw [lid_rTensor_lTensor, lid_rTensor_lTensor, ← LinearMap.rTensor_comp_apply, hl] at this
        simp only [LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero, sub_zero] at this
        exact sub_eq_zero.mp this)
    obtain ⟨r, rfl⟩ := hiY β
    have hb : ∀ j : Y.affineOpens, b j = algebraMap Γ(S, ⊤) (Fn iY j.1) r := by
      intro j
      refine (hβ j).symm.trans ?_
      have : iY.appTop = iY.appLE ⊤ ⊤ le_top := iY.app_eq_appLE (U := ⊤)
      rw [this]
      exact rs_appLE iY _ _ r
    have hr : r = 0 := by
      have h1 := apply_lid_rTensor l (evA y hy W₀.1 hW₀).toLinearMap (z W₀)
      rw [hz₀, show l (dlt iX U x) = 0 from LinearMap.congr_fun hl x] at h1
      have h2 : evA y hy W₀.1 hW₀ (b W₀) = 0 := h1
      rwa [hb, AlgHom.commutes] at h2
    have := hb W
    rwa [hr, map_zero] at this
  obtain ⟨w, hw⟩ := mem_range_rTensor_of_forall_dual hR (dlt iX U) (z W) hl
  refine splits_glue (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W.1) (fun i => σ i W) (fun i => hσ i W)
    (fun i => MM H U W.1 i _ inf_le_left inf_le_right w) ?_ _ ?_
  · intro i k a M hi hk ha
    have hM : M ≤ p ⁻¹ᵁ U₂ (i, k) ⊓ q ⁻¹ᵁ W.1 := by
      refine le_inf ?_ (hi.trans inf_le_right)
      rw [p.preimage_inf]
      exact le_inf (hi.trans inf_le_left) (hk.trans inf_le_left)
    have b1 := hc W (i, k) a M hM ha
    rw [← hz W (i, k), rs_MM, ← hw, MM_dlt] at b1
    rw [rs_MM, rs_MM]
    exact b1.symm
  · rw [← iSup_inf_eq, ← p.preimage_iSup, hUtop]
    exact le_inf le_top le_rfl

/- English proof (translation)
Use `choose τ hτ using hτ`. Establish `hN : ∀ N : Y.Opens, N ≤ t ⁻¹ᵁ (q ⁻¹ᵁ N)`. Introduce `N`. Rewrite using `[← Scheme.Hom.comp_preimage, ht]`. Conclude with `le_rfl`.

Establish `hN' : ∀ N : Y.Opens, N ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ N` using `fun N => le_rfl`. Take `⟨x, hx⟩` from `pull_coboundary hV t ρ hρ (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ (fun j => j.1) (fun j => hN _)`. Use `splits_glue (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ (fun j => (q.appLE j.1 _ le_rfl).hom (x j)) ?_ ⊤ ?_` and prove the remaining obligations. Introduce `j k a M hj hk ha`. Establish `hW'` using `hY _ _ j.2 k.2`.

Establish `m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1` using `q.preimage_mono inf_le_left`. Establish `m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1` using `q.preimage_mono inf_le_right`. Take `⟨e, he⟩` from `exists_isDiff hV (hτ j) (hτ k) m1 m2`. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := j.1 ⊓ k.1) (UX := ⊤) (UY := q ⁻¹ᵁ (j.1 ⊓ k.1)) le_top le_top (by simp)).1 (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _) hW' (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ))`. Establish `: IsIso (iX.appLE ⊤ ⊤ le_top)`.

Establish `e : iX.appTop = iX.appLE ⊤ ⊤ le_top` using `iX.app_eq_appLE (U := ⊤)`. Rewrite using `[← e]`. Conclude with `(ConcreteCategory.isIso_iff_bijective _).mpr hiX`. Establish `hiso` using `po.isIso_inr_of_isIso`. Take `⟨u, hu⟩` from `(ConcreteCategory.bijective_of_isIso (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl)).2 e`.

Establish `hu' : (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl).hom u = e` using `hu`. Establish `h1` using `hx j k _ m1 m2 e he (j.1 ⊓ k.1) inf_le_left inf_le_right (hN _)`. Rewrite `h1` using `[← hu', appLE_appLE t q _ ht _ _ (hN' _), id_appLE, rs_self]`. Establish `hM : M ≤ q ⁻¹ᵁ (j.1 ⊓ k.1)` using `by rw [q.preimage_inf]; exact le_inf hj hk`. Establish `h2` using `he a M hM ha`.

Rewrite `h2` using `[← hu', h1]`. Simplify using `only [map_sub, appLE_rs, rs_appLE] at h2 ⊢`. Conclude with `h2.symm`. Rewrite using `[← q.preimage_iSup, iSup_affineOpens_eq_top]`. Conclude with `le_top`.
-/
theorem exists_splits_top [IsAffine S] [Flat iY] [CompactSpace X] [QuasiSeparatedSpace X]
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiX : Function.Bijective iX.appTop.hom) {t : Y ⟶ Z} (ht : t ≫ q = 𝟙 Y)
    (hV : ⨆ a, V a = ⊤) (ρ : ∀ a, Γ(Y, t ⁻¹ᵁ V a))
    (hρ : ∀ a b, (t.app (V a ⊓ V b)).hom (φ a b) =
      rs (t.preimage_mono inf_le_left) (ρ a) - rs (t.preimage_mono inf_le_right) (ρ b))
    (hτ : ∀ W : Y.affineOpens, ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ) : ∃ χ, Splits V φ ⊤ χ := by
  choose τ hτ using hτ
  have hN : ∀ N : Y.Opens, N ≤ t ⁻¹ᵁ (q ⁻¹ᵁ N) := by
    intro N
    rw [← Scheme.Hom.comp_preimage, ht]
    exact le_rfl
  have hN' : ∀ N : Y.Opens, N ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ N := fun N => le_rfl
  obtain ⟨x, hx⟩ := pull_coboundary hV t ρ hρ (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => j.1) (fun j => hN _)
  refine splits_glue (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => (q.appLE j.1 _ le_rfl).hom (x j)) ?_ ⊤ ?_
  · intro j k a M hj hk ha
    have hW' := hY _ _ j.2 k.2
    have m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    obtain ⟨e, he⟩ := exists_isDiff hV (hτ j) (hτ k) m1 m2
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := j.1 ⊓ k.1) (UX := ⊤)
      (UY := q ⁻¹ᵁ (j.1 ⊓ k.1)) le_top le_top (by simp)).1
      (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _) hW'
        (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ))
    have : IsIso (iX.appLE ⊤ ⊤ le_top) := by
      have e : iX.appTop = iX.appLE ⊤ ⊤ le_top := iX.app_eq_appLE (U := ⊤)
      rw [← e]
      exact (ConcreteCategory.isIso_iff_bijective _).mpr hiX
    have hiso := po.isIso_inr_of_isIso
    obtain ⟨u, hu⟩ := (ConcreteCategory.bijective_of_isIso
      (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl)).2 e
    have hu' : (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl).hom u = e := hu
    have h1 := hx j k _ m1 m2 e he (j.1 ⊓ k.1) inf_le_left inf_le_right (hN _)
    rw [← hu', appLE_appLE t q _ ht _ _ (hN' _), id_appLE, rs_self] at h1
    have hM : M ≤ q ⁻¹ᵁ (j.1 ⊓ k.1) := by rw [q.preimage_inf]; exact le_inf hj hk
    have h2 := he a M hM ha
    rw [← hu', h1] at h2
    simp only [map_sub, appLE_rs, rs_appLE] at h2 ⊢
    exact h2.symm
  · rw [← q.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top

end General

/- English proof (translation)
Establish `: X.IsSeparated` using `⟨by rw [← terminal.comp_from f]; infer_instance⟩`. Conclude with `hU.inf hU'`.
-/
theorem isAffineOpen_inf_of_isSeparated {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact hU.inf hU'

/- English proof (translation)
Introduce `K _ X Y x₀ y₀ sX qX sY qY bX bY I V hV φ hφ ⟨ρX, hρX⟩ ⟨ρY, hρY⟩`. Establish `H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom` using `IsPullback.of_hasPullback X.hom Y.hom`. Establish `hR : IsField Γ(Spec (CommRingCat.of K), ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)`. Establish `: CompactSpace X.left` using `QuasiCompact.compactSpace_of_compactSpace X.hom`. Establish `: QuasiSeparatedSpace X.left` using `(quasiSeparated_iff_quasiSeparatedSpace X.hom).mp inferInstance`.

Establish `: Flat Y.hom` using `inferInstance`. Establish `hco : IsCocycle V φ`. Introduce `a b d N ha hb hd`. Use `congrArg (rs (le_inf (le_inf ha hb) hd)) (hφ a b d)` as an intermediate fact. Rewrite `this` using `[map_add]`.

Conclude with `(congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm.trans (this.trans (rs_rs _ _ _))`. Set `y : Spec (CommRingCat.of K) ⟶ Y.left` to `y₀.left`. Establish `hy : y ≫ Y.hom = 𝟙 _` using `Over.w y₀`. Establish `hs : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (fst X Y).left = 𝟙 _`. Rewrite using `[← Over.comp_left, lift_fst]`.

Both sides reduce to the same expression. Establish `hs' : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (snd X Y).left = X.hom ≫ y`. Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Establish `ht : (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ≫ (snd X Y).left = 𝟙 _`.

Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨W₀, hW₀⟩ : ∃ W₀ : Y.left.affineOpens, ⊤ ≤ y ⁻¹ᵁ W₀.1 := by`. Establish `: y default ∈ ⨆ W : Y.left.affineOpens, W.1`. Rewrite using `[iSup_affineOpens_eq_top]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨W, hW⟩` from `TopologicalSpace.Opens.mem_iSup.mp this`. Use `⟨W, fun z _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim z default]`. Conclude with `hW`.

Take `⟨χ, hχ⟩` from `exists_splits_top H (isAffineOpen_inf_of_isSeparated Y.hom) bX ht hV ρY hρY (exists_splits_preimage H hR (isAffineOpen_inf_of_isSeparated X.hom) (isAffineOpen_inf_of_isSeparated Y.hom) bY.2 hy hs hs' W₀ hW₀ hV hco ρX hρX)`. Use `⟨fun a => rs (le_inf le_top le_rfl) (χ a), fun a b => ?_⟩` and prove the remaining obligations. Use `hχ a b (V a ⊓ V b) le_top inf_le_left inf_le_right` as an intermediate fact. Rewrite `this` using `[rs_self]`. Conclude with `this.trans (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm`.
-/
theorem kuenneth_injective :
    ∀ (K : Type) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → Function.Bijective X.hom.appTop.hom → Function.Bijective Y.hom.appTop.hom → ∀ (I : Type) (V : I → (X ⊗ Y).left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ((X ⊗ Y).left, V a ⊓ V b), (∀ a b d, ((X ⊗ Y).left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b)).op).hom (φ a b) + ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d)).op).hom (φ b d) = ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d)).op).hom (φ a d)) → (∃ ψ : ∀ a, Γ(X.left, (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a), ∀ a b, ((lift (𝟙 X) (toUnit X ≫ y₀)).left.app (V a ⊓ V b)).hom (φ a b) = (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → (∃ ψ : ∀ a, Γ(Y.left, (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a), ∀ a b, ((lift (toUnit Y ≫ x₀) (𝟙 Y)).left.app (V a ⊓ V b)).hom (φ a b) = (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → ∃ ψ : ∀ a, Γ((X ⊗ Y).left, V a), ∀ a b, φ a b = ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) - ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_right).op).hom (ψ b) := by
  intro K _ X Y x₀ y₀ sX qX sY qY bX bY I V hV φ hφ ⟨ρX, hρX⟩ ⟨ρY, hρY⟩
  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have hR : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := (quasiSeparated_iff_quasiSeparatedSpace X.hom).mp inferInstance
  have : Flat Y.hom := inferInstance
  have hco : IsCocycle V φ := by
    intro a b d N ha hb hd
    have := congrArg (rs (le_inf (le_inf ha hb) hd)) (hφ a b d)
    rw [map_add] at this
    exact (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm.trans (this.trans (rs_rs _ _ _))
  let y : Spec (CommRingCat.of K) ⟶ Y.left := y₀.left
  have hy : y ≫ Y.hom = 𝟙 _ := Over.w y₀
  have hs : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (fst X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hs' : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (snd X Y).left = X.hom ≫ y := by
    rw [← Over.comp_left, lift_snd]; rfl
  have ht : (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ≫ (snd X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Y.left.affineOpens, ⊤ ≤ y ⁻¹ᵁ W₀.1 := by
    have : y default ∈ ⨆ W : Y.left.affineOpens, W.1 := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine ⟨W, fun z _ => ?_⟩
    rw [Subsingleton.elim z default]
    exact hW
  obtain ⟨χ, hχ⟩ := exists_splits_top H (isAffineOpen_inf_of_isSeparated Y.hom) bX ht hV ρY hρY
    (exists_splits_preimage H hR (isAffineOpen_inf_of_isSeparated X.hom)
      (isAffineOpen_inf_of_isSeparated Y.hom) bY.2 hy hs hs' W₀ hW₀ hV hco ρX hρX)
  refine ⟨fun a => rs (le_inf le_top le_rfl) (χ a), fun a b => ?_⟩
  have := hχ a b (V a ⊓ V b) le_top inf_le_left inf_le_right
  rw [rs_self] at this
  exact this.trans (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm

end GlobalTheory.KuennethOne
