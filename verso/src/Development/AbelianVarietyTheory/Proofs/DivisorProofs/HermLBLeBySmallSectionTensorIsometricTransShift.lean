import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Establish `h : 0 < ‖u‖` using `norm_pos_iff.2 hu`. Rewrite using `[Real.log_pow, show -((2 : ℕ) * Real.log ‖u‖) / 2 = -Real.log ‖u‖ by push_cast; ring, Real.exp_neg, Real.exp_log h, mul_inv_cancel₀ h.ne']`.
-/
theorem norm_mul_exp_neg_log_normSq {u : ℂ} (hu : u ≠ 0) :
    ‖u‖ * Real.exp (-Real.log (‖u‖ ^ 2) / 2) = 1 := by
  have h : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [Real.log_pow, show -((2 : ℕ) * Real.log ‖u‖) / 2 = -Real.log ‖u‖ by push_cast; ring,
    Real.exp_neg, Real.exp_log h, mul_inv_cancel₀ h.ne']

/- English proof (translation)
Rewrite using `[hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]`.
-/
theorem ratSec_div_eq {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    (h : genericPoint X ∈ L.U i ⊓ L.U j) :
    (r i : X.functionField) / (r j : X.functionField) = fnOf _ h (L.g i j : Γ(X, L.U i ⊓ L.U j)) := by
  rw [hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]

/- English proof (translation)
Rewrite using `[ratSec_div_eq hr (gen_mem (memInf hi hj))]`. Conclude with `regAt_fnOf (memInf hi hj) _ _`.
-/
theorem regAt_ratSec_div {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι} {x : X}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : RegAt x ((r i : X.functionField) / (r j : X.functionField)) := by
  rw [ratSec_div_eq hr (gen_mem (memInf hi hj))]
  exact regAt_fnOf (memInf hi hj) _ _

/- English proof (translation)
Establish `hy` using `mem_ptsIn_inf.2 ⟨hi, hj⟩`. Rewrite using `[ratSec_div_eq hr (gen_mem (mem_ptsIn.1 hy)), ratVal_fnOf hy]`. Both sides reduce to the same expression.
-/
theorem ratVal_ratSec_div {σ : k →+* ℂ} {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ratVal ((r i : X.functionField) / (r j : X.functionField)) y = gv p σ L i j y := by
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  rw [ratSec_div_eq hr (gen_mem (mem_ptsIn.1 hy)), ratVal_fnOf hy]
  rfl

/- English proof (translation)
Rewrite using `[ratVal_ratSec_div hr hi hj, φ.trans i j y hi hj, sub_sub_cancel]`. Conclude with `norm_mul_exp_neg_log_normSq (gv_ne_zero hi hj)`.
-/
theorem norm_ratSec_div {σ : k →+* ℂ} {L : LB X} (φ : Weight p σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {i j : L.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ‖ratVal ((r i : X.functionField) / (r j : X.functionField)) y‖ * Real.exp (-(φ.φ i y - φ.φ j y) / 2) = 1 := by
  rw [ratVal_ratSec_div hr hi hj, φ.trans i j y hi hj, sub_sub_cancel]
  exact norm_mul_exp_neg_log_normSq (gv_ne_zero hi hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Take `⟨r, r', hr, hr', hreg, hn⟩` from `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h`. Use `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ _).2 ⟨r, r', hr, hr', hreg, fun σ y i j hi hj => ?_⟩` and prove the remaining obligations. Establish `e : ((A.shift (fun _ => t) fun _ => rfl).φ σ).φ i y - ((B.shift (fun _ => t) fun _ => rfl).φ σ).φ j y = (A.φ σ).φ i y - (B.φ σ).φ j y`. Simplify using `only [HermLB.shift, Weight.addFn]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `hn σ y i j hi hj`.
-/
theorem Le.shift {A B : HermLB p} (t : ℝ) (h : Le B A) :
    Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ _).2 ⟨r, r', hr, hr', hreg, fun σ y i j hi hj => ?_⟩
  have e : ((A.shift (fun _ => t) fun _ => rfl).φ σ).φ i y - ((B.shift (fun _ => t) fun _ => rfl).φ σ).φ j y =
      (A.φ σ).φ i y - (B.φ σ).φ j y := by
    simp only [HermLB.shift, Weight.addFn]; ring
  rw [e]
  exact hn σ y i j hi hj

/- English proof (translation)
Take `⟨r₁, r₁', hr₁, hr₁', hreg₁, hn₁⟩` from `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h₁`. Take `⟨r₂, r₂', hr₂, hr₂', hreg₂, hn₂⟩` from `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M A).1 h₂`. Take `⟨a₀, h₀⟩` from `exists_chart A.isLB (genericPoint X)`. Set `c : X.functionFieldˣ` to `r₂' a₀ / r₁ a₀`. Establish `hs : IsRatSec B.B fun j => r₁' j * c` using `fun i j h => by`.

Simplify using `only [Units.val_mul]`. Rewrite using `[hr₁' i j h, mul_assoc]`. Establish `key (a : A.B.ι) (ha : genericPoint X ∈ A.B.U a) (i : M.B.ι) (j : B.B.ι) : (r₂ i : X.functionField) / ((r₁' j * c : X.functionFieldˣ) : X.functionField) = (r₂ i : X.functionField) / (r₂' a : X.functionField) * ((r₁ a : X.functionField) / (r₁' j : X.functionField))`. Establish `e₁` using `hr₁ a a₀ (memInf ha h₀)`. Establish `e₂` using `hr₂' a a₀ (memInf ha h₀)`.

Establish `n₁` using `(r₁ a₀).ne_zero`. Establish `n₂` using `(r₂' a₀).ne_zero`. Establish `n₃` using `(r₂' a).ne_zero`. Establish `n₄` using `(r₁' j).ne_zero`. Simplify using `only [c, Units.val_mul, Units.val_div_eq_div_val]`.

Rewrite using `[div_mul_div_comm, div_eq_div_iff (mul_ne_zero n₄ (div_ne_zero n₂ n₁)) (mul_ne_zero n₃ n₄), e₁, e₂]`. Clear the denominators using the available nonvanishing facts. Use `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M B).2 ⟨r₂, _, hr₂, hs, fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_chart A.isLB x`. Rewrite using `[key a (gen_mem ha)]`.

Conclude with `(hreg₂ x i a hi ha).mul (hreg₁ x a j ha hj)`. Establish `ha` using `mem_pick (A.φ σ).isLB y set a := pick (A.φ σ).isLB y`. Establish `hx` using `mem_ptsIn.1 ha`. Rewrite using `[key a (gen_mem hx), ratVal_mul (hreg₂ _ i a (mem_ptsIn.1 hi) hx) (hreg₁ _ a j hx (mem_ptsIn.1 hj)), norm_mul]`. Establish `e : -((M.φ σ).φ i y - (B.φ σ).φ j y) / 2 = -((M.φ σ).φ i y - (A.φ σ).φ a y) / 2 + -((A.φ σ).φ a y - (B.φ σ).φ j y) / 2` using `by ring`.

Rewrite using `[e, Real.exp_add]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Le.trans {A B M : HermLB p} (h₁ : Le B A) (h₂ : Le A M) : Le B M := by
  obtain ⟨r₁, r₁', hr₁, hr₁', hreg₁, hn₁⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h₁
  obtain ⟨r₂, r₂', hr₂, hr₂', hreg₂, hn₂⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M A).1 h₂
  obtain ⟨a₀, h₀⟩ := exists_chart A.isLB (genericPoint X)
  let c : X.functionFieldˣ := r₂' a₀ / r₁ a₀
  have hs : IsRatSec B.B fun j => r₁' j * c := fun i j h => by
    simp only [Units.val_mul]
    rw [hr₁' i j h, mul_assoc]
  have key (a : A.B.ι) (ha : genericPoint X ∈ A.B.U a) (i : M.B.ι) (j : B.B.ι) :
      (r₂ i : X.functionField) / ((r₁' j * c : X.functionFieldˣ) : X.functionField) =
        (r₂ i : X.functionField) / (r₂' a : X.functionField) * ((r₁ a : X.functionField) / (r₁' j : X.functionField)) := by
    have e₁ := hr₁ a a₀ (memInf ha h₀)
    have e₂ := hr₂' a a₀ (memInf ha h₀)
    have n₁ := (r₁ a₀).ne_zero
    have n₂ := (r₂' a₀).ne_zero
    have n₃ := (r₂' a).ne_zero
    have n₄ := (r₁' j).ne_zero
    simp only [c, Units.val_mul, Units.val_div_eq_div_val]
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero n₄ (div_ne_zero n₂ n₁)) (mul_ne_zero n₃ n₄), e₁, e₂]
    field_simp
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M B).2 ⟨r₂, _, hr₂, hs, fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart A.isLB x
    rw [key a (gen_mem ha)]
    exact (hreg₂ x i a hi ha).mul (hreg₁ x a j ha hj)
  · have ha := mem_pick (A.φ σ).isLB y
    set a := pick (A.φ σ).isLB y
    have hx := mem_ptsIn.1 ha
    rw [key a (gen_mem hx), ratVal_mul (hreg₂ _ i a (mem_ptsIn.1 hi) hx) (hreg₁ _ a j hx (mem_ptsIn.1 hj)), norm_mul]
    have e : -((M.φ σ).φ i y - (B.φ σ).φ j y) / 2 =
        -((M.φ σ).φ i y - (A.φ σ).φ a y) / 2 + -((A.φ σ).φ a y - (B.φ σ).φ j y) / 2 := by ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((r₂ i : X.functionField) / (r₂' a : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ i y - (A.φ σ).φ a y) / 2)) *
        (‖ratVal ((r₁ a : X.functionField) / (r₁' j : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ a y - (B.φ σ).φ j y) / 2)) := by ring
      _ ≤ 1 := mul_le_one₀ (hn₂ σ y i a hi ha) (by positivity) (hn₁ σ y a j ha hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Take `⟨r, r', hr, hr', hreg, hn⟩` from `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h`. Take `⟨ρ, hρ⟩` from `exists_isRatSec M.isLB`. Establish `hs` using `((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec A.isLB hr)).isRatSec`. Establish `hs'` using `((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec B.isLB hr')).isRatSec`. Establish `key (c : M.B.ι × A.B.ι) (d : M.B.ι × B.B.ι) : ((ρ c.1 * r c.2 : X.functionFieldˣ) : X.functionField) / ((ρ d.1 * r' d.2 : X.functionFieldˣ) : X.functionField) = (ρ c.1 : X.functionField) / (ρ d.1 : X.functionField) * ((r c.2 : X.functionField) / (r' d.2 : X.functionField))`.

Rewrite using `[Units.val_mul, Units.val_mul, mul_div_mul_comm]`. Use `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p (M.tens A) (M.tens B)).2 ⟨fun c => ρ c.1 * r c.2, fun d => ρ d.1 * r' d.2, hs, hs', fun x c d hc hd => ?_, fun σ y c d hc hd => ?_⟩` and prove the remaining obligations. Use `beta_reduce erw [key c d]`. Conclude with `(regAt_ratSec_div hρ hc.1 hd.1).mul (hreg x c.2 d.2 hc.2 hd.2)`. Establish `hc'` using `mem_ptsIn_inf.1 hc`.

Establish `hd'` using `mem_ptsIn_inf.1 hd`. Use `beta_reduce`. Use `erw [key c d]`. Rewrite using `[ratVal_mul (regAt_ratSec_div hρ (mem_ptsIn.1 hc'.1) (mem_ptsIn.1 hd'.1)) (hreg _ c.2 d.2 (mem_ptsIn.1 hc'.2) (mem_ptsIn.1 hd'.2)), norm_mul]`. Establish `e : -(((M.tens A).φ σ).φ c y - ((M.tens B).φ σ).φ d y) / 2 = -((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2 + -((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2`.

Simplify using `only [HermLB.tens, Weight.tens]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Real.exp_add]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_ratSec_div (M.φ σ) hρ hc'.1 hd'.1, one_mul]`.

Conclude with `hn σ y c.2 d.2 hc'.2 hd'.2`.
-/
theorem Le.tens {A B : HermLB p} (M : HermLB p) (h : Le B A) : Le (M.tens B) (M.tens A) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  obtain ⟨ρ, hρ⟩ := exists_isRatSec M.isLB
  have hs := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec A.isLB hr)).isRatSec
  have hs' := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec B.isLB hr')).isRatSec
  have key (c : M.B.ι × A.B.ι) (d : M.B.ι × B.B.ι) :
      ((ρ c.1 * r c.2 : X.functionFieldˣ) : X.functionField) / ((ρ d.1 * r' d.2 : X.functionFieldˣ) : X.functionField) =
        (ρ c.1 : X.functionField) / (ρ d.1 : X.functionField) * ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) := by
    rw [Units.val_mul, Units.val_mul, mul_div_mul_comm]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p (M.tens A) (M.tens B)).2 ⟨fun c => ρ c.1 * r c.2, fun d => ρ d.1 * r' d.2, hs, hs',
    fun x c d hc hd => ?_, fun σ y c d hc hd => ?_⟩
  · beta_reduce
    erw [key c d]
    exact (regAt_ratSec_div hρ hc.1 hd.1).mul (hreg x c.2 d.2 hc.2 hd.2)
  · have hc' := mem_ptsIn_inf.1 hc
    have hd' := mem_ptsIn_inf.1 hd
    beta_reduce
    erw [key c d]
    rw [ratVal_mul (regAt_ratSec_div hρ (mem_ptsIn.1 hc'.1) (mem_ptsIn.1 hd'.1))
      (hreg _ c.2 d.2 (mem_ptsIn.1 hc'.2) (mem_ptsIn.1 hd'.2)), norm_mul]
    have e : -(((M.tens A).φ σ).φ c y - ((M.tens B).φ σ).φ d y) / 2 =
        -((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2 + -((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2 := by
      simp only [HermLB.tens, Weight.tens]; ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((ρ c.1 : X.functionField) / (ρ d.1 : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2)) *
        (‖ratVal ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2)) := by ring
      _ ≤ 1 := by
        rw [norm_ratSec_div (M.φ σ) hρ hc'.1 hd'.1, one_mul]
        exact hn σ y c.2 d.2 hc'.2 hd'.2

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Take `⟨w, hw, h⟩` from `hi.exists_units`. Take `⟨r, hr⟩` from `exists_isRatSec B.isLB`. Take `⟨b₀, h₀⟩` from `exists_chart B.isLB (genericPoint X)`. Set `F (U : X.Opens) (u : Γ(X, U)ˣ) : X.functionFieldˣ` to `gm (𝟙 X) (genericPoint X) U u`. Establish `hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint X ∈ U) : (F U u : X.functionField) = fnOf U hU u.val` using `gm_val (𝟙 X) _ U hU u`.

Establish `hw' (a a' b b') (h₁ : genericPoint X ∈ A.B.U a) (h₂ : genericPoint X ∈ A.B.U a') (h₃ : genericPoint X ∈ B.B.U b) (h₄ : genericPoint X ∈ B.B.U b') : F _ (w a b) = F _ (A.B.g a a') * (F _ (B.B.g b b'))⁻¹ * F _ (w a' b')` using `hw _ (𝟙 X) _ a a' b b' h₁ h₂ h₃ h₄`. Establish `hM (a) (h₁ : genericPoint X ∈ A.B.U a) : F _ (A.B.g a a) = 1` using `gm_self A.isLB (𝟙 X) _ h₁`. Establish `hL : F _ (B.B.g b₀ b₀) = 1` using `gm_self B.isLB (𝟙 X) _ h₀`. Establish `hr' : IsRatSec A.B fun a => F _ (w a b₀) * r b₀` using `fun a a' h' => by beta_reduce`. Rewrite using `[← hF, ← Units.val_mul, hw' a a' b₀ b₀ h'.1 h'.2 h₀ h₀, hL, inv_one, mul_one, mul_assoc]`.

Establish `key (a b) (h' : genericPoint X ∈ A.B.U a ⊓ B.B.U b) : ((F _ (w a b₀) * r b₀ : X.functionFieldˣ) : X.functionField) / (r b : X.functionField) = fnOf _ h' (w a b).val`. Rewrite using `[div_eq_iff (r b).ne_zero, ← hF, hr b b₀ (memInf h'.2 h₀), ← hF _ (B.B.g b b₀), ← Units.val_mul, ← Units.val_mul, hw' a a b b₀ h'.1 h'.1 h'.2 h₀, hM a h'.1, one_mul, mul_comm (F _ (B.B.g b b₀))⁻¹, mul_assoc, inv_mul_cancel_left]`. Use `(GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).2 ⟨_, r, hr', hr, fun x a b ha hb => ?_, fun σ y a b ha hb => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[key a b (gen_mem (memInf ha hb))]`.

Conclude with `regAt_fnOf (memInf ha hb) _ _`. Establish `hab` using `mem_ptsIn_inf.2 ⟨ha, hb⟩ beta_reduce`. Rewrite using `[key a b (gen_mem (mem_ptsIn.1 hab)), ratVal_fnOf hab, h σ a b y ha hb, add_sub_cancel_left, logSq, norm_mul_exp_neg_log_normSq (ev_ne_zero hab (Units.isUnit _))]`.
-/
theorem le_of_isometric {A B : HermLB p} (hi : B.Isometric A) : Le B A := by
  classical
  obtain ⟨w, hw, h⟩ := hi.exists_units
  obtain ⟨r, hr⟩ := exists_isRatSec B.isLB
  obtain ⟨b₀, h₀⟩ := exists_chart B.isLB (genericPoint X)
  let F (U : X.Opens) (u : Γ(X, U)ˣ) : X.functionFieldˣ := gm (𝟙 X) (genericPoint X) U u
  have hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint X ∈ U) : (F U u : X.functionField) = fnOf U hU u.val :=
    gm_val (𝟙 X) _ U hU u
  have hw' (a a' b b') (h₁ : genericPoint X ∈ A.B.U a) (h₂ : genericPoint X ∈ A.B.U a')
      (h₃ : genericPoint X ∈ B.B.U b) (h₄ : genericPoint X ∈ B.B.U b') :
      F _ (w a b) = F _ (A.B.g a a') * (F _ (B.B.g b b'))⁻¹ * F _ (w a' b') :=
    hw _ (𝟙 X) _ a a' b b' h₁ h₂ h₃ h₄
  have hM (a) (h₁ : genericPoint X ∈ A.B.U a) : F _ (A.B.g a a) = 1 := gm_self A.isLB (𝟙 X) _ h₁
  have hL : F _ (B.B.g b₀ b₀) = 1 := gm_self B.isLB (𝟙 X) _ h₀
  have hr' : IsRatSec A.B fun a => F _ (w a b₀) * r b₀ := fun a a' h' => by
    beta_reduce
    rw [← hF, ← Units.val_mul, hw' a a' b₀ b₀ h'.1 h'.2 h₀ h₀, hL, inv_one, mul_one, mul_assoc]
  have key (a b) (h' : genericPoint X ∈ A.B.U a ⊓ B.B.U b) :
      ((F _ (w a b₀) * r b₀ : X.functionFieldˣ) : X.functionField) / (r b : X.functionField) = fnOf _ h' (w a b).val := by
    rw [div_eq_iff (r b).ne_zero, ← hF, hr b b₀ (memInf h'.2 h₀), ← hF _ (B.B.g b b₀), ← Units.val_mul, ← Units.val_mul,
      hw' a a b b₀ h'.1 h'.1 h'.2 h₀, hM a h'.1, one_mul, mul_comm (F _ (B.B.g b b₀))⁻¹, mul_assoc,
      inv_mul_cancel_left]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).2 ⟨_, r, hr', hr, fun x a b ha hb => ?_, fun σ y a b ha hb => ?_⟩
  · beta_reduce
    rw [key a b (gen_mem (memInf ha hb))]
    exact regAt_fnOf (memInf ha hb) _ _
  · have hab := mem_ptsIn_inf.2 ⟨ha, hb⟩
    beta_reduce
    rw [key a b (gen_mem (mem_ptsIn.1 hab)), ratVal_fnOf hab, h σ a b y ha hb, add_sub_cancel_left, logSq,
      norm_mul_exp_neg_log_normSq (ev_ne_zero hab (Units.isUnit _))]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _` and use `⟨Le.tens _, le_of_isometric, Le.trans, fun t => Le.shift t⟩`.
-/
theorem le_tens_isometric_trans_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B M : HermLB p, (Le B A → Le (M.tens B) (M.tens A)) ∧ (B.Isometric A → Le B A) ∧ (Le B A → Le A M → Le B M) ∧
      ∀ t : ℝ, Le B A → Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) :=
  fun _ _ _ _ _ _ _ _ => ⟨Le.tens _, le_of_isometric, Le.trans, fun t => Le.shift t⟩

end GlobalTheory.HSNef
