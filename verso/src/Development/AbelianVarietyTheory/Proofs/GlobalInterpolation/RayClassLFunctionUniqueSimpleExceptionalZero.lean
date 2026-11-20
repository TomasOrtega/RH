import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowthStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionLogDerivLocalFormulaStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyLogDerivPositivityStatement

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RealZero

/- English proof (translation)
Establish `hA` using `(GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1`. Establish `hU : IsPreconnected {s : ℂ | 1 / 2 < s.re}` using `(convex_halfSpace_re_gt (1 / 2)).isPreconnected`. Establish `h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re}` using `by show (1 : ℝ) / 2 < (2 : ℂ).re`. Evaluate the numerical expressions. Establish `hF2 : 𝓕.F χ 2 ≠ 0` using `(GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ 2 (by norm_num)).2.2.1`.

Establish `h2top : analyticOrderAt (𝓕.F χ) 2 ≠ ⊤`. Rewrite using `[(hA 2 h2).analyticOrderAt_eq_zero.mpr hF2]`. Conclude with `ENat.zero_ne_top`. Conclude with `hA.analyticOrderAt_ne_top_of_isPreconnected hU h2 hz h2top`.
-/
theorem order_ne_top (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ} (hz : 1 / 2 < z.re) :
    analyticOrderAt (𝓕.F χ) z ≠ ⊤ := by
  have hA := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1
  have hU : IsPreconnected {s : ℂ | 1 / 2 < s.re} := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show (1 : ℝ) / 2 < (2 : ℂ).re
    norm_num
  have hF2 : 𝓕.F χ 2 ≠ 0 := (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ 2 (by norm_num)).2.2.1
  have h2top : analyticOrderAt (𝓕.F χ) 2 ≠ ⊤ := by
    rw [(hA 2 h2).analyticOrderAt_eq_zero.mpr hF2]
    exact ENat.zero_ne_top
  exact hA.analyticOrderAt_ne_top_of_isPreconnected hU h2 hz h2top

/- English proof (translation)
Establish `hA` using `(GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1 z hz`. Establish `h` using `(natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mpr hn`. Rewrite `h` using `[← Nat.cast_analyticOrderNatAt (order_ne_top 𝓕 χ hz)]`. Conclude with `h` after adjusting the coercions.
-/
theorem le_order (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ} (hz : 1 / 2 < z.re) (n : ℕ)
    (hn : ∀ i < n, iteratedDeriv i (𝓕.F χ) z = 0) :
    n ≤ analyticOrderNatAt (𝓕.F χ) z := by
  have hA := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1 z hz
  have h := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mpr hn
  rw [← Nat.cast_analyticOrderNatAt (order_ne_top 𝓕 χ hz)] at h
  exact_mod_cast h

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `(GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ z (not_le.mp h)).2.2.1 hz`.
-/
theorem re_le_one (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ}
    (hz : 𝓕.F χ z = 0) : z.re ≤ 1 := by
  by_contra h
  exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ z (not_le.mp h)).2.2.1 hz

/- English proof (translation)
Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hS, Complex.re_sum]`. Establish `hnn : ∀ w ∈ hS.toFinset, 0 ≤ ((m w : ℂ) / ((σ : ℂ) - w)).re`. Introduce `w hw`. Rewrite `hw` using `[Set.Finite.mem_toFinset]`. Establish `h1` using `hre w hw`.

Rewrite using `[Complex.div_re]`. Simplify using `only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero, Complex.sub_re, Complex.ofReal_re]`. Conclude with `div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Complex.normSq_nonneg _)`. Establish `himg : ∑ β ∈ T, (m β : ℝ) / (σ - β) = ∑ w ∈ T.image (fun β : ℝ => (β : ℂ)), ((m w : ℂ) / ((σ : ℂ) - w)).re`. Rewrite using `[Finset.sum_image (fun a _ b _ h => Complex.ofReal_injective h)]`.

Use `Finset.sum_congr rfl (fun β _ => ?_)` and prove the remaining obligations. Establish `e : (m β : ℂ) / ((σ : ℂ) - β) = (((m β : ℝ) / (σ - β) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]`. Rewrite using `[e, Complex.ofReal_re]`. Rewrite using `[himg]`.

Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w hw _ => hnn w hw)` and prove the remaining obligations. Introduce `w hw`. Rewrite `hw` using `[Finset.mem_image]`. Take `⟨β, hβ, rfl⟩` from `hw`. Rewrite using `[Set.Finite.mem_toFinset]`.

Conclude with `hTS β hβ`.
-/
private lemma sum_real_zeros_div_sub_le_re_finsum_div_sub (m : ℂ → ℕ) (σ : ℝ) (S : Set ℂ) (hS : S.Finite) (T : Finset ℝ)
    (hTS : ∀ β ∈ T, (β : ℂ) ∈ S) (hre : ∀ w ∈ S, w.re < σ) :
    ∑ β ∈ T, (m β : ℝ) / (σ - β) ≤ (∑ᶠ w ∈ S, (m w : ℂ) / ((σ : ℂ) - w)).re := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Complex.re_sum]
  have hnn : ∀ w ∈ hS.toFinset, 0 ≤ ((m w : ℂ) / ((σ : ℂ) - w)).re := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have h1 := hre w hw
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero,
      Complex.sub_re, Complex.ofReal_re]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Complex.normSq_nonneg _)
  have himg : ∑ β ∈ T, (m β : ℝ) / (σ - β)
      = ∑ w ∈ T.image (fun β : ℝ => (β : ℂ)), ((m w : ℂ) / ((σ : ℂ) - w)).re := by
    rw [Finset.sum_image (fun a _ b _ h => Complex.ofReal_injective h)]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    have e : (m β : ℂ) / ((σ : ℂ) - β) = (((m β : ℝ) / (σ - β) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
    rw [e, Complex.ofReal_re]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w hw _ => hnn w hw)
  intro w hw
  rw [Finset.mem_image] at hw
  obtain ⟨β, hβ, rfl⟩ := hw
  rw [Set.Finite.mem_toFinset]
  exact hTS β hβ

/- English proof (translation)
Establish `h1` using `Complex.re_le_norm (B - A)`. Rewrite `h1` using `[norm_sub_rev, Complex.sub_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma neg_re_le_neg_add_of_norm_sub_le_of_le_re (A B : ℂ) (x y : ℝ) (h : ‖A - B‖ ≤ x) (hy : y ≤ B.re) :
    -A.re ≤ -y + x := by
  have h1 := Complex.re_le_norm (B - A)
  rw [norm_sub_rev, Complex.sub_re] at h1
  linarith

/- English proof (translation)
Take `⟨C, hC, hmain⟩` from `GlobalTheory.T.rayClassLFunction_logDeriv_local_formula`. Use `⟨C, hC, fun 𝓕 χ σ hσ1 hσ2 T hT => ?_⟩` and prove the remaining obligations. Take `⟨hfin, -, happ⟩` from `hmain 𝓕 χ 0`. Simplify using `only [Complex.ofReal_zero, zero_mul, add_zero] at hfin happ`. Establish `hs1 : 1 < (σ : ℂ).re` using `by simpa using hσ1`.

Take `⟨-, -, hFs, hL⟩` from `GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ σ hs1`. Establish `hnear : ‖(σ : ℂ) - 5 / 4‖ ≤ 1 / 2`. Establish `e : (σ : ℂ) - 5 / 4 = ((σ - 5 / 4 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.

Establish `hE` using `happ σ hnear hFs`. Establish `hsum` using `sum_real_zeros_div_sub_le_re_finsum_div_sub (analyticOrderNatAt (𝓕.F χ)) σ _ hfin T ?_ ?_`. Establish `h2` using `neg_re_le_neg_add_of_norm_sub_le_of_le_re _ _ _ _ hE hsum`. Rewrite using `[← hL, Complex.add_re, Complex.neg_re]`. Use `split_ifs with h1`.

Establish `e : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1)`. Rewrite using `[show (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) by`. Rewrite using `[Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one], Complex.ofReal_re]`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `β hβ`. Take `⟨h34, hz⟩` from `hT β hβ`. Establish `hb1 : β ≤ 1` using `by simpa using re_le_one 𝓕 χ hz`.

Use `⟨?_, hz⟩` and prove the remaining obligations. Establish `e : (β : ℂ) - 5 / 4 = ((β - 5 / 4 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Introduce `w hw`.

Use `re_le_one 𝓕 χ hw.2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bound : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ),
    ∀ σ : ℝ, 1 < σ → σ ≤ 7 / 4 → ∀ T : Finset ℝ,
    (∀ β ∈ T, 3 / 4 ≤ β ∧ 𝓕.F χ β = 0) →
    (LSeries (𝓕.lamChi χ) σ).re ≤ (if χ = 1 then 1 / (σ - 1) else 0) + C * 𝓕.ell 0
      - ∑ β ∈ T, (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) := by
  obtain ⟨C, hC, hmain⟩ := GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
  refine ⟨C, hC, fun 𝓕 χ σ hσ1 hσ2 T hT => ?_⟩
  obtain ⟨hfin, -, happ⟩ := hmain 𝓕 χ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hfin happ
  have hs1 : 1 < (σ : ℂ).re := by simpa using hσ1
  obtain ⟨-, -, hFs, hL⟩ := GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ σ hs1
  have hnear : ‖(σ : ℂ) - 5 / 4‖ ≤ 1 / 2 := by
    have e : (σ : ℂ) - 5 / 4 = ((σ - 5 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hE := happ σ hnear hFs
  have hsum := sum_real_zeros_div_sub_le_re_finsum_div_sub (analyticOrderNatAt (𝓕.F χ)) σ _ hfin T ?_ ?_
  · have h2 := neg_re_le_neg_add_of_norm_sub_le_of_le_re _ _ _ _ hE hsum
    rw [← hL, Complex.add_re, Complex.neg_re]
    split_ifs with h1
    · have e : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
        rw [show (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) by
          rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one], Complex.ofReal_re]
      rw [e]
      linarith
    · rw [Complex.zero_re]
      linarith
  · intro β hβ
    obtain ⟨h34, hz⟩ := hT β hβ
    have hb1 : β ≤ 1 := by simpa using re_le_one 𝓕 χ hz
    refine ⟨?_, hz⟩
    have e : (β : ℂ) - 5 / 4 = ((β - 5 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · intro w hw
    have := re_le_one 𝓕 χ hw.2
    linarith

/- English proof (translation)
Substitute `hσ` using the available equality. Establish `h2c : 0 < 2 * c / ℓ` using `by positivity`. Establish `hpos : 0 < 1 + 2 * c / ℓ - β` using `by linarith`. Establish `hle : 1 + 2 * c / ℓ - β ≤ 3 * c / ℓ`. Establish `: 3 * c / ℓ = c / ℓ + 2 * c / ℓ` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `one_div_le_one_div_of_le hpos hle`. Rewrite `key` using `[one_div_div]`. Rewrite using `[div_eq_mul_one_div m]`. Conclude with `mul_le_mul_of_nonneg_left key hm`.
-/
private lemma term_lemma_3 {c ℓ σ β : ℝ} (m : ℝ) (hm : 0 ≤ m) (hc : 0 < c) (hℓ : 0 < ℓ)
    (hσ : σ = 1 + 2 * c / ℓ) (h1 : 1 - c / ℓ ≤ β) (h2 : β ≤ 1) :
    m * (ℓ / (3 * c)) ≤ m / (σ - β) := by
  subst hσ
  have h2c : 0 < 2 * c / ℓ := by positivity
  have hpos : 0 < 1 + 2 * c / ℓ - β := by linarith
  have hle : 1 + 2 * c / ℓ - β ≤ 3 * c / ℓ := by
    have : 3 * c / ℓ = c / ℓ + 2 * c / ℓ := by ring
    linarith
  have key := one_div_le_one_div_of_le hpos hle
  rw [one_div_div] at key
  rw [div_eq_mul_one_div m]
  exact mul_le_mul_of_nonneg_left key hm

/- English proof (translation)
Establish `h1c : 1 / c = 100 * (C + 1)`. Rewrite using `[eq_comm, eq_div_iff hc.ne']`. Take the linear combination `hcC`. Establish `e2 : ℓ / (2 * c) = ℓ / 2 * (1 / c)` using `by rw [div_mul_div_comm, mul_one]`. Establish `e3 : ℓ / (3 * c) = ℓ / 3 * (1 / c)` using `by rw [div_mul_div_comm, mul_one]`.

Rewrite `hX` using `[e3, h1c]`. Rewrite `h` using `[e2, h1c]`. Use polynomial arithmetic with `[mul_pos hℓ hC]`.
-/
private lemma false_of_le_of_mul_hundred_mul_add_one_eq_one {C c ℓ X : ℝ} (hC : 0 < C) (hℓ : 0 < ℓ) (hcC : c * (100 * (C + 1)) = 1)
    (hc : 0 < c) (hX : 2 * (ℓ / (3 * c)) ≤ X) (h : 0 ≤ ℓ / (2 * c) + 4 * (C * ℓ) - X) : False := by
  have h1c : 1 / c = 100 * (C + 1) := by
    rw [eq_comm, eq_div_iff hc.ne']
    linear_combination hcC
  have e2 : ℓ / (2 * c) = ℓ / 2 * (1 / c) := by rw [div_mul_div_comm, mul_one]
  have e3 : ℓ / (3 * c) = ℓ / 3 * (1 / c) := by rw [div_mul_div_comm, mul_one]
  rw [e3, h1c] at hX
  rw [e2, h1c] at h
  nlinarith [mul_pos hℓ hC]

/- English proof (translation)
Take `⟨C, hC, hb⟩` from `exists_bound`. Take `⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (100 * (C + 1))` from `⟨_, rfl⟩`. Establish `hc : 0 < c` using `by rw [hcdef]; positivity`. Establish `hcC : c * (100 * (C + 1)) = 1`. Rewrite using `[hcdef, one_div, inv_mul_cancel₀ (by positivity)]`.

Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Introduce `𝓕 χ ψ β β' hχ hψ hβ hβ' hc1 hc1' hz hz'`. Establish `hℓ2 : 2 < 𝓕.ell 0` using `𝓕.two_lt_ell 0`. Establish `hℓ : 0 < 𝓕.ell 0` using `by linarith`. Establish `hCℓ : 0 < C * 𝓕.ell 0` using `mul_pos hC hℓ`.

Take `⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + 2 * c / 𝓕.ell 0` from `⟨_, rfl⟩`. Establish `hσ1 : 1 < σ`. Establish `: 0 < 2 * c / 𝓕.ell 0` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hσ2 : σ ≤ 7 / 4`.

Establish `hc' : c < 1 / 100` using `by nlinarith [mul_pos hc hC]`. Establish `: 2 * c / 𝓕.ell 0 ≤ 3 / 4`. Rewrite using `[div_le_iff₀ hℓ]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hpole : 1 / (σ - 1) = 𝓕.ell 0 / (2 * c)`. Rewrite using `[hσdef, add_sub_cancel_left, one_div_div]`. Establish `hq : 0 < 𝓕.ell 0 / (3 * c)` using `by positivity`. Establish `tb : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ) (k : ℕ), 3 / 4 ≤ x → 1 - c / 𝓕.ell 0 ≤ x → 𝓕.F φ x = 0 → (∀ i < k, iteratedDeriv i (𝓕.F φ) x = 0) → k * (𝓕.ell 0 / (3 * c)) ≤ (analyticOrderNatAt (𝓕.F φ) x : ℝ) / (σ - x)`. Introduce `φ x k hx hxc hx0 hk`.

Establish `hx2 : 1 / 2 < (x : ℂ).re`. Rewrite using `[Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx1 : x ≤ 1` using `by simpa using re_le_one 𝓕 φ hx0`. Establish `hm : (k : ℝ) ≤ analyticOrderNatAt (𝓕.F φ) x`.

Conclude with `le_order 𝓕 φ hx2 k hk` after adjusting the coercions. Establish `ht` using `term_lemma_3 (analyticOrderNatAt (𝓕.F φ) x : ℝ) (by positivity) hc hℓ hσdef hxc hx1`. Use the polynomial consequences of the given equalities and inequalities. Establish `d1 : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 𝓕.F φ x = 0 → ∀ i < 1, iteratedDeriv i (𝓕.F φ) x = 0`. Introduce `φ x h0 i hi`.

Use `interval_cases i`. Simplify using `using h0`. Establish `tβ` using `tb χ β 1 hβ hc1 hz (d1 χ β hz)`. Establish `tβ'` using `tb ψ β' 1 hβ' hc1' hz' (d1 ψ β' hz')`. Move the coercions through the operations in `at tβ tβ'`.

Establish `sg : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 3 / 4 ≤ x → 𝓕.F φ x = 0 → ∀ y ∈ ({x} : Finset ℝ), 3 / 4 ≤ y ∧ 𝓕.F φ y = 0`. Introduce `φ x hx h0 y hy`. Rewrite `hy` using `[Finset.mem_singleton]`. Rewrite using `[hy]`. Conclude with `⟨hx, h0⟩`.

Distinguish the cases in `hcp : χ = ψ`. Substitute `hcp` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hbad`. Choose the witnesses or unpack the hypotheses as in `⟨T, hT, hXT⟩ : ∃ T : Finset ℝ, (∀ x ∈ T, 3 / 4 ≤ x ∧ 𝓕.F χ x = 0) ∧ 2 * (𝓕.ell 0 / (3 * c)) ≤ ∑ x ∈ T, (analyticOrderNatAt (𝓕.F χ) x : ℝ) / (σ - x) := by`.

Distinguish the cases in `hne : β = β'`. Establish `hd : deriv (𝓕.F χ) β = 0`. Assume the negation of the conclusion as `hd`. Conclude with `hbad ⟨hne, hd⟩`. Use `⟨{β}, sg χ β hβ hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_singleton]`. Establish `h2` using `tb χ β 2 hβ hc1 hz (by`. Introduce `i hi`. Use `interval_cases i`. Simplify using `using hz`.

Simplify using `using hd)`. Conclude with `h2` after adjusting the coercions. Use `⟨{β, β'}, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_insert, Finset.mem_singleton]`.

Break down `hx with rfl | rfl` into its components or cases. Conclude with `⟨hβ, hz⟩`. Conclude with `⟨hβ', hz'⟩`. Rewrite using `[Finset.sum_pair hne]`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `h1 : χ = 1`. Substitute `h1` using the available equality. Establish `hB` using `hb 𝓕 1 σ hσ1 hσ2 T hT`. Rewrite `hB` using `[if_pos rfl, hpole]`. Establish `h0` using `(GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 1 1 σ 0 hσ1).2.1`.

Conclude with `false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)`. Establish `hB` using `hb 𝓕 χ σ hσ1 hσ2 T hT`. Rewrite `hB` using `[if_neg h1]`. Establish `hB1` using `hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)`. Rewrite `hB1` using `[if_pos rfl, hpole, Finset.sum_empty]`.

Establish `h0` using `((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1`. Conclude with `false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)`. It suffices to derive a contradiction. Distinguish the cases in `h1 : χ = 1`. Substitute `h1` using the available equality.

Establish `hψ1 : ψ ≠ 1` using `fun h => hcp h.symm`. Establish `hB1` using `hb 𝓕 1 σ hσ1 hσ2 {β} (sg 1 β hβ hz)`. Rewrite `hB1` using `[if_pos rfl, hpole, Finset.sum_singleton]`. Establish `hBψ` using `hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')`. Rewrite `hBψ` using `[if_neg hψ1, Finset.sum_singleton]`.

Establish `h0` using `((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 ψ ψ σ 0 hσ1).2.2 hψ hψ).1`. Conclude with `false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F 1) β : ℝ) / (σ - β) + (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)`. Distinguish the cases in `h2 : ψ = 1`. Substitute `h2` using the available equality. Establish `hB1` using `hb 𝓕 1 σ hσ1 hσ2 {β'} (sg 1 β' hβ' hz')`.

Rewrite `hB1` using `[if_pos rfl, hpole, Finset.sum_singleton]`. Establish `hBχ` using `hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)`. Rewrite `hBχ` using `[if_neg h1, Finset.sum_singleton]`. Establish `h0` using `((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1`. Conclude with `false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) + (analyticOrderNatAt (𝓕.F 1) β' : ℝ) / (σ - β')) (by linarith) (by linarith)`.

Establish `hχψ : χ * ψ ≠ 1`. Introduce `h`. Apply `hcp` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hB1` using `hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)`.

Rewrite `hB1` using `[if_pos rfl, hpole, Finset.sum_empty]`. Establish `hBχ` using `hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)`. Rewrite `hBχ` using `[if_neg h1, Finset.sum_singleton]`. Establish `hBψ` using `hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')`. Rewrite `hBψ` using `[if_neg h2, Finset.sum_singleton]`.

Establish `hBχψ` using `hb 𝓕 (χ * ψ) σ hσ1 hσ2 ∅ (by simp)`. Rewrite `hBχψ` using `[if_neg hχψ, Finset.sum_empty]`. Establish `h0` using `((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ ψ σ 0 hσ1).2.2 hχ hψ).2`. Conclude with `false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) + (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)`.
-/
theorem main : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (β β' : ℝ), χ * χ = 1 → ψ * ψ = 1 → 3 / 4 ≤ β → 3 / 4 ≤ β' → 1 - c / 𝓕.ell 0 ≤ β → 1 - c / 𝓕.ell 0 ≤ β' → 𝓕.F χ β = 0 → 𝓕.F ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (𝓕.F χ) β ≠ 0 := by
  obtain ⟨C, hC, hb⟩ := exists_bound
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (100 * (C + 1)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hcC : c * (100 * (C + 1)) = 1 := by
    rw [hcdef, one_div, inv_mul_cancel₀ (by positivity)]
  refine ⟨c, hc, ?_⟩
  intro 𝓕 χ ψ β β' hχ hψ hβ hβ' hc1 hc1' hz hz'
  have hℓ2 : 2 < 𝓕.ell 0 := 𝓕.two_lt_ell 0
  have hℓ : 0 < 𝓕.ell 0 := by linarith
  have hCℓ : 0 < C * 𝓕.ell 0 := mul_pos hC hℓ
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + 2 * c / 𝓕.ell 0 := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by
    have : 0 < 2 * c / 𝓕.ell 0 := by positivity
    linarith
  have hσ2 : σ ≤ 7 / 4 := by
    have hc' : c < 1 / 100 := by nlinarith [mul_pos hc hC]
    have : 2 * c / 𝓕.ell 0 ≤ 3 / 4 := by
      rw [div_le_iff₀ hℓ]
      linarith
    linarith
  have hpole : 1 / (σ - 1) = 𝓕.ell 0 / (2 * c) := by
    rw [hσdef, add_sub_cancel_left, one_div_div]
  have hq : 0 < 𝓕.ell 0 / (3 * c) := by positivity
  have tb : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ) (k : ℕ), 3 / 4 ≤ x → 1 - c / 𝓕.ell 0 ≤ x →
      𝓕.F φ x = 0 → (∀ i < k, iteratedDeriv i (𝓕.F φ) x = 0) →
      k * (𝓕.ell 0 / (3 * c)) ≤ (analyticOrderNatAt (𝓕.F φ) x : ℝ) / (σ - x) := by
    intro φ x k hx hxc hx0 hk
    have hx2 : 1 / 2 < (x : ℂ).re := by
      rw [Complex.ofReal_re]
      linarith
    have hx1 : x ≤ 1 := by simpa using re_le_one 𝓕 φ hx0
    have hm : (k : ℝ) ≤ analyticOrderNatAt (𝓕.F φ) x := by
      exact_mod_cast le_order 𝓕 φ hx2 k hk
    have ht := term_lemma_3 (analyticOrderNatAt (𝓕.F φ) x : ℝ) (by positivity) hc hℓ hσdef hxc hx1
    nlinarith
  have d1 : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 𝓕.F φ x = 0 → ∀ i < 1, iteratedDeriv i (𝓕.F φ) x = 0 := by
    intro φ x h0 i hi
    interval_cases i
    simpa using h0
  have tβ := tb χ β 1 hβ hc1 hz (d1 χ β hz)
  have tβ' := tb ψ β' 1 hβ' hc1' hz' (d1 ψ β' hz')
  push_cast at tβ tβ'
  have sg : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 3 / 4 ≤ x → 𝓕.F φ x = 0 →
      ∀ y ∈ ({x} : Finset ℝ), 3 / 4 ≤ y ∧ 𝓕.F φ y = 0 := by
    intro φ x hx h0 y hy
    rw [Finset.mem_singleton] at hy
    rw [hy]
    exact ⟨hx, h0⟩
  by_cases hcp : χ = ψ
  · subst hcp
    refine ⟨rfl, ?_⟩
    by_contra hbad
    obtain ⟨T, hT, hXT⟩ : ∃ T : Finset ℝ, (∀ x ∈ T, 3 / 4 ≤ x ∧ 𝓕.F χ x = 0) ∧
        2 * (𝓕.ell 0 / (3 * c)) ≤ ∑ x ∈ T, (analyticOrderNatAt (𝓕.F χ) x : ℝ) / (σ - x) := by
      by_cases hne : β = β'
      · have hd : deriv (𝓕.F χ) β = 0 := by
          by_contra hd
          exact hbad ⟨hne, hd⟩
        refine ⟨{β}, sg χ β hβ hz, ?_⟩
        rw [Finset.sum_singleton]
        have h2 := tb χ β 2 hβ hc1 hz (by
          intro i hi
          interval_cases i
          · simpa using hz
          · simpa using hd)
        exact_mod_cast h2
      · refine ⟨{β, β'}, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨hβ, hz⟩
          · exact ⟨hβ', hz'⟩
        · rw [Finset.sum_pair hne]
          linarith
    by_cases h1 : χ = 1
    · subst h1
      have hB := hb 𝓕 1 σ hσ1 hσ2 T hT
      rw [if_pos rfl, hpole] at hB
      have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 1 1 σ 0 hσ1).2.1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)
    · have hB := hb 𝓕 χ σ hσ1 hσ2 T hT
      rw [if_neg h1] at hB
      have hB1 := hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)
      rw [if_pos rfl, hpole, Finset.sum_empty] at hB1
      have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)
  · exfalso
    by_cases h1 : χ = 1
    · subst h1
      have hψ1 : ψ ≠ 1 := fun h => hcp h.symm
      have hB1 := hb 𝓕 1 σ hσ1 hσ2 {β} (sg 1 β hβ hz)
      rw [if_pos rfl, hpole, Finset.sum_singleton] at hB1
      have hBψ := hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')
      rw [if_neg hψ1, Finset.sum_singleton] at hBψ
      have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 ψ ψ σ 0 hσ1).2.2 hψ hψ).1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F 1) β : ℝ) / (σ - β) +
        (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)
    · by_cases h2 : ψ = 1
      · subst h2
        have hB1 := hb 𝓕 1 σ hσ1 hσ2 {β'} (sg 1 β' hβ' hz')
        rw [if_pos rfl, hpole, Finset.sum_singleton] at hB1
        have hBχ := hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)
        rw [if_neg h1, Finset.sum_singleton] at hBχ
        have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1
        exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) +
          (analyticOrderNatAt (𝓕.F 1) β' : ℝ) / (σ - β')) (by linarith) (by linarith)
      · have hχψ : χ * ψ ≠ 1 := by
          intro h
          apply hcp
          calc χ = χ * (ψ * ψ) := by rw [hψ, mul_one]
            _ = (χ * ψ) * ψ := (mul_assoc _ _ _).symm
            _ = ψ := by rw [h, one_mul]
        have hB1 := hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)
        rw [if_pos rfl, hpole, Finset.sum_empty] at hB1
        have hBχ := hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)
        rw [if_neg h1, Finset.sum_singleton] at hBχ
        have hBψ := hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')
        rw [if_neg h2, Finset.sum_singleton] at hBψ
        have hBχψ := hb 𝓕 (χ * ψ) σ hσ1 hσ2 ∅ (by simp)
        rw [if_neg hχψ, Finset.sum_empty] at hBχψ
        have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ ψ σ 0 hσ1).2.2 hχ hψ).2
        exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) +
          (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)

end GlobalTheory.Hk.RealZero
