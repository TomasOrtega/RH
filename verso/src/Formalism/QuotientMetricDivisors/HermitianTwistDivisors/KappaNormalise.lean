import Mathlib
import Formalism.QuotientMetricDivisors.PassageScaleFree
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DualMu
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.HarderNarasimhan.ShiftInvariance

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

/- English proof (translation)
Introduce `muC mu0 HH0 lam0 logκ de c1 c2 c3 Cd f r g k b p1 p2 C0 hc1 hc2 hCd hf hr hk hb hde hg hl0 hlb hmu hHH hA hB hcmp hc3`. Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hkb : 1 ≤ k * b` using `by nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 hb)]`. Establish `hkb0 : 0 ≤ k * b` using `by linarith`. Establish `h8 : 1 ≤ (k * b) ^ 8` using `one_le_pow₀ hkb`.

Establish `hg0 : 0 < g` using `by linarith`. Establish `hfr : 0 ≤ Cd * f * r` using `mul_nonneg (mul_nonneg hCd hf) hr`. Establish `hde0 : 0 ≤ de`. Rewrite using `[hde]`. Conclude with `div_nonneg hfr hg0.le`.

Establish `hde3 : de ≤ 1 / 3`. Rewrite using `[hde, div_le_iff₀ hg0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hQ : mu0 + HH0 + c2 * lam0 ≤ (p1 + p2 + c2) * b`. Use `mul_le_mul_of_nonneg_left hlb hc2` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN : c1 * Cd * f * r * (p1 + p2 + c2) * b ≤ (k * b) ^ 8`. Establish `h1` using `mul_le_mul_of_nonneg_right hA hb0`. Establish `h2 : (k * b) ^ 7 * b ≤ (k * b) ^ 7 * (k * b)` using `mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]) (pow_nonneg hkb0 7)`. Establish `h3 : (k * b) ^ 7 * (k * b) = (k * b) ^ 8` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd1 : c1 * de * (mu0 + HH0 + c2 * lam0) ≤ 1`. Establish `hc1de : 0 ≤ c1 * de` using `mul_nonneg hc1 hde0`. Establish `h1 : c1 * de * (mu0 + HH0 + c2 * lam0) ≤ c1 * de * ((p1 + p2 + c2) * b)` using `mul_le_mul_of_nonneg_left hQ hc1de`. Establish `h2 : c1 * de * ((p1 + p2 + c2) * b) = c1 * Cd * f * r * (p1 + p2 + c2) * b / g`.

Rewrite using `[hde]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : c1 * Cd * f * r * (p1 + p2 + c2) * b / g ≤ 1`. Rewrite using `[div_le_one hg0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc3l : c3 * lam0 ≤ C0 * lam0` using `mul_le_mul_of_nonneg_right hc3 hl0`. Use `⟨hde0, hde3, by linarith [hcmp hde3], hd1, by linarith⟩` and prove the remaining obligations.
-/
theorem passage_arithmetic : PassageArith := by
  intro muC mu0 HH0 lam0 logκ de c1 c2 c3 Cd f r g k b p1 p2 C0 hc1 hc2 hCd hf hr hk hb hde hg
    hl0 hlb hmu hHH hA hB hcmp hc3
  have hb0 : 0 ≤ b := by linarith
  have hkb : 1 ≤ k * b := by nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 hb)]
  have hkb0 : 0 ≤ k * b := by linarith
  have h8 : 1 ≤ (k * b) ^ 8 := one_le_pow₀ hkb
  have hg0 : 0 < g := by linarith
  have hfr : 0 ≤ Cd * f * r := mul_nonneg (mul_nonneg hCd hf) hr
  have hde0 : 0 ≤ de := by
    rw [hde]
    exact div_nonneg hfr hg0.le
  have hde3 : de ≤ 1 / 3 := by
    rw [hde, div_le_iff₀ hg0]
    linarith
  have hQ : mu0 + HH0 + c2 * lam0 ≤ (p1 + p2 + c2) * b := by
    have := mul_le_mul_of_nonneg_left hlb hc2
    linarith
  have hN : c1 * Cd * f * r * (p1 + p2 + c2) * b ≤ (k * b) ^ 8 := by
    have h1 := mul_le_mul_of_nonneg_right hA hb0
    have h2 : (k * b) ^ 7 * b ≤ (k * b) ^ 7 * (k * b) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]) (pow_nonneg hkb0 7)
    have h3 : (k * b) ^ 7 * (k * b) = (k * b) ^ 8 := by ring
    linarith
  have hd1 : c1 * de * (mu0 + HH0 + c2 * lam0) ≤ 1 := by
    have hc1de : 0 ≤ c1 * de := mul_nonneg hc1 hde0
    have h1 : c1 * de * (mu0 + HH0 + c2 * lam0) ≤ c1 * de * ((p1 + p2 + c2) * b) :=
      mul_le_mul_of_nonneg_left hQ hc1de
    have h2 : c1 * de * ((p1 + p2 + c2) * b) = c1 * Cd * f * r * (p1 + p2 + c2) * b / g := by
      rw [hde]
      ring
    have h3 : c1 * Cd * f * r * (p1 + p2 + c2) * b / g ≤ 1 := by
      rw [div_le_one hg0]
      linarith
    linarith
  have hc3l : c3 * lam0 ≤ C0 * lam0 := mul_le_mul_of_nonneg_right hc3 hl0
  refine ⟨hde0, hde3, by linarith [hcmp hde3], hd1, by linarith⟩

/- English proof (translation)
Introduce `J Pl _ _ mu0 logκ Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps pq w h1 hJ hPl hpq hW hw hLa hFo hC0 hEb`. Establish `hLa0 : 0 ≤ La` using `le_trans (abs_nonneg _) hLa`. Establish `hm0 : 0 ≤ m`. Rewrite using `[← hJ]`. Conclude with `Nat.cast_nonneg _`.

Establish `hf0 : 0 ≤ f` using `le_trans (Nat.cast_nonneg _) hPl`. Establish `hmN : 0 ≤ m * N`. Break down `isEmpty_or_nonempty J with hJe | ⟨⟨j0⟩⟩` into its components or cases. Establish `: m = 0`. Rewrite using `[← hJ]`.

Simplify using the standard rewrite rules. Simplify using `[this]`. Conclude with `mul_nonneg hm0 (le_trans (abs_nonneg _) (hpq j0))`. Establish `hterm : ∀ j ρ, pq j * w j ρ * logOm ≤ |pq j| * W * La`. Introduce `j ρ`.

Establish `e1 : pq j * w j ρ * logOm ≤ |pq j * w j ρ * logOm|` using `le_abs_self _`. Rewrite `e1` using `[abs_mul, abs_mul, abs_of_nonneg (hw j ρ).1]`. Establish `e2 : |pq j| * w j ρ ≤ |pq j| * W` using `mul_le_mul_of_nonneg_left (hw j ρ).2 (abs_nonneg _)`. Establish `e3 : |pq j| * w j ρ * |logOm| ≤ |pq j| * W * La` using `mul_le_mul e2 hLa (abs_nonneg _) (mul_nonneg (abs_nonneg _) hW)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsum : ∑ j, ∑ ρ, pq j * w j ρ * logOm ≤ m * f * N * W * La`. Combine the equalities or inequalities in the displayed calculation. Use `hterm j ρ` as an intermediate fact. Use `mul_le_mul_of_nonneg_right (hpq j) (mul_nonneg hW hLa0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ = m * (Fintype.card Pl : ℝ) * (N * (W * La)) := by`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ m * f * N * W * La := by`. Use `mul_le_mul_of_nonneg_left hPl (mul_nonneg (mul_nonneg hmN hW) hLa0)` as an intermediate fact.

Use polynomial arithmetic with `[this]`. Establish `g1 : mu0 ≤ logκ + m * f * N * W * La + 2 * Fabs + C0 * m * xe * (B0 + Nc)` using `by linarith`. Use `⟨g1, fun hWb hb hF hNc hB0 hxe hxe0 => ?_⟩` and prove the remaining obligations. Establish `k1 : m * f * N * W * La ≤ m * f * N * (2 * b) * La`. Use `mul_le_mul_of_nonneg_left hWb (mul_nonneg (mul_nonneg hmN hf0) hLa0)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `k2 : B0 ≤ f * m * b * xe`. Rewrite using `[hB0]`. Conclude with `mul_le_mul_of_nonneg_left hxe (mul_nonneg (mul_nonneg hf0 hm0) hb)`. Establish `k3 : C0 * m * xe * (B0 + Nc) ≤ C0 * m * xe * (f * m * b * xe + pN * b)` using `mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC0 hm0) hxe0)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem passage_size : PassageSize := by
  intro J Pl _ _ mu0 logκ Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps pq w h1 hJ hPl
    hpq hW hw hLa hFo hC0 hEb
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) hLa
  have hm0 : 0 ≤ m := by
    rw [← hJ]
    exact Nat.cast_nonneg _
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hPl
  have hmN : 0 ≤ m * N := by
    rcases isEmpty_or_nonempty J with hJe | ⟨⟨j0⟩⟩
    · have : m = 0 := by
        rw [← hJ]
        simp
      simp [this]
    · exact mul_nonneg hm0 (le_trans (abs_nonneg _) (hpq j0))
  have hterm : ∀ j ρ, pq j * w j ρ * logOm ≤ |pq j| * W * La := by
    intro j ρ
    have e1 : pq j * w j ρ * logOm ≤ |pq j * w j ρ * logOm| := le_abs_self _
    rw [abs_mul, abs_mul, abs_of_nonneg (hw j ρ).1] at e1
    have e2 : |pq j| * w j ρ ≤ |pq j| * W := mul_le_mul_of_nonneg_left (hw j ρ).2 (abs_nonneg _)
    have e3 : |pq j| * w j ρ * |logOm| ≤ |pq j| * W * La :=
      mul_le_mul e2 hLa (abs_nonneg _) (mul_nonneg (abs_nonneg _) hW)
    linarith
  have hsum : ∑ j, ∑ ρ, pq j * w j ρ * logOm ≤ m * f * N * W * La := by
    calc ∑ j, ∑ ρ, pq j * w j ρ * logOm ≤ ∑ j : J, ∑ ρ : Pl, N * (W * La) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ρ _ => by
            have := hterm j ρ
            have := mul_le_mul_of_nonneg_right (hpq j) (mul_nonneg hW hLa0)
            linarith
      _ = m * (Fintype.card Pl : ℝ) * (N * (W * La)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ]
          ring
      _ ≤ m * f * N * W * La := by
          have := mul_le_mul_of_nonneg_left hPl (mul_nonneg (mul_nonneg hmN hW) hLa0)
          nlinarith [this]
  have g1 : mu0 ≤ logκ + m * f * N * W * La + 2 * Fabs + C0 * m * xe * (B0 + Nc) := by linarith
  refine ⟨g1, fun hWb hb hF hNc hB0 hxe hxe0 => ?_⟩
  have k1 : m * f * N * W * La ≤ m * f * N * (2 * b) * La := by
    have := mul_le_mul_of_nonneg_left hWb (mul_nonneg (mul_nonneg hmN hf0) hLa0)
    linarith
  have k2 : B0 ≤ f * m * b * xe := by
    rw [hB0]
    exact mul_le_mul_of_nonneg_left hxe (mul_nonneg (mul_nonneg hf0 hm0) hb)
  have k3 : C0 * m * xe * (B0 + Nc) ≤ C0 * m * xe * (f * m * b * xe + pN * b) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC0 hm0) hxe0)
  linarith

/- English proof (translation)
Introduce `lam0 f r g Cg L b hf h1 h2`. Establish `hfr : 0 ≤ f * r ^ 2` using `mul_nonneg hf (sq_nonneg r)`. Establish `h3 : f * r ^ 2 * Real.log g ≤ f * r ^ 2 * (Cg * L)` using `mul_le_mul_of_nonneg_left h2 hfr`. Conclude with `⟨by linarith, by linarith, fun hb => by linarith⟩`.
-/
theorem passage_lambda : PassageLam := by
  intro lam0 f r g Cg L b hf h1 h2
  have hfr : 0 ≤ f * r ^ 2 := mul_nonneg hf (sq_nonneg r)
  have h3 : f * r ^ 2 * Real.log g ≤ f * r ^ 2 * (Cg * L) := mul_le_mul_of_nonneg_left h2 hfr
  exact ⟨by linarith, by linarith, fun hb => by linarith⟩

/- English proof (translation)
Introduce `J Pl _ _ muC mu0 HH0 lam0 logκ de Cd r g k p2 Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps pq w h1 hJ hPl hpq hW hw hLa hFo hC0 hEb hWb hF hNc hB0 hxe hxe0 hHH hCd hr hk hb hde hg hl0 hlb hA hB hcmp`. Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hf0 : 0 ≤ f` using `le_trans (Nat.cast_nonneg _) hPl`. Establish `hsz` using `passage_size J Pl mu0 logκ Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps pq w h1 hJ hPl hpq hW hw hLa hFo hC0 hEb`. Establish `hmu` using `hsz.2 hWb hb0 hF hNc hB0 hxe hxe0`.

Take `⟨_, _, hmuC, hd1, hLp⟩` from `passage_arithmetic muC mu0 HH0 lam0 logκ de 3 28 28 Cd f r g k b (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) p2 28 (by norm_num) (by norm_num) hCd hf0 hr hk hb hde hg hl0 hlb hmu hHH hA hB hcmp le_rfl`. Conclude with `⟨hmuC, hLp, by linarith⟩`.
-/
theorem passage_chain : PassageChain := by
  intro J Pl _ _ muC mu0 HH0 lam0 logκ de Cd r g k p2 Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF
    pN x eps pq w h1 hJ hPl hpq hW hw hLa hFo hC0 hEb hWb hF hNc hB0 hxe hxe0 hHH hCd hr hk hb hde
    hg hl0 hlb hA hB hcmp
  have hb0 : 0 ≤ b := by linarith
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hPl
  have hsz := passage_size J Pl mu0 logκ Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps
    pq w h1 hJ hPl hpq hW hw hLa hFo hC0 hEb
  have hmu := hsz.2 hWb hb0 hF hNc hB0 hxe hxe0
  obtain ⟨_, _, hmuC, hd1, hLp⟩ := passage_arithmetic muC mu0 HH0 lam0 logκ de 3 28 28 Cd f r g k b
    (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) p2 28 (by norm_num) (by norm_num)
    hCd hf0 hr hk hb hde hg hl0 hlb hmu hHH hA hB hcmp le_rfl
  exact ⟨hmuC, hLp, by linarith⟩

/- English proof (translation)
Introduce `muC mu0 HH0 lam0 de c1 c2 c3 τ0 τs`. Establish `e : (mu0 + τ0) + (HH0 - τ0) + c2 * lam0 = mu0 + HH0 + c2 * lam0` using `by ring`. Use `⟨e, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`.
-/
theorem passage_scale_free : PassageScaleFree := by
  intro muC mu0 HH0 lam0 de c1 c2 c3 τ0 τs
  have e : (mu0 + τ0) + (HH0 - τ0) + c2 * lam0 = mu0 + HH0 + c2 * lam0 := by ring
  refine ⟨e, ?_⟩
  rw [e]
  constructor <;> intro h <;> linarith

/- English proof (translation)
Introduce `mu0 HH0 lam0 logκ c2 cq f r g k b p1 p2 hc2 hk hb hg hlam hmu hHH`. Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hcl : c2 * lam0 ≤ c2 * b` using `mul_le_mul_of_nonneg_left hlam hc2`. Use `⟨by linarith, fun hP => by nlinarith [mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hb)], fun h => ?_⟩` and prove the remaining obligations. Establish `hkb0 : 0 ≤ k * b` using `by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]`.

Establish `h1 : cq * f * r * (p1 + p2 + c2) * b ≤ (k * b) ^ 7 * b` using `mul_le_mul_of_nonneg_right h hb0`. Establish `h2 : (k * b) ^ 7 * b ≤ (k * b) ^ 7 * (k * b)` using `mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]) (pow_nonneg hkb0 7)`. Establish `h3 : (k * b) ^ 7 * (k * b) = (k * b) ^ 8` using `by ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem passage_quotient : PassageQ := by
  intro mu0 HH0 lam0 logκ c2 cq f r g k b p1 p2 hc2 hk hb hg hlam hmu hHH
  have hb0 : 0 ≤ b := by linarith
  have hcl : c2 * lam0 ≤ c2 * b := mul_le_mul_of_nonneg_left hlam hc2
  refine ⟨by linarith, fun hP => by nlinarith [mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hb)],
    fun h => ?_⟩
  have hkb0 : 0 ≤ k * b := by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]
  have h1 : cq * f * r * (p1 + p2 + c2) * b ≤ (k * b) ^ 7 * b := mul_le_mul_of_nonneg_right h hb0
  have h2 : (k * b) ^ 7 * b ≤ (k * b) ^ 7 * (k * b) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]) (pow_nonneg hkb0 7)
  have h3 : (k * b) ^ 7 * (k * b) = (k * b) ^ 8 := by ring
  calc cq * f * r * ((p1 + p2 + c2) * b) = cq * f * r * (p1 + p2 + c2) * b := by ring
    _ ≤ g := by linarith

/- English proof (translation)
Introduce `J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 Eb e6 eP logOm eK pq w eE δ logκ HH0 de c1 c2 c3 Cd r g p2 pF pN hc1 hc2 hc3 hCd hr hde hg hl0 hcmp hHH hpq hF hNc hA hB h1 hhu hK' hfa hP' hph hnν hx heps hL hb h …`. Establish `hL1 : 1 ≤ L`. Rewrite using `[hL]`. Conclude with `Real.one_le_rpow hx heps.le`. Establish `hb1 : 1 ≤ b`.

Rewrite using `[hb]`. Conclude with `Real.one_le_exp (by linarith)`. Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hxe0 : 0 ≤ xe` using `le_trans (Real.rpow_nonneg (by linarith) eps) hxe`. Establish `hf0 : 0 ≤ f` using `by linarith`.

Establish `hmu : mu0 ≤ logκ + (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) * b` using `(passage_size J Pl mu0 logκ Fo Fo Eb logOm La (2 * b) b N m f C0 xe B0 Nc pF pN x eps pq w h1 hJ hPl hpq (by linarith) hw hlogOm le_rfl hC0 hEb).2 le_rfl hb0 hF hNc hB0 hxe hxe0`. Take `⟨_, _, hmuC, _, hLp⟩` from `passage_arithmetic muC mu0 HH0 lam0 logκ de c1 c2 c3 Cd f r g k b (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) p2 C0 hc1 hc2 hCd hf0 hr hk hb1 hde hg hl0 hlb hmu hHH hA hB hcmp hc3`. Establish `key` using `divisor_inequality J Pl TT (muC - logκ) (mu0 - logκ) Fo (hP + ∑ j, hK j - mlam) hP mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 (c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0) Eb e6 eP logOm eK pq w eE δ (by linarith) (by linarith) rfl hK' …`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem divisor_inequality_passage : DivIneqPassage := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S
    tt η w'' b' dC lam0 C0 Eb e6 eP logOm eK pq w eE δ logκ HH0 de c1 c2 c3 Cd r g p2 pF pN hc1 hc2
    hc3 hCd hr hde hg hl0 hcmp hHH hpq hF hNc hA hB h1 hhu hK' hfa hP' hph hnν hx heps hL hb ha hrd
    hlrd hlx hLa hB0 hNc0 hxe hJ hPl hm hf hk hN hS htt hη hdC hw hpqk hlogOm hlb hN2 hm3 hmη hkN
    hkS hmt hNw hbN hmkb hC0 hEb heK he6 heP heE hδ
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact Real.one_le_rpow hx heps.le
  have hb1 : 1 ≤ b := by
    rw [hb]
    exact Real.one_le_exp (by linarith)
  have hb0 : 0 ≤ b := by linarith
  have hxe0 : 0 ≤ xe := le_trans (Real.rpow_nonneg (by linarith) eps) hxe
  have hf0 : 0 ≤ f := by linarith
  have hmu : mu0 ≤ logκ + (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) * b :=
    (passage_size J Pl mu0 logκ Fo Fo Eb logOm La (2 * b) b N m f C0 xe B0 Nc pF pN x eps pq w
      h1 hJ hPl hpq (by linarith) hw hlogOm le_rfl hC0 hEb).2 le_rfl hb0 hF hNc hB0 hxe hxe0
  obtain ⟨_, _, hmuC, _, hLp⟩ := passage_arithmetic muC mu0 HH0 lam0 logκ de c1 c2 c3 Cd f r g k b
    (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) p2 C0 hc1 hc2 hCd hf0 hr hk hb1
    hde hg hl0 hlb hmu hHH hA hB hcmp hc3
  have key := divisor_inequality J Pl TT (muC - logκ) (mu0 - logκ) Fo (hP + ∑ j, hK j - mlam) hP
    mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0
    (c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0) Eb e6 eP logOm eK pq w eE δ
    (by linarith) (by linarith) rfl hK' hfa hP' hph hnν hx heps hL hb ha hrd hlrd hlx hLa hB0 hNc0
    hxe hJ hPl hm hf hk hN hS htt hη hdC hw hpqk hlogOm hlb hN2 hm3 hmη hkN hkS hmt hNw hbN hmkb hC0
    hLp hEb heK he6 heP heE hδ
  linarith

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]`. Establish `h : ((s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one]`. Rewrite using `[h, one_smul]`.
-/
theorem inv_inv_real_smul {d : ℕ} (s : ℝ) (hs : 0 < s) (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A.det) :
    (((s⁻¹ : ℝ) : ℂ) • A)⁻¹ = ((s : ℝ) : ℂ) • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]
  have h : ((s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one]
  rw [h, one_smul]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]`. Establish `h : ((s⁻¹ : ℝ) : ℂ) * ((s : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne', Complex.ofReal_one]`. Rewrite using `[h, one_smul]`.
-/
theorem inv_real_smul_inv {d : ℕ} (s : ℝ) (hs : 0 < s) (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A.det) :
    (((s : ℝ) : ℂ) • A)⁻¹ = ((s⁻¹ : ℝ) : ℂ) • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]
  have h : ((s⁻¹ : ℝ) : ℂ) * ((s : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne', Complex.ofReal_one]
  rw [h, one_smul]

/- English proof (translation)
The claim follows from `inv_inv_real_smul _ (Real.sqrt_pos.mpr (ht v)) (X v) (hX v)`.
-/
theorem scaleFrame_inv {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    (scaleFrame t X v)⁻¹ = ((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹ :=
  inv_inv_real_smul _ (Real.sqrt_pos.mpr (ht v)) (X v) (hX v)

/- English proof (translation)
Establish `hc : (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (ht v)).ne')`. Use `show IsUnit ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v).det`. Rewrite using `[Matrix.det_smul]`. Conclude with `((isUnit_iff_ne_zero.mpr hc).pow _).mul (hX v)`.
-/
theorem scaleFrame_det_isUnit {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    IsUnit (scaleFrame t X v).det := by
  have hc : (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (ht v)).ne')
  show IsUnit ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v).det
  rw [Matrix.det_smul]
  exact ((isUnit_iff_ne_zero.mpr hc).pow _).mul (hX v)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Use `show ((((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v)).transpose)⁻¹ = ((Real.sqrt (t v) : ℝ) : ℂ) • ((X v).transpose)⁻¹`. Rewrite using `[Matrix.transpose_smul]`. Conclude with `inv_inv_real_smul _ (Real.sqrt_pos.mpr (ht v)) _ (by rw [Matrix.det_transpose]; exact hX v)`.
-/
theorem dualFrame_scaleFrame {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Formalism.HN.dualFrame (scaleFrame t X) =
      fun v => ((Real.sqrt (t v) : ℝ) : ℂ) • Formalism.HN.dualFrame X v := by
  funext v
  show ((((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v)).transpose)⁻¹ =
    ((Real.sqrt (t v) : ℝ) : ℂ) • ((X v).transpose)⁻¹
  rw [Matrix.transpose_smul]
  exact inv_inv_real_smul _ (Real.sqrt_pos.mpr (ht v)) _ (by rw [Matrix.det_transpose]; exact hX v)

/- English proof (translation)
Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]`.
-/
theorem sqrt_mul_sqrt_complex (s : ℝ) (hs : 0 < s) : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]

/- English proof (translation)
Unfold `meanLog`. Establish `h : ∑ v, Real.log (Real.sqrt (t v)) = (∑ v, Real.log (t v)) / 2`. Rewrite using `[Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun v _ => Real.log_sqrt (ht v).le`. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mean_log_sqrt (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) :
    2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Real.sqrt (t v))) = meanLog t := by
  unfold meanLog
  have h : ∑ v, Real.log (Real.sqrt (t v)) = (∑ v, Real.log (t v)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => Real.log_sqrt (ht v).le
  rw [h]
  ring

/- English proof (translation)
Unfold `meanLog`. Establish `h : ∑ v, Real.log (Real.sqrt (t v))⁻¹ = -((∑ v, Real.log (t v)) / 2)`. Rewrite using `[Finset.sum_div, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun v _ => by rw [Real.log_inv, Real.log_sqrt (ht v).le]`. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mean_log_sqrt_inv (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) :
    2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Real.sqrt (t v))⁻¹) = -meanLog t := by
  unfold meanLog
  have h : ∑ v, Real.log (Real.sqrt (t v))⁻¹ = -((∑ v, Real.log (t v)) / 2) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [Real.log_inv, Real.log_sqrt (ht v).le]
  rw [h]
  ring

/- English proof (translation)
Establish `hs` using `scaleFrame_inv t ht X hX v`. Establish `hmv : ∀ (u : Fin d → ℂ) (i : Fin d), ((((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹) *ᵥ u) i = ((Real.sqrt (t v) : ℝ) : ℂ) * (((X v)⁻¹) *ᵥ u) i`. Introduce `u i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`. Use extensionality with `a c`.

Simplify using `only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hs, hmv, star_mul', map_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← sqrt_mul_sqrt_complex (t v) (ht v)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_scaleFrame [StarRing K] {d m : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (e : Fin m → Fin d → K) :
    gram (scaleFrame t X) v e = (t v : ℂ) • gram X v e := by
  have hs := scaleFrame_inv t ht X hX v
  have hmv : ∀ (u : Fin d → ℂ) (i : Fin d), ((((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹) *ᵥ u) i =
      ((Real.sqrt (t v) : ℝ) : ℂ) * (((X v)⁻¹) *ᵥ u) i := by
    intro u i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  ext a c
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, hs, hmv, star_mul', map_mul, Complex.star_def,
    Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sqrt_mul_sqrt_complex (t v) (ht v)]
  ring

/- English proof (translation)
Unfold `meanLog`. Rewrite using `[← mul_add, ← Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun v _ => Real.log_mul (ht v).ne' (hκ v).ne'`.
-/
theorem meanLog_mul (t κ : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) (hκ : ∀ v, 0 < κ v) :
    meanLog (fun v => t v * κ v) = meanLog t + meanLog κ := by
  unfold meanLog
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ => Real.log_mul (ht v).ne' (hκ v).ne'

/- English proof (translation)
Unfold `Formalism.HN.opNormAt`. Rewrite using `[hY', inv_real_smul_inv s hs (Y v) hY, Matrix.smul_mul, Matrix.smul_mul, map_smul, map_smul, norm_smul, Complex.norm_of_nonneg (inv_nonneg.mpr hs.le)]`.
-/
theorem opNormAt_scale_alt [StarRing K] {n D : ℕ} (s : ℝ) (hs : 0 < s)
    (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y Y' : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (v : InfinitePlace K)
    (hY : IsUnit (Y v).det) (hY' : Y' v = ((s : ℝ) : ℂ) • Y v)
    (φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K)) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y' v φ =
      s⁻¹ * Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y v φ := by
  unfold Formalism.HN.opNormAt
  rw [hY', inv_real_smul_inv s hs (Y v) hY, Matrix.smul_mul, Matrix.smul_mul, map_smul, map_smul,
    norm_smul, Complex.norm_of_nonneg (inv_nonneg.mpr hs.le)]

/- English proof (translation)
Unfold `Formalism.HN.opNormAt`. Rewrite using `[norm_pos_iff]`. Introduce `h0`. Apply `hφ` to reduce the goal to its premises. Establish `hA : (Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ).map v.embedding * XN v = 0` using `(Matrix.toEuclideanLin).map_eq_zero_iff.mp (LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp h0)`.

Establish `hM : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ).map v.embedding = 0`. Establish `e1 : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ).map v.embedding = Y v * ((Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ).map v.embedding * XN v) * (XN v)⁻¹`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXN, Matrix.mul_one]`. Rewrite using `[e1, hA, Matrix.mul_zero, Matrix.zero_mul]`. Establish `hT : LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ = 0`.

Use extensionality with `i j`. Establish `h1` using `congrArg (fun A => A i j) hM`. Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at h1`. Conclude with `(map_eq_zero_iff _ v.embedding.injective).mp h1`. Conclude with `(LinearMap.toMatrix _ _).map_eq_zero_iff.mp hT`.
-/
theorem opNormAt_pos_alt [StarRing K] {n D : ℕ}
    (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (v : InfinitePlace K)
    (hXN : IsUnit (XN v).det) (hY : IsUnit (Y v).det)
    (φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K)) (hφ : φ ≠ 0) :
    0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y v φ := by
  unfold Formalism.HN.opNormAt
  rw [norm_pos_iff]
  intro h0
  apply hφ
  have hA : (Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
      φ).map v.embedding * XN v = 0 :=
    (Matrix.toEuclideanLin).map_eq_zero_iff.mp (LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp h0)
  have hM : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
      φ).map v.embedding = 0 := by
    have e1 : (LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis
        φ).map v.embedding = Y v * ((Y v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K (Fin n))
        (Pi.basisFun K (Fin D)).dualBasis φ).map v.embedding * XN v) * (XN v)⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXN, Matrix.mul_one]
    rw [e1, hA, Matrix.mul_zero, Matrix.zero_mul]
  have hT : LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin D)).dualBasis φ = 0 := by
    ext i j
    have h1 := congrArg (fun A => A i j) hM
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1
    exact (map_eq_zero_iff _ v.embedding.injective).mp h1
  exact (LinearMap.toMatrix _ _).map_eq_zero_iff.mp hT

end SlopeTestRemainingChoices

/- English proof (translation)
Use `⟨hR.fg, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Use `haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩`. Establish `h` using `hR.span_eq_top`. Rewrite `h` using `[Submodule.bot_coe, Submodule.span_zero_singleton]`.

Conclude with `bot_ne_top h`.
-/
theorem lattice_fg_ne_bot {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {D : ℕ}
    (hD : 0 < D) (R : Submodule (𝓞 K) (Fin D → K)) (hR : Submodule.IsLattice K R) :
    R.FG ∧ R ≠ ⊥ := by
  refine ⟨hR.fg, ?_⟩
  rintro rfl
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have h := hR.span_eq_top
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at h
  exact bot_ne_top h

/- English proof (translation)
Introduce `K _ _ _ _ D hD XE hXE t ht`. Establish `hsq : ∀ v, 0 < Real.sqrt (t v)` using `fun v => Real.sqrt_pos.mpr (ht v)`. Establish `hXd : ∀ v, IsUnit (Formalism.HN.dualFrame XE v).det`. Introduce `v`. Simplify using `only [Formalism.HN.dualFrame]`.

Rewrite using `[Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]`. Conclude with `hXE v`. Establish `hdual : ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R → Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE)) (Formalism.HN.dualLat R) = Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formal …`. Introduce `R hR`. Establish `hfg : R.FG` using `Submodule.IsLattice.fg (self := hR)`.

Establish `hspan : Submodule.span K (R : Set (Fin D → K)) = ⊤` using `Submodule.IsLattice.span_eq_top (self := hR)`. Take `⟨hdfg, hdspan, -⟩` from `Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE hXE R hfg hspan`. Establish `hne : Formalism.HN.dualLat R ≠ ⊥`. Introduce `h`. Establish `h2 : Submodule.span K (((⊥ : Submodule (𝓞 K) (Module.Dual K (Fin D → K)))) : Set (Module.Dual K (Fin D → K))) = ⊥` using `by simp`.

Rewrite `hdspan` using `[h, h2]`. Establish `h1 : finrank K (Module.Dual K (Fin D → K)) = D`. Simplify using `[Subspace.dual_finrank_eq]`. Establish `h3` using `congrArg (fun U : Submodule K (Module.Dual K (Fin D → K)) => finrank K U) hdspan`. Simplify using `only [finrank_bot, finrank_top, h1] at h3`.

Use linear arithmetic over natural numbers and integers. Take `⟨-, -, h, -⟩` from `Formalism.HN.twist K (Module.Dual K (Fin D → K)) (Fin D) (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (fun v => Real.sqrt (t v)) hXd hsq (Formalism.HN.dualLat R) hdfg`. Establish `h1` using `(h hne).1`. Rewrite using `[dualFrame_scaleFrame t ht XE hXE, h1, mean_log_sqrt t ht]`. Use `⟨fun v => ⟨scaleFrame_det_isUnit t ht XE hXE v, ?_⟩, ?_, fun κ hκ => meanLog_mul t κ ht hκ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[scaleFrame_inv t ht XE hXE v, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_ofReal, sqrt_mul_sqrt_complex _ (ht v)]`. Introduce `d XS φ v`. Simplify using `only [detRatio, gram_scaleFrame t ht XE hXE v, Matrix.det_smul, Fintype.card_fin]`. Rewrite using `[← Complex.ofReal_pow, Complex.re_ofReal_mul, mul_div_assoc]`. Introduce `R hR`.

Take `⟨hfg, hne⟩` from `lattice_fg_ne_bot hD R hR`. Take `⟨-, -, h, -⟩` from `Formalism.HN.twist K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE (fun v => (Real.sqrt (t v))⁻¹) hXE (fun v => inv_pos.mpr (hsq v)) R hfg`. Take `⟨h1, h2, -⟩` from `h hne`. Establish `hDr : (D : ℝ) ≠ 0` using `by exact_mod_cast hD.ne'`. Use `⟨?_, hdual R hR, ?_, ?_⟩` and prove the remaining obligations.

Establish `e1` using `dual_lattice_measure K D hD XE hXE R hR`. Establish `e2` using `dual_lattice_measure K D hD (scaleFrame t XE) (scaleFrame_det_isUnit t ht XE hXE) R hR`. Rewrite `e2` using `[hdual R hR, e1]`. Clear denominators, using `at e2` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v` using `rfl`. Rewrite using `[this, h1, mean_log_sqrt_inv t ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `: scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v` using `rfl`. Rewrite using `[this, h2, mean_log_sqrt_inv t ht]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `n XN hXN φ hφ`. Establish `hop : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE)) v φ ^ 2) = Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v …`. Introduce `v`. Establish `hp` using `opNormAt_pos_alt XN (Formalism.HN.dualFrame XE) v (hXN v) (hXd v) φ hφ`.

Rewrite using `[opNormAt_scale_alt (Real.sqrt (t v)) (hsq v) XN (Formalism.HN.dualFrame XE) _ v (hXd v) (by rw [dualFrame_scaleFrame t ht XE hXE]) φ, mul_pow, inv_pow, Real.sq_sqrt (ht v).le, Real.log_mul (inv_pos.mpr (ht v)).ne' (pow_pos hp 2).ne', Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Formalism.HN.htMap, hop, Finset.sum_sub_distrib, meanLog]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kappa_invariance : KappaInvariance := by
  intro K _ _ _ _ D hD XE hXE t ht
  have hsq : ∀ v, 0 < Real.sqrt (t v) := fun v => Real.sqrt_pos.mpr (ht v)
  have hXd : ∀ v, IsUnit (Formalism.HN.dualFrame XE v).det := by
    intro v
    simp only [Formalism.HN.dualFrame]
    rw [Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]
    exact hXE v

  have hdual : ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE))
                (Formalism.HN.dualLat R) =
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
          meanLog t := by
    intro R hR
    have hfg : R.FG := Submodule.IsLattice.fg (self := hR)
    have hspan : Submodule.span K (R : Set (Fin D → K)) = ⊤ :=
      Submodule.IsLattice.span_eq_top (self := hR)
    obtain ⟨hdfg, hdspan, -⟩ :=
      Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE hXE R hfg hspan
    have hne : Formalism.HN.dualLat R ≠ ⊥ := by
      intro h
      have h2 : Submodule.span K (((⊥ : Submodule (𝓞 K) (Module.Dual K (Fin D → K)))) :
          Set (Module.Dual K (Fin D → K))) = ⊥ := by simp
      rw [h, h2] at hdspan
      have h1 : finrank K (Module.Dual K (Fin D → K)) = D := by
        simp [Subspace.dual_finrank_eq]
      have h3 := congrArg (fun U : Submodule K (Module.Dual K (Fin D → K)) => finrank K U) hdspan
      simp only [finrank_bot, finrank_top, h1] at h3
      omega
    obtain ⟨-, -, h, -⟩ := Formalism.HN.twist K (Module.Dual K (Fin D → K)) (Fin D)
      (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (fun v => Real.sqrt (t v)) hXd hsq
      (Formalism.HN.dualLat R) hdfg
    have h1 := (h hne).1
    rw [dualFrame_scaleFrame t ht XE hXE, h1, mean_log_sqrt t ht]
  refine ⟨fun v => ⟨scaleFrame_det_isUnit t ht XE hXE v, ?_⟩, ?_, fun κ hκ => meanLog_mul t κ ht hκ, ?_, ?_⟩
  · rw [scaleFrame_inv t ht XE hXE v, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Complex.star_def, Complex.conj_ofReal, sqrt_mul_sqrt_complex _ (ht v)]
  · intro d XS φ v
    simp only [detRatio, gram_scaleFrame t ht XE hXE v, Matrix.det_smul, Fintype.card_fin]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, mul_div_assoc]
  · intro R hR
    obtain ⟨hfg, hne⟩ := lattice_fg_ne_bot hD R hR
    obtain ⟨-, -, h, -⟩ := Formalism.HN.twist K (Fin D → K) (Fin D)
      (Pi.basisFun K (Fin D)) XE (fun v => (Real.sqrt (t v))⁻¹) hXE (fun v => inv_pos.mpr (hsq v))
      R hfg
    obtain ⟨h1, h2, -⟩ := h hne
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    refine ⟨?_, hdual R hR, ?_, ?_⟩
    · have e1 := dual_lattice_measure K D hD XE hXE R hR
      have e2 := dual_lattice_measure K D hD (scaleFrame t XE) (scaleFrame_det_isUnit t ht XE hXE) R hR
      rw [hdual R hR, e1] at e2
      field_simp at e2
      linarith
    · have : scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v := rfl
      rw [this, h1, mean_log_sqrt_inv t ht]; ring
    · have : scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v := rfl
      rw [this, h2, mean_log_sqrt_inv t ht]; ring
  · intro n XN hXN φ hφ
    have hop : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE)) v φ ^ 2) =
        Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v φ ^ 2) - Real.log (t v) := by
      intro v
      have hp := opNormAt_pos_alt XN (Formalism.HN.dualFrame XE) v (hXN v) (hXd v) φ hφ
      rw [opNormAt_scale_alt (Real.sqrt (t v)) (hsq v) XN (Formalism.HN.dualFrame XE) _ v (hXd v)
        (by rw [dualFrame_scaleFrame t ht XE hXE]) φ, mul_pow, inv_pow, Real.sq_sqrt (ht v).le,
        Real.log_mul (inv_pos.mpr (ht v)).ne' (pow_pos hp 2).ne', Real.log_inv]
      ring
    simp only [Formalism.HN.htMap, hop, Finset.sum_sub_distrib, meanLog]
    ring

/- English proof (translation)
Unfold `meanLog`. Simplify using `only [Real.log_inv, Finset.sum_neg_distrib, mul_neg]`.
-/
theorem meanLog_inv {K : Type} [Field K] [NumberField K] (κ : InfinitePlace K → ℝ) :
    meanLog (fun v => (κ v)⁻¹) = -meanLog κ := by
  unfold meanLog
  simp only [Real.log_inv, Finset.sum_neg_distrib, mul_neg]

/- English proof (translation)
Introduce `K _ _ _ _ D hD XE hXE κ hκ`. Take `⟨h1, h2, -, h4, h5⟩` from `kappa_invariance K D hD XE hXE (fun v => (κ v)⁻¹) (fun v => inv_pos.mpr (hκ v))`. Rewrite `h4`, `h5` using `[meanLog_inv]`. Use `⟨fun v => (h1 v).1, ?_, ?_, by simp [meanLog], ?_⟩` and prove the remaining obligations. Introduce `XS φ v ρ P h`.

Rewrite using `[h2 D XS φ v, h, mul_pow, mul_pow, one_pow, inv_pow]`. Establish `: κ v ^ D ≠ 0` using `pow_ne_zero _ (hκ v).ne'`. Clear the denominators using the available nonvanishing facts. Introduce `XS φ v P h`. Rewrite using `[h2 D XS φ v, h, one_pow, inv_pow]`.

Establish `: κ v ^ D ≠ 0` using `pow_ne_zero _ (hκ v).ne'`. Clear the denominators using the available nonvanishing facts. Introduce `R hR`. Take `⟨-, e2, -, e4⟩` from `h4 R hR`. Use `⟨by rw [e2]; ring, by rw [e4]; ring, by rw [e2, e4]; ring, ?_⟩` and prove the remaining obligations.

Introduce `n XN hXN φ hφ`. Establish `e5` using `h5 n XN hXN φ hφ`. Conclude with `⟨by rw [e5]; ring, by rw [e2, e5]; ring⟩`.
-/
theorem kappa_normalise : KappaNormalise := by
  intro K _ _ _ _ D hD XE hXE κ hκ
  obtain ⟨h1, h2, -, h4, h5⟩ := kappa_invariance K D hD XE hXE (fun v => (κ v)⁻¹)
    (fun v => inv_pos.mpr (hκ v))
  rw [meanLog_inv] at h4 h5
  refine ⟨fun v => (h1 v).1, ?_, ?_, by simp [meanLog], ?_⟩
  · intro XS φ v ρ P h
    rw [h2 D XS φ v, h, mul_pow, mul_pow, one_pow, inv_pow]
    have : κ v ^ D ≠ 0 := pow_ne_zero _ (hκ v).ne'
    field_simp
  · intro XS φ v P h
    rw [h2 D XS φ v, h, one_pow, inv_pow]
    have : κ v ^ D ≠ 0 := pow_ne_zero _ (hκ v).ne'
    field_simp
  · intro R hR
    obtain ⟨-, e2, -, e4⟩ := h4 R hR
    refine ⟨by rw [e2]; ring, by rw [e4]; ring, by rw [e2, e4]; ring, ?_⟩
    intro n XN hXN φ hφ
    have e5 := h5 n XN hXN φ hφ
    exact ⟨by rw [e5]; ring, by rw [e2, e5]; ring⟩

end Formalism.DivisionValues
