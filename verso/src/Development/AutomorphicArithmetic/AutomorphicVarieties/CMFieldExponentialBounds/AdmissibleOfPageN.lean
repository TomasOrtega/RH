import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.logpair
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.bigpair
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.LogConductorMulHeightLeOfPageN
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.minusle
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ErrorTermsLeSqrtExpRpow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ConductorBoundsOfIsChiField
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.IsCMFieldOfIsChiField

noncomputable section

open NumberField

namespace UpperTheory.V

open Formalism.HC UpperTheory.Top

/- English proof (translation)
Introduce `Ω _ _ _ ld`. Take `⟨h1, h2⟩` from `h Ω ld`. Conclude with `⟨h1, fun S hS => (h2 S hS).trans hB⟩`.
-/
theorem VVminusLe.mono {E : Type} [Field E] [NumberField E] [IsCMField E] {t : ℕ} {B B' : ℝ} (h : VVminusLe E t B)
    (hB : B ≤ B') : VVminusLe E t B' := by
  intro Ω _ _ _ ld
  obtain ⟨h1, h2⟩ := h Ω ld
  exact ⟨h1, fun S hS => (h2 S hS).trans hB⟩

/- English proof (translation)
Introduce `x hx`. Establish `hx1 : (1 : ℝ) ≤ x` using `by linarith`. Take `⟨a, b⟩` from `he x hx1`. Establish `h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `h3 : x ^ (2 + 8 * eps) ≤ x ^ (3 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`.

Establish `h4 : x ^ (4 : ℝ) = x * x ^ (3 : ℝ)`. Rewrite using `[show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]`. Establish `h5 : (0 : ℝ) ≤ x ^ (3 : ℝ)` using `by positivity`. Establish `h6 : x ≤ x ^ Ct` using `Real.self_le_rpow_of_one_le hx1 hC`. Establish `h8 : 2 * x ^ (3 : ℝ) ≤ x * x ^ (3 : ℝ)` using `mul_le_mul_of_nonneg_right hx h5`.

Use `⟨?_, b.trans ((mul_le_mul_of_nonneg_left h3 zero_le_two).trans (h8.trans h4.ge)), Nat.le_floor (by push_cast; linarith), Nat.floor_le (by linarith)⟩` and prove the remaining obligations. Rewrite `h2` using `[Real.rpow_two]`. Establish `h7 : (2 : ℝ) ^ 2 ≤ 2 ^ e x` using `by nlinarith`. Conclude with `(pow_le_pow_iff_right₀ (by norm_num)).1 h7`.
-/
theorem admissible_of_pageN {eps Ct : ℝ} (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : 1 ≤ Ct) {e : ℝ → ℕ}
    (he : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) : admitted 4 Ct e fun x => ⌊x ^ Ct⌋₊ := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  obtain ⟨a, b⟩ := he x hx1
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h3 : x ^ (2 + 8 * eps) ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h4 : x ^ (4 : ℝ) = x * x ^ (3 : ℝ) := by
    rw [show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have h5 : (0 : ℝ) ≤ x ^ (3 : ℝ) := by positivity
  have h6 : x ≤ x ^ Ct := Real.self_le_rpow_of_one_le hx1 hC
  have h8 : 2 * x ^ (3 : ℝ) ≤ x * x ^ (3 : ℝ) := mul_le_mul_of_nonneg_right hx h5
  refine ⟨?_, b.trans ((mul_le_mul_of_nonneg_left h3 zero_le_two).trans (h8.trans h4.ge)), Nat.le_floor (by push_cast; linarith), Nat.floor_le (by linarith)⟩
  rw [Real.rpow_two] at h2
  have h7 : (2 : ℝ) ^ 2 ≤ 2 ^ e x := by nlinarith
  exact (pow_le_pow_iff_right₀ (by norm_num)).1 h7

/- English proof (translation)
Introduce `eps h0 h1 e he`. Use `set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht`. Establish `hadm : admitted 4 Ct e t` using `admissible_of_pageN h0 h1 hC he`. Take `⟨J, C, P, XJ, hJ0, hmain⟩` from `hJ ψ eps 4 h0 h1 e t hadm`. Take `⟨Cb, hCb⟩` from `hc`.

Take `⟨K, hK0, hK⟩` from `minusBound_le_exp_of_log_le Cb (AbF.ofChar ψ).deg`. Take `⟨xT, hxT⟩` from `error_terms_le_sqrt_exp_rpow eps K C h0`. Take `⟨xN, hxN⟩` from `log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1`. Take `⟨Y0, hY0⟩` from `log_mul_le_rpow_of_winPair eps h0`. Take `⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J'` from `⟨max J 1, le_max_right _ _, le_max_left _ _⟩`.

Establish `hJ'0 : 0 < J'` using `by linarith`. Take `⟨P', hPP', hNP'⟩ : ∃ P' : ℝ, P ≤ P' ∧ (ψ.N : ℝ) ≤ P'` from `⟨max P (ψ.N : ℝ), le_max_left _ _, le_max_right _ _⟩`. Take `⟨XB, hXB⟩` from `eventually_winPair_gt_power eps J' Ct P' h0 hJ'0`. Take `⟨L, hxTL, hxNL, hY0L, h2L⟩ : ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L` from `⟨max (max xT xN) (max Y0 2), le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _), le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩`. Establish `hL1 : (1 : ℝ) ≤ L` using `by linarith`.

Establish `hL0 : (0 : ℝ) ≤ L` using `by linarith`. Use `⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩` and prove the remaining obligations. Introduce `X hX q d hw`. Establish `hXJ : XJ ≤ X` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX`. Establish `hXB' : XB ≤ X` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX`.

Establish `hXL : L ^ J' ≤ X` using `le_trans (le_max_right _ _) hX`. Establish `hLX : L ≤ X ^ (1 / J')`. Use `Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))` as an intermediate fact. Rewrite `this` using `[← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one]`. Then use the resulting hypothesis. Establish `hX1 : 1 ≤ X`.

Establish `: 1 ≤ L ^ J'` using `Real.one_le_rpow hL1 hJ'0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX0 : (0 : ℝ) ≤ X` using `by linarith`. Take `⟨hq3, hd3, hPq, hPd⟩` from `hXB X hXB' q d hw`. Establish `hlog` using `hY0 _ (hY0L.trans hLX) q d hw`.

Establish `hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J'))`. Rewrite using `[← Real.rpow_mul hX0]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J))` using `Real.rpow_le_rpow_of_exponent_le hX1 (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))`.

Establish `hlogJ : Real.log (↑q * ↑d) ≤ X ^ (eps / (4 * J))`. Rewrite `hlog` using `[hpow]`. Conclude with `hlog.trans hmono`. Establish `hN0 : 0 < ψ.N` using `(AbF.ofChar ψ).pos`. Establish `hcop : ∀ r : ℕ, Nat.Prime r → (ψ.N : ℝ) < r → Nat.Coprime r ψ.N`.

Introduce `r hr hlt`. Establish `hlt' : ψ.N < r` using `by exact_mod_cast hlt`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hr).2 (fun hdvd => absurd (Nat.le_of_dvd hN0 hdvd) (not_le.2 hlt'))`. Establish `hpp : PrimePair ψ.N q d` using `⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod, Nat.Coprime.mul (hcop q hw.q_prime (lt_of_le_of_lt hNP' hPq)) (hcop d hw.d_prime (lt_of_le_of_lt hNP' hPd))⟩`. Take `⟨Y, ⟨hYlo, hYhi⟩, hY⟩` from `hmain X hXJ q d hpp hq3 hd3 (lt_of_le_of_lt hPP' hPq) (lt_of_le_of_lt hPP' hPd) hlogJ`.

Establish `hWY : X ^ (1 / J') ≤ Y` using `le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo`. Use `⟨Y, hWY, hYhi, ?_⟩` and prove the remaining obligations. Introduce `x hxY hxY2`. Establish `hWx : X ^ (1 / J') ≤ x` using `hWY.trans hxY`. Establish `hLx : L ≤ x` using `hLX.trans hWx`.

Establish `hx2 : 2 ≤ x` using `h2L.trans hLx`. Establish `hx1 : 1 ≤ x` using `by linarith`. Take `⟨hBa, hHV⟩` from `hY x hxY hxY2`. Introduce `E _ _ hE`. Establish `hq0 : 0 < q` using `hw.q_prime.pos`.

Establish `hd0 : 0 < d` using `hw.d_prime.pos`. Establish `hq4 : q % 4 = 3`. Use `hw.q_mod` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `haveI : IsCMField E := isCMField_of_isChiField ψ (e x) q d hw.q_prime hq4 E hE`.

Establish `hE' : IsCompField (AbF.ofChar ψ) (e x) q d E` using `(isCompField_ofChar ψ (e x) q d E).2 hE`. Establish `h2` using `hBa E hE'`. Establish `hp` using `hHV E hE`. Establish `hm` using `hCb (AbF.ofChar ψ) 4 e t hadm x hx2 q d hpp E hE'`. Take `⟨hc1, hc2, hc3⟩` from `conductor_bounds_of_isChiField ψ (e x) q d hq0 hd0 E hE`.

Take `⟨-, -, ht2, htle⟩` from `hadm x hx2`. Establish `ht1 : 1 ≤ t x` using `by omega`. Establish `hWpos : (0 : ℝ) ≤ X ^ (1 / J')` using `Real.rpow_nonneg hX0 _`. Establish `hqd : Real.log (↑q * ↑d) ≤ x ^ (eps / 4)`. Establish `hlog0` using `hY0 _ (hY0L.trans hLX) q d hw`.

Conclude with `hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))`. Establish `hNt` using `hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd`. Establish `hmb` using `hK (Module.finrank ℚ E) (condF E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt`. Establish `hm'` using `VVminusLe.mono hm hmb`. Establish `hv` using `vvle_of_parts h2 hm' hp`.

Establish `hu1 : (1 : ℝ) ≤ ↑(condF E) * ↑(t x)`. Establish `a : (1 : ℝ) ≤ condF E` using `by exact_mod_cast hc1`. Establish `b : (1 : ℝ) ≤ t x` using `by exact_mod_cast ht1`. Use the polynomial consequences of the given equalities and inequalities. Establish `htot` using `hxT x (hxTL.trans hLx) _ hu1 hNt`.

Conclude with `VVle.mono hv le_rfl htot`.
-/
theorem vwinAt_of_joint {Ct : ℝ} (hC : 1 ≤ Ct) (hJ : JointWin Ct) (hc : ThmBc Ct) (ψ : PChar) : VWinAt ψ Ct := by
  intro eps h0 h1 e he
  set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht
  have hadm : admitted 4 Ct e t := admissible_of_pageN h0 h1 hC he
  obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := hJ ψ eps 4 h0 h1 e t hadm
  obtain ⟨Cb, hCb⟩ := hc
  obtain ⟨K, hK0, hK⟩ := minusBound_le_exp_of_log_le Cb (AbF.ofChar ψ).deg
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps K C h0
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1
  obtain ⟨Y0, hY0⟩ := log_mul_le_rpow_of_winPair eps h0
  obtain ⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J' := ⟨max J 1, le_max_right _ _, le_max_left _ _⟩
  have hJ'0 : 0 < J' := by linarith
  obtain ⟨P', hPP', hNP'⟩ : ∃ P' : ℝ, P ≤ P' ∧ (ψ.N : ℝ) ≤ P' := ⟨max P (ψ.N : ℝ), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨XB, hXB⟩ := eventually_winPair_gt_power eps J' Ct P' h0 hJ'0
  obtain ⟨L, hxTL, hxNL, hY0L, h2L⟩ : ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L :=
    ⟨max (max xT xN) (max Y0 2), le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  refine ⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩
  intro X hX q d hw
  have hXJ : XJ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXB' : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXL : L ^ J' ≤ X := le_trans (le_max_right _ _) hX
  have hLX : L ≤ X ^ (1 / J') := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))
    rwa [← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one] at this
  have hX1 : 1 ≤ X := by
    have : 1 ≤ L ^ J' := Real.one_le_rpow hL1 hJ'0.le
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  obtain ⟨hq3, hd3, hPq, hPd⟩ := hXB X hXB' q d hw
  have hlog := hY0 _ (hY0L.trans hLX) q d hw
  have hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J')) := by
    rw [← Real.rpow_mul hX0]
    congr 1
    field_simp
  have hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J)) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))
  have hlogJ : Real.log (↑q * ↑d) ≤ X ^ (eps / (4 * J)) := by
    rw [hpow] at hlog
    exact hlog.trans hmono
  have hN0 : 0 < ψ.N := (AbF.ofChar ψ).pos
  have hcop : ∀ r : ℕ, Nat.Prime r → (ψ.N : ℝ) < r → Nat.Coprime r ψ.N := by
    intro r hr hlt
    have hlt' : ψ.N < r := by exact_mod_cast hlt
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 (fun hdvd => absurd (Nat.le_of_dvd hN0 hdvd) (not_le.2 hlt'))
  have hpp : PrimePair ψ.N q d :=
    ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod,
      Nat.Coprime.mul (hcop q hw.q_prime (lt_of_le_of_lt hNP' hPq)) (hcop d hw.d_prime (lt_of_le_of_lt hNP' hPd))⟩
  obtain ⟨Y, ⟨hYlo, hYhi⟩, hY⟩ :=
    hmain X hXJ q d hpp hq3 hd3 (lt_of_le_of_lt hPP' hPq) (lt_of_le_of_lt hPP' hPd) hlogJ
  have hWY : X ^ (1 / J') ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo
  refine ⟨Y, hWY, hYhi, ?_⟩
  intro x hxY hxY2
  have hWx : X ^ (1 / J') ≤ x := hWY.trans hxY
  have hLx : L ≤ x := hLX.trans hWx
  have hx2 : 2 ≤ x := h2L.trans hLx
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hBa, hHV⟩ := hY x hxY hxY2
  intro E _ _ hE
  have hq0 : 0 < q := hw.q_prime.pos
  have hd0 : 0 < d := hw.d_prime.pos
  have hq4 : q % 4 = 3 := by
    have := hw.q_mod
    omega
  haveI : IsCMField E := isCMField_of_isChiField ψ (e x) q d hw.q_prime hq4 E hE
  have hE' : IsCompField (AbF.ofChar ψ) (e x) q d E := (isCompField_ofChar ψ (e x) q d E).2 hE
  have h2 := hBa E hE'
  have hp := hHV E hE
  have hm := hCb (AbF.ofChar ψ) 4 e t hadm x hx2 q d hpp E hE'
  obtain ⟨hc1, hc2, hc3⟩ := conductor_bounds_of_isChiField ψ (e x) q d hq0 hd0 E hE
  obtain ⟨-, -, ht2, htle⟩ := hadm x hx2
  have ht1 : 1 ≤ t x := by omega
  have hWpos : (0 : ℝ) ≤ X ^ (1 / J') := Real.rpow_nonneg hX0 _
  have hqd : Real.log (↑q * ↑d) ≤ x ^ (eps / 4) := by
    have hlog0 := hY0 _ (hY0L.trans hLX) q d hw
    exact hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))
  have hNt := hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hmb := hK (Module.finrank ℚ E) (condF E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt
  have hm' := VVminusLe.mono hm hmb
  have hv := vvle_of_parts h2 hm' hp
  have hu1 : (1 : ℝ) ≤ ↑(condF E) * ↑(t x) := by
    have a : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have htot := hxT x (hxTL.trans hLx) _ hu1 hNt
  exact VVle.mono hv le_rfl htot

/- English proof (translation)
Introduce `ψ`. Conclude with `vwinAt_of_joint (by norm_num) hJ hc ψ`.
-/
theorem vwin_of_joint (hJ : JointWin 401) (hc : ThmBc 401) : VWin := by
  intro ψ
  exact vwinAt_of_joint (by norm_num) hJ hc ψ

end UpperTheory.V

end
