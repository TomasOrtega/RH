import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonValue
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open _root_.WittVector Laurent Polynomial WittTilt

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Use `set r₀ : ℝ := (p : ℝ)⁻¹ with hr₀`. Establish `hr0 : 0 < r₀` using `inv_p_pos`. Establish `hr1 : r₀ < 1` using `inv_p_lt_one`. Establish `hnp : ‖(p : ℂ_[p])‖ = r₀` using `norm_p_Cp`. Establish `ha : a ≠ 0`.

Introduce and unpack `rfl`. Rewrite `h` using `[map_zero]`. Establish `h1 : algClToBdR p y ≠ 0` using `fun h0 => hy (injective_algClToBdR p (by rw [h0, map_zero]))`. Establish `h2 : iota ℂ_[p] p b ≠ 0` using `fun h0 => hb (iota_injective (by rw [h0, map_zero]))`. Conclude with `mul_ne_zero h1 h2 h.symm`.

Use `set q := minpoly ℚ_[p] y with hq`. Use `set d := q.natDegree with hd_def`. Establish `hd : 1 ≤ d` using `natDegree_minpoly_pos y`. Establish `hqd : q.coeff d = 1` using `(minpoly.monic (Algebra.IsIntegral.isIntegral y)).coeff_natDegree`. Use `set Cq : ℝ := max 1 ‖y‖ ^ d with hCq`.

Establish `hCq1 : 1 ≤ Cq` using `one_le_pow₀ (le_max_left _ _)`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le hCq1)) hr1`. Establish `hqle : ∀ i, ‖q.coeff i‖ ≤ Cq`. Introduce `i`. Distinguish the cases in `hi : i ≤ d`.

Conclude with `(norm_minpoly_coeff_le y hi).trans ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le d i)))`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (not_le.1 hi), norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnormc : ∀ i, ‖(p : ℚ_[p]) ^ k * q.coeff i‖ = r₀ ^ k * ‖q.coeff i‖`. Introduce `i`.

Rewrite using `[norm_mul, norm_pow, Padic.norm_p]`. Establish `hcoeff : ∀ i, ‖(p : ℚ_[p]) ^ k * q.coeff i‖ ≤ 1`. Introduce `i`. Rewrite using `[hnormc]`. Combine the equalities or inequalities in the displayed calculation.

Use `set c : ℕ → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ k * q.coeff i, hcoeff i⟩ with hc`. Establish `hnc : ∀ i, ‖c i‖ = r₀ ^ k * ‖q.coeff i‖` using `fun i => hnormc i`. Use `set x : ℕ → AInf ℂ_[p] p := fun i => IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p (c i) with hx`. Establish `hrel : ∑ i ∈ Finset.range (d + 1), algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (x i) * a ^ i * b ^ (d - i) = 0`. Apply `iota_injective (K := ℂ_[p]) (p := p)` to reduce the goal to its premises.

Rewrite using `[map_zero, map_sum]`. Establish `e : ∀ i ∈ Finset.range (d + 1), iota ℂ_[p] p (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (x i) * a ^ i * b ^ (d - i)) = algebraMap ℚ_[p] 𝔹 ((p : ℚ_[p]) ^ k) * iota ℂ_[p] p b ^ d * (algebraMap ℚ_[p] 𝔹 (q.coeff i) * algClToBdR p y ^ i)`. Introduce `i hi`. Establish `hid : i ≤ d` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Rewrite using `[map_mul, map_mul, map_pow, map_pow, iota_padicInt, h, mul_pow]`.

Establish `hci : ((c i : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * q.coeff i` using `rfl`. Rewrite using `[hci, map_mul]`. Establish `hb' : iota ℂ_[p] p b ^ i * iota ℂ_[p] p b ^ (d - i) = iota ℂ_[p] p b ^ d`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hid]`. Take the linear combination `(algebraMap ℚ_[p] 𝔹 ((p : ℚ_[p]) ^ k) * algebraMap ℚ_[p] 𝔹 (q.coeff i) * algClToBdR p y ^ i) * hb'`.

Rewrite using `[Finset.sum_congr rfl e, ← Finset.mul_sum]`. Establish `haeval : ∑ i ∈ Finset.range (d + 1), algebraMap ℚ_[p] 𝔹 (q.coeff i) * algClToBdR p y ^ i = 0`. Use `Polynomial.aeval_eq_sum_range (p := q) (algClToBdR p y)` as an intermediate fact. Rewrite `this` using `[Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Simplify using `only [Algebra.smul_def] at this`.

Conclude with `this.symm`. Rewrite using `[haeval, mul_zero]`. Take `⟨ρa, Na, ca0, hρa, hρa1, -, hgooda, hsta⟩` from `exists_stable (K := ℂ_[p]) ha`. Take `⟨ρb, Nb, cb0, hρb, hρb1, -, hgoodb, hstb⟩` from `exists_stable (K := ℂ_[p]) hb`. Rewrite `hρa`, `hρb`, `hgooda`, `hgoodb`, `hsta`, `hstb` using `[hnp]`.

Establish `hca0 : (ca0 : 𝔸) ≠ 0`. Introduce `h0`. Use `hgooda r₀ ⟨le_rfl, hρa.le⟩` as an intermediate fact. Rewrite `this` using `[h0, gn_zero]`. Combine the linear relations using `[pow_pos hr0 Na]`.

Establish `hcb0 : (cb0 : 𝔸) ≠ 0`. Introduce `h0`. Use `hgoodb r₀ ⟨le_rfl, hρb.le⟩` as an intermediate fact. Rewrite `this` using `[h0, gn_zero]`. Combine the linear relations using `[pow_pos hr0 Nb]`.

Take `⟨βa, ia, ρ3a, hβa, hρ3a, hρ3a1, hmona⟩` from `exists_gn_eq_monomial hca0 hr0 hr1`. Take `⟨βb, ib, ρ3b, hβb, hρ3b, hρ3b1, hmonb⟩` from `exists_gn_eq_monomial hcb0 hr0 hr1`. Use `set ρ₅ := min (min ρa ρb) (min ρ3a ρ3b) with hρ₅`. Establish `hr₅ : r₀ < ρ₅` using `lt_min (lt_min hρa hρb) (lt_min hρ3a hρ3b)`. Establish `hmem : ∀ ρ ∈ Set.Icc r₀ ρ₅, ρ ∈ Set.Icc r₀ ρa ∧ ρ ∈ Set.Icc r₀ ρb ∧ ρ ∈ Set.Icc r₀ ρ3a ∧ ρ ∈ Set.Icc r₀ ρ3b`.

Introduce `ρ hρ`. Use `⟨⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩⟩` and prove the remaining obligations. Conclude with `hρ.2.trans ((min_le_left _ _).trans (min_le_left _ _))`. Conclude with `hρ.2.trans ((min_le_left _ _).trans (min_le_right _ _))`. Conclude with `hρ.2.trans ((min_le_right _ _).trans (min_le_left _ _))`.

Conclude with `hρ.2.trans ((min_le_right _ _).trans (min_le_right _ _))`. Establish `hid : ∀ ρ ∈ Set.Icc r₀ ρ₅, gn ℂ_[p] p ρ (ca0 : 𝔸) = ‖y‖ ^ sig p ρ * gn ℂ_[p] p ρ (cb0 : 𝔸)`. Introduce `ρ hρ`. Take `⟨hρA, hρB, -, -⟩` from `hmem ρ hρ`. Establish `hρ0 : 0 < ρ` using `hr0.trans_le hρ.1`.

Establish `hρ1 : ρ < 1` using `hρA.2.trans_lt hρa1`. Establish `hpρ : ‖(p : ℂ_[p])‖ ≤ ρ` using `hnp ▸ hρ.1`. Establish `hσ` using `sig_pos (p := p) hρ0 hρ1`. Use `set Fa := gn ℂ_[p] p ρ (ca0 : 𝔸)`. Use `set Fb := gn ℂ_[p] p ρ (cb0 : 𝔸)`.

Establish `hFa : 0 < Fa` using `(pow_pos hρ0 Na).trans (hgooda ρ hρA)`. Establish `hFb : 0 < Fb` using `(pow_pos hρ0 Nb).trans (hgoodb ρ hρB)`. Use `set μ := ‖y‖ ^ sig p ρ`. Establish `hμ : 0 < μ` using `Real.rpow_pos_of_pos (norm_pos_iff.2 hy) _`. Use `set G : ℕ → ℝ := fun i => gn ℂ_[p] p ρ (algebraMap (AInf ℂ_[p] p) 𝔸 (x i)) with hG_def`.

Establish `hGc : ∀ i, G i = ‖c i‖ ^ sig p ρ` using `fun i => gn_padicInt hρ0 hρ1 (c i)`. Establish `hsig : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, (r₀ ^ n * t) ^ sig p ρ = ρ ^ n * t ^ sig p ρ`. Introduce `t ht n`. Rewrite using `[Real.mul_rpow (pow_nonneg hr0.le n) ht, pow_rpow_comm hr0.le, rpow_sig hρ0]`. Establish `hG : ∀ i ≤ d, 0 ≤ G i ∧ G i ≤ ρ ^ k * μ ^ (d - i)`.

Introduce `i hi`. Use `⟨hGc i ▸ Real.rpow_nonneg (norm_nonneg _) _, ?_⟩` and prove the remaining obligations. Rewrite using `[hGc, hnc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hG0 : G 0 = ρ ^ k * μ ^ d`.

Rewrite using `[hGc, hnc, norm_minpoly_coeff_zero, hsig _ (by positivity), pow_rpow_comm (norm_nonneg _)]`. Establish `hGd : G d = ρ ^ k`. Rewrite using `[hGc, hnc, hqd, norm_one, mul_one, ← mul_one (r₀ ^ k), hsig _ zero_le_one, Real.one_rpow, mul_one]`. Establish `hsa : ∀ N ≥ Na, ∀ c' : ACrisZero ℂ_[p] p, a - algebraMap _ (ACris ℂ_[p] p) c' ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} → gn ℂ_[p] p ρ (c' : 𝔸) = Fa` using `fun N hN c' hc' => hsta N hN c' hc' ρ hρA`. Establish `hsb : ∀ N ≥ Nb, ∀ c' : ACrisZero ℂ_[p] p, b - algebraMap _ (ACris ℂ_[p] p) c' ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} → gn ℂ_[p] p ρ (c' : 𝔸) = Fb` using `fun N hN c' hc' => hstb N hN c' hc' ρ hρB`.

Conclude with `eq_of_no_dominant hd hFa hFb hμ (pow_pos hρ0 k) G hG hG0 hGd fun j hj hpos hdom => false_of_dominant hpρ hρ1 hsa hsb d x hrel hj hpos hdom`. Establish `e1` using `hid r₀ ⟨le_rfl, hr₅.le⟩`. Establish `e2` using `hid ρ₅ ⟨hr₅.le, le_rfl⟩`. Take `⟨-, -, hA1, hB1⟩` from `hmem r₀ ⟨le_rfl, hr₅.le⟩`. Take `⟨-, -, hA2, hB2⟩` from `hmem ρ₅ ⟨hr₅.le, le_rfl⟩`.

Rewrite `e1` using `[hmona r₀ hA1, hmonb r₀ hB1, sig_inv_p, Real.rpow_one]`. Rewrite `e2` using `[hmona ρ₅ hA2, hmonb ρ₅ hB2]`. Establish `hρ₅0 : 0 < ρ₅` using `hr0.trans hr₅`. Use `set D : ℤ := ia - ib`. Use `set γ : ℝ := βa / βb with hγ`.

Establish `hγ0 : 0 < γ` using `div_pos hβa hβb`. Establish `hy1 : ‖y‖ = γ * r₀ ^ D`. Establish `hne : βb * r₀ ^ ib ≠ 0` using `(mul_pos hβb (zpow_pos hr0 ib)).ne'`. Establish `h0 : ‖y‖ = (βa * r₀ ^ ia) / (βb * r₀ ^ ib)` using `by rw [e1, mul_div_cancel_right₀ _ hne]`. Rewrite using `[h0, mul_div_mul_comm, ← zpow_sub₀ hr0.ne']`.

Establish `hzr : ∀ (t : ℝ), 0 < t → (r₀ ^ D) ^ sig p t = t ^ D`. Introduce `t ht`. Rewrite using `[← Real.rpow_intCast, ← Real.rpow_mul hr0.le, mul_comm, Real.rpow_mul hr0.le, rpow_sig ht, Real.rpow_intCast]`. Establish `hγσ : γ ^ sig p ρ₅ = γ`. Establish `h2 : ‖y‖ ^ sig p ρ₅ = γ ^ sig p ρ₅ * ρ₅ ^ D`.

Rewrite using `[hy1, Real.mul_rpow hγ0.le (zpow_nonneg hr0.le D), hzr ρ₅ hρ₅0]`. Establish `h3 : βa * ρ₅ ^ ia = γ ^ sig p ρ₅ * ρ₅ ^ D * (βb * ρ₅ ^ ib)` using `by rw [e2, h2]`. Establish `h4 : ρ₅ ^ ia = ρ₅ ^ D * ρ₅ ^ ib`. Rewrite using `[← zpow_add₀ hρ₅0.ne']`. Use `show ρ₅ ^ ia = ρ₅ ^ (ia - ib + ib)`.

Rewrite using `[sub_add_cancel]`. Rewrite `h3` using `[h4]`. Establish `h5 : (γ ^ sig p ρ₅ - γ) * (βb * ρ₅ ^ D * ρ₅ ^ ib) = 0`. Establish `hβ : βa = γ * βb` using `by rw [hγ, div_mul_cancel₀ _ hβb.ne']`. Rewrite `h3` using `[hβ]`.

Take the linear combination `-h3`. Establish `h6 : βb * ρ₅ ^ D * ρ₅ ^ ib ≠ 0` using `by positivity`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_right h6)`. Establish `hσ1 : sig p ρ₅ ≠ 1`. Introduce `h1`.

Establish `: Real.log ρ₅ = Real.log r₀`. Unfold `sig at h1`. Rewrite `h1` using `[div_eq_one_iff_eq log_inv_p_neg.ne]`. Conclude with `h1`. Conclude with `hr₅.ne' (Real.log_injOn_pos (Set.mem_Ioi.2 hρ₅0) (Set.mem_Ioi.2 hr0) this)`.

Establish `hγ1 : γ = 1`. Establish `h7` using `congrArg Real.log hγσ`. Rewrite `h7` using `[Real.log_rpow hγ0]`. Establish `h8 : (sig p ρ₅ - 1) * Real.log γ = 0` using `by linear_combination h7`. Establish `h9` using `(mul_eq_zero.1 h8).resolve_left (sub_ne_zero.2 hσ1)`.

Conclude with `Real.eq_one_of_pos_of_log_eq_zero hγ0 h9`. Use `⟨D, ?_⟩` and prove the remaining obligations. Rewrite using `[hy1, hγ1, one_mul, norm_p_algCl]`.
-/
theorem exists_norm_eq_zpow_of_iota_eq {y : PadicAlgCl p} (hy : y ≠ 0) {a b : ACris ℂ_[p] p}
    (hb : b ≠ 0) (h : iota ℂ_[p] p a = algClToBdR p y * iota ℂ_[p] p b) :
    ∃ D : ℤ, ‖y‖ = ‖(p : PadicAlgCl p)‖ ^ D := by
  set r₀ : ℝ := (p : ℝ)⁻¹ with hr₀
  have hr0 : 0 < r₀ := inv_p_pos
  have hr1 : r₀ < 1 := inv_p_lt_one
  have hnp : ‖(p : ℂ_[p])‖ = r₀ := norm_p_Cp
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    have h1 : algClToBdR p y ≠ 0 := fun h0 => hy (injective_algClToBdR p (by rw [h0, map_zero]))
    have h2 : iota ℂ_[p] p b ≠ 0 := fun h0 => hb (iota_injective (by rw [h0, map_zero]))
    exact mul_ne_zero h1 h2 h.symm

  set q := minpoly ℚ_[p] y with hq
  set d := q.natDegree with hd_def
  have hd : 1 ≤ d := natDegree_minpoly_pos y
  have hqd : q.coeff d = 1 := (minpoly.monic (Algebra.IsIntegral.isIntegral y)).coeff_natDegree
  set Cq : ℝ := max 1 ‖y‖ ^ d with hCq
  have hCq1 : 1 ≤ Cq := one_le_pow₀ (le_max_left _ _)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le hCq1)) hr1
  have hqle : ∀ i, ‖q.coeff i‖ ≤ Cq := by
    intro i
    by_cases hi : i ≤ d
    · exact (norm_minpoly_coeff_le y hi).trans ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le d i)))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), norm_zero]; linarith
  have hnormc : ∀ i, ‖(p : ℚ_[p]) ^ k * q.coeff i‖ = r₀ ^ k * ‖q.coeff i‖ := by
    intro i; rw [norm_mul, norm_pow, Padic.norm_p]
  have hcoeff : ∀ i, ‖(p : ℚ_[p]) ^ k * q.coeff i‖ ≤ 1 := by
    intro i
    rw [hnormc]
    calc r₀ ^ k * ‖q.coeff i‖ ≤ r₀ ^ k * Cq := mul_le_mul_of_nonneg_left (hqle i) (pow_nonneg hr0.le k)
      _ ≤ Cq⁻¹ * Cq := mul_le_mul_of_nonneg_right hk.le (zero_le_one.trans hCq1)
      _ = 1 := inv_mul_cancel₀ (zero_lt_one.trans_le hCq1).ne'
  set c : ℕ → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ k * q.coeff i, hcoeff i⟩ with hc
  have hnc : ∀ i, ‖c i‖ = r₀ ^ k * ‖q.coeff i‖ := fun i => hnormc i
  set x : ℕ → AInf ℂ_[p] p := fun i => IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p (c i) with hx

  have hrel : ∑ i ∈ Finset.range (d + 1),
      algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (x i) * a ^ i * b ^ (d - i) = 0 := by
    apply iota_injective (K := ℂ_[p]) (p := p)
    rw [map_zero, map_sum]
    have e : ∀ i ∈ Finset.range (d + 1), iota ℂ_[p] p
        (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (x i) * a ^ i * b ^ (d - i)) =
        algebraMap ℚ_[p] 𝔹 ((p : ℚ_[p]) ^ k) * iota ℂ_[p] p b ^ d *
          (algebraMap ℚ_[p] 𝔹 (q.coeff i) * algClToBdR p y ^ i) := by
      intro i hi
      have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [map_mul, map_mul, map_pow, map_pow, iota_padicInt, h, mul_pow]
      have hci : ((c i : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * q.coeff i := rfl
      rw [hci, map_mul]
      have hb' : iota ℂ_[p] p b ^ i * iota ℂ_[p] p b ^ (d - i) = iota ℂ_[p] p b ^ d := by
        rw [← pow_add, Nat.add_sub_cancel' hid]
      linear_combination (algebraMap ℚ_[p] 𝔹 ((p : ℚ_[p]) ^ k) * algebraMap ℚ_[p] 𝔹 (q.coeff i) *
        algClToBdR p y ^ i) * hb'
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have haeval : ∑ i ∈ Finset.range (d + 1), algebraMap ℚ_[p] 𝔹 (q.coeff i) * algClToBdR p y ^ i = 0 := by
      have := Polynomial.aeval_eq_sum_range (p := q) (algClToBdR p y)
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero] at this
      simp only [Algebra.smul_def] at this
      exact this.symm
    rw [haeval, mul_zero]

  obtain ⟨ρa, Na, ca0, hρa, hρa1, -, hgooda, hsta⟩ := exists_stable (K := ℂ_[p]) ha
  obtain ⟨ρb, Nb, cb0, hρb, hρb1, -, hgoodb, hstb⟩ := exists_stable (K := ℂ_[p]) hb
  rw [hnp] at hρa hρb hgooda hgoodb hsta hstb
  have hca0 : (ca0 : 𝔸) ≠ 0 := by
    intro h0
    have := hgooda r₀ ⟨le_rfl, hρa.le⟩
    rw [h0, gn_zero] at this
    linarith [pow_pos hr0 Na]
  have hcb0 : (cb0 : 𝔸) ≠ 0 := by
    intro h0
    have := hgoodb r₀ ⟨le_rfl, hρb.le⟩
    rw [h0, gn_zero] at this
    linarith [pow_pos hr0 Nb]
  obtain ⟨βa, ia, ρ3a, hβa, hρ3a, hρ3a1, hmona⟩ := exists_gn_eq_monomial hca0 hr0 hr1
  obtain ⟨βb, ib, ρ3b, hβb, hρ3b, hρ3b1, hmonb⟩ := exists_gn_eq_monomial hcb0 hr0 hr1
  set ρ₅ := min (min ρa ρb) (min ρ3a ρ3b) with hρ₅
  have hr₅ : r₀ < ρ₅ := lt_min (lt_min hρa hρb) (lt_min hρ3a hρ3b)
  have hmem : ∀ ρ ∈ Set.Icc r₀ ρ₅, ρ ∈ Set.Icc r₀ ρa ∧ ρ ∈ Set.Icc r₀ ρb ∧
      ρ ∈ Set.Icc r₀ ρ3a ∧ ρ ∈ Set.Icc r₀ ρ3b := by
    intro ρ hρ
    refine ⟨⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩⟩
    · exact hρ.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    · exact hρ.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    · exact hρ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hρ.2.trans ((min_le_right _ _).trans (min_le_right _ _))

  have hid : ∀ ρ ∈ Set.Icc r₀ ρ₅,
      gn ℂ_[p] p ρ (ca0 : 𝔸) = ‖y‖ ^ sig p ρ * gn ℂ_[p] p ρ (cb0 : 𝔸) := by
    intro ρ hρ
    obtain ⟨hρA, hρB, -, -⟩ := hmem ρ hρ
    have hρ0 : 0 < ρ := hr0.trans_le hρ.1
    have hρ1 : ρ < 1 := hρA.2.trans_lt hρa1
    have hpρ : ‖(p : ℂ_[p])‖ ≤ ρ := hnp ▸ hρ.1
    have hσ := sig_pos (p := p) hρ0 hρ1
    set Fa := gn ℂ_[p] p ρ (ca0 : 𝔸)
    set Fb := gn ℂ_[p] p ρ (cb0 : 𝔸)
    have hFa : 0 < Fa := (pow_pos hρ0 Na).trans (hgooda ρ hρA)
    have hFb : 0 < Fb := (pow_pos hρ0 Nb).trans (hgoodb ρ hρB)
    set μ := ‖y‖ ^ sig p ρ
    have hμ : 0 < μ := Real.rpow_pos_of_pos (norm_pos_iff.2 hy) _
    set G : ℕ → ℝ := fun i => gn ℂ_[p] p ρ (algebraMap (AInf ℂ_[p] p) 𝔸 (x i)) with hG_def
    have hGc : ∀ i, G i = ‖c i‖ ^ sig p ρ := fun i => gn_padicInt hρ0 hρ1 (c i)
    have hsig : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, (r₀ ^ n * t) ^ sig p ρ = ρ ^ n * t ^ sig p ρ := by
      intro t ht n
      rw [Real.mul_rpow (pow_nonneg hr0.le n) ht, pow_rpow_comm hr0.le, rpow_sig hρ0]
    have hG : ∀ i ≤ d, 0 ≤ G i ∧ G i ≤ ρ ^ k * μ ^ (d - i) := by
      intro i hi
      refine ⟨hGc i ▸ Real.rpow_nonneg (norm_nonneg _) _, ?_⟩
      rw [hGc, hnc]
      calc (r₀ ^ k * ‖q.coeff i‖) ^ sig p ρ ≤ (r₀ ^ k * ‖y‖ ^ (d - i)) ^ sig p ρ :=
            Real.rpow_le_rpow (by positivity)
              (mul_le_mul_of_nonneg_left (norm_minpoly_coeff_le y hi) (pow_nonneg hr0.le k)) hσ.le
        _ = ρ ^ k * μ ^ (d - i) := by rw [hsig _ (by positivity), pow_rpow_comm (norm_nonneg _)]
    have hG0 : G 0 = ρ ^ k * μ ^ d := by
      rw [hGc, hnc, norm_minpoly_coeff_zero, hsig _ (by positivity), pow_rpow_comm (norm_nonneg _)]
    have hGd : G d = ρ ^ k := by
      rw [hGc, hnc, hqd, norm_one, mul_one, ← mul_one (r₀ ^ k), hsig _ zero_le_one, Real.one_rpow,
        mul_one]
    have hsa : ∀ N ≥ Na, ∀ c' : ACrisZero ℂ_[p] p,
        a - algebraMap _ (ACris ℂ_[p] p) c' ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} →
          gn ℂ_[p] p ρ (c' : 𝔸) = Fa := fun N hN c' hc' => hsta N hN c' hc' ρ hρA
    have hsb : ∀ N ≥ Nb, ∀ c' : ACrisZero ℂ_[p] p,
        b - algebraMap _ (ACris ℂ_[p] p) c' ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} →
          gn ℂ_[p] p ρ (c' : 𝔸) = Fb := fun N hN c' hc' => hstb N hN c' hc' ρ hρB
    exact eq_of_no_dominant hd hFa hFb hμ (pow_pos hρ0 k) G hG hG0 hGd
      fun j hj hpos hdom => false_of_dominant hpρ hρ1 hsa hsb d x hrel hj hpos hdom

  have e1 := hid r₀ ⟨le_rfl, hr₅.le⟩
  have e2 := hid ρ₅ ⟨hr₅.le, le_rfl⟩
  obtain ⟨-, -, hA1, hB1⟩ := hmem r₀ ⟨le_rfl, hr₅.le⟩
  obtain ⟨-, -, hA2, hB2⟩ := hmem ρ₅ ⟨hr₅.le, le_rfl⟩
  rw [hmona r₀ hA1, hmonb r₀ hB1, sig_inv_p, Real.rpow_one] at e1
  rw [hmona ρ₅ hA2, hmonb ρ₅ hB2] at e2
  have hρ₅0 : 0 < ρ₅ := hr0.trans hr₅
  set D : ℤ := ia - ib
  set γ : ℝ := βa / βb with hγ
  have hγ0 : 0 < γ := div_pos hβa hβb
  have hy1 : ‖y‖ = γ * r₀ ^ D := by
    have hne : βb * r₀ ^ ib ≠ 0 := (mul_pos hβb (zpow_pos hr0 ib)).ne'
    have h0 : ‖y‖ = (βa * r₀ ^ ia) / (βb * r₀ ^ ib) := by rw [e1, mul_div_cancel_right₀ _ hne]
    rw [h0, mul_div_mul_comm, ← zpow_sub₀ hr0.ne']
  have hzr : ∀ (t : ℝ), 0 < t → (r₀ ^ D) ^ sig p t = t ^ D := by
    intro t ht
    rw [← Real.rpow_intCast, ← Real.rpow_mul hr0.le, mul_comm, Real.rpow_mul hr0.le, rpow_sig ht,
      Real.rpow_intCast]
  have hγσ : γ ^ sig p ρ₅ = γ := by
    have h2 : ‖y‖ ^ sig p ρ₅ = γ ^ sig p ρ₅ * ρ₅ ^ D := by
      rw [hy1, Real.mul_rpow hγ0.le (zpow_nonneg hr0.le D), hzr ρ₅ hρ₅0]
    have h3 : βa * ρ₅ ^ ia = γ ^ sig p ρ₅ * ρ₅ ^ D * (βb * ρ₅ ^ ib) := by rw [e2, h2]
    have h4 : ρ₅ ^ ia = ρ₅ ^ D * ρ₅ ^ ib := by
      rw [← zpow_add₀ hρ₅0.ne']
      show ρ₅ ^ ia = ρ₅ ^ (ia - ib + ib)
      rw [sub_add_cancel]
    rw [h4] at h3
    have h5 : (γ ^ sig p ρ₅ - γ) * (βb * ρ₅ ^ D * ρ₅ ^ ib) = 0 := by
      have hβ : βa = γ * βb := by rw [hγ, div_mul_cancel₀ _ hβb.ne']
      rw [hβ] at h3
      linear_combination -h3
    have h6 : βb * ρ₅ ^ D * ρ₅ ^ ib ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_right h6)
  have hσ1 : sig p ρ₅ ≠ 1 := by
    intro h1
    have : Real.log ρ₅ = Real.log r₀ := by
      unfold sig at h1
      rw [div_eq_one_iff_eq log_inv_p_neg.ne] at h1
      exact h1
    exact hr₅.ne' (Real.log_injOn_pos (Set.mem_Ioi.2 hρ₅0) (Set.mem_Ioi.2 hr0) this)
  have hγ1 : γ = 1 := by
    have h7 := congrArg Real.log hγσ
    rw [Real.log_rpow hγ0] at h7
    have h8 : (sig p ρ₅ - 1) * Real.log γ = 0 := by linear_combination h7
    have h9 := (mul_eq_zero.1 h8).resolve_left (sub_ne_zero.2 hσ1)
    exact Real.eq_one_of_pos_of_log_eq_zero hγ0 h9
  refine ⟨D, ?_⟩
  rw [hy1, hγ1, one_mul, norm_p_algCl]

end ACris

end GroundTheory.PAdicHodge
