import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaFrob
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

/- English proof (translation)
Establish `h1 : T.coeff (T.teich (T.red y)⁻¹ * y) 0 = 1`. Rewrite using `[coeff_teich_mul, coeff_zero, inv_mul_cancel₀ hy]`. Establish `hu` using `T.isUnit_of_coeff_zero_eq_one h1`. Establish `ht : IsUnit (T.teich (T.red y))` using `isUnit_iff_exists_inv.2 ⟨T.teich (T.red y)⁻¹, by rw [← T.teich_mul, mul_inv_cancel₀ hy, T.teich_one]⟩`. Establish `e : y = T.teich (T.red y) * (T.teich (T.red y)⁻¹ * y)`.

Rewrite using `[← mul_assoc, ← T.teich_mul, mul_inv_cancel₀ hy, T.teich_one, one_mul]`. Rewrite using `[e]`. Conclude with `ht.mul hu`.
-/
theorem isUnit_of_red_ne_zero {y : Γ} (hy : T.red y ≠ 0) : IsUnit y := by
  have h1 : T.coeff (T.teich (T.red y)⁻¹ * y) 0 = 1 := by
    rw [coeff_teich_mul, coeff_zero, inv_mul_cancel₀ hy]
  have hu := T.isUnit_of_coeff_zero_eq_one h1
  have ht : IsUnit (T.teich (T.red y)) :=
    isUnit_iff_exists_inv.2 ⟨T.teich (T.red y)⁻¹, by rw [← T.teich_mul, mul_inv_cancel₀ hy, T.teich_one]⟩
  have e : y = T.teich (T.red y) * (T.teich (T.red y)⁻¹ * y) := by
    rw [← mul_assoc, ← T.teich_mul, mul_inv_cancel₀ hy, T.teich_one, one_mul]
  rw [e]; exact ht.mul hu

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Establish `h1` using `T.norm_red_le_one _ (u : T.int).2`. Establish `h2` using `T.norm_red_le_one _ ((u⁻¹ : T.intˣ) : T.int).2`. Establish `h3 : T.red ((u : T.int) : Γ) * T.red (((u⁻¹ : T.intˣ) : T.int) : Γ) = 1`.

Rewrite using `[← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]`. Establish `h4` using `congrArg norm h3`. Rewrite `h4` using `[norm_mul, norm_one]`. Use `le_antisymm h1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `: ‖T.red ((u : T.int) : Γ)‖ * ‖T.red (((u⁻¹ : T.intˣ) : T.int) : Γ)‖ < 1` using `(mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`. Take `⟨v, hv, huv⟩` from `T.exists_inv_mem_int x.2 h`.

Conclude with `isUnit_iff_exists_inv.2 ⟨⟨v, hv⟩, Subtype.ext huv⟩`.
-/
theorem isUnit_int_iff {x : T.int} : IsUnit x ↔ ‖T.red x‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := T.norm_red_le_one _ (u : T.int).2
    have h2 := T.norm_red_le_one _ ((u⁻¹ : T.intˣ) : T.int).2
    have h3 : T.red ((u : T.int) : Γ) * T.red (((u⁻¹ : T.intˣ) : T.int) : Γ) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have : ‖T.red ((u : T.int) : Γ)‖ * ‖T.red (((u⁻¹ : T.intˣ) : T.int) : Γ)‖ < 1 :=
      (mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt hlt
    linarith
  · intro h
    obtain ⟨v, hv, huv⟩ := T.exists_inv_mem_int x.2 h
    exact isUnit_iff_exists_inv.2 ⟨⟨v, hv⟩, Subtype.ext huv⟩

/- English proof (translation)
Rewrite `hx`, the goal using `[T.mem_int_iff]`. Introduce `n`. Use `hx (n + k)` as an intermediate fact. Rewrite `this` using `[h, coeff_π_pow_mul_add]`. Then use the resulting hypothesis.
-/
theorem exists_int_of_eq_π_pow_mul {x z : Γ} (hx : x ∈ T.int) {k : ℕ} (h : x = T.π ^ k * z) :
    z ∈ T.int := by
  rw [T.mem_int_iff] at hx ⊢
  intro n
  have := hx (n + k)
  rwa [h, coeff_π_pow_mul_add] at this

def teichInt {z : L} (hz : ‖z‖ ≤ 1) : T.int := ⟨T.teich z, T.teich_mem_int hz⟩

def πInt : T.int := ⟨T.π, T.π_mem_int⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_teichInt {z : L} (hz : ‖z‖ ≤ 1) : (T.teichInt hz : Γ) = T.teich z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_πInt : (T.πInt : Γ) = T.π := rfl

structure IsPrimOne (ξ : T.int) : Prop where
  coeff_zero_ne : T.coeff ξ 0 ≠ 0
  norm_coeff_zero_lt : ‖T.coeff ξ 0‖ < 1
  norm_coeff_one : ‖T.coeff ξ 1‖ = 1

abbrev Untilt (ξ : T.int) := T.int ⧸ Ideal.span {ξ}

abbrev toUntilt (ξ : T.int) : T.int →+* T.Untilt ξ := Ideal.Quotient.mk _

variable {ξ : T.int}

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨B, hB⟩`. Use `⟨B, B.2, ?_⟩` and prove the remaining obligations. Use `congrArg (Subtype.val : T.int → Γ) hB` as an intermediate fact.

Simplify using `only [Subring.coe_mul, AddSubgroupClass.coe_sub] at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨B, hB, h⟩`. Use `⟨⟨B, hB⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Simplify using `only [Subring.coe_mul, AddSubgroupClass.coe_sub]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toUntilt_eq_iff {x y : T.int} :
    T.toUntilt ξ x = T.toUntilt ξ y ↔ ∃ B ∈ T.int, (x : Γ) - y = ξ * B := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, B.2, ?_⟩
    have := congrArg (Subtype.val : T.int → Γ) hB
    simp only [Subring.coe_mul, AddSubgroupClass.coe_sub] at this
    rw [← this]; ring
  · rintro ⟨B, hB, h⟩
    refine ⟨⟨B, hB⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, AddSubgroupClass.coe_sub]
    rw [h]; ring

/- English proof (translation)
Rewrite using `[← map_zero (T.toUntilt ξ), toUntilt_eq_iff]`. Simplify using the standard rewrite rules.
-/
theorem toUntilt_eq_zero_iff {x : T.int} :
    T.toUntilt ξ x = 0 ↔ ∃ B ∈ T.int, (x : Γ) = ξ * B := by
  rw [← map_zero (T.toUntilt ξ), toUntilt_eq_iff]
  simp

def ξtail (ξ : T.int) : T.int := ⟨T.tail ξ, T.tail_mem_int ξ.2⟩

/- English proof (translation)
Rewrite using `[coeff_zero]`. Conclude with `T.eq_teich_add_π_mul_tail ξ`.
-/
theorem coe_eq_teich_add (ξ : T.int) :
    (ξ : Γ) = T.teich (T.coeff ξ 0) + T.π * (T.ξtail ξ : Γ) := by
  rw [coeff_zero]; exact T.eq_teich_add_π_mul_tail ξ

/- English proof (translation)
The claim follows from `(T.mem_int_iff.1 ξ.2) 0`.
-/
theorem norm_coeff_zero_le (ξ : T.int) : ‖T.coeff ξ 0‖ ≤ 1 := (T.mem_int_iff.1 ξ.2) 0

variable (hξ : T.IsPrimOne ξ)

include hξ in
/- English proof (translation)
Rewrite using `[isUnit_int_iff]`. Use `hξ.norm_coeff_one` as an intermediate fact. Rewrite `this` using `[coeff_succ, coeff_zero]`. Then use the resulting hypothesis.
-/
theorem isUnit_ξtail : IsUnit (T.ξtail ξ) := by
  rw [isUnit_int_iff]
  have := hξ.norm_coeff_one
  rwa [coeff_succ, coeff_zero] at this

include hξ in

/- English proof (translation)
Rewrite using `[← map_mul, ← map_neg, toUntilt_eq_iff]`. Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Establish `e` using `T.coe_eq_teich_add ξ`. Use `push_cast`. Simplify using `only [coe_teichInt, coe_πInt, mul_one]`.

Take the linear combination `-e`.
-/
theorem toUntilt_teich_coeff_zero :
    T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) =
      -(T.toUntilt ξ T.πInt * T.toUntilt ξ (T.ξtail ξ)) := by
  rw [← map_mul, ← map_neg, toUntilt_eq_iff]
  refine ⟨1, one_mem _, ?_⟩
  have e := T.coe_eq_teich_add ξ
  push_cast
  simp only [coe_teichInt, coe_πInt, mul_one]
  linear_combination -e

include hξ in

/- English proof (translation)
Use `T.isUnit_of_red_ne_zero ?_` and prove the remaining obligations. Rewrite using `[← coeff_zero]`. Conclude with `hξ.coeff_zero_ne`.
-/
theorem isUnit_coe_ξ : IsUnit (ξ : Γ) := by
  refine T.isUnit_of_red_ne_zero ?_
  rw [← coeff_zero]; exact hξ.coeff_zero_ne

include hξ in

/- English proof (translation)
Use `haveI := T.isAdicComplete`. Use `choose A hA B hB hAB using h`. Take `⟨Pinv, hPinv⟩` from `(T.isUnit_coe_ξ hξ).exists_right_inv`. Establish `hstep : ∀ k, B k - B (k + 1) ∈ Ideal.span {T.π ^ k}`. Introduce `k`.

Use `T.mem_span_pow.2 ⟨Pinv * (T.π * A (k + 1) - A k), ?_⟩` and prove the remaining obligations. Establish `e : (ξ : Γ) * (B k - B (k + 1)) = T.π ^ k * (T.π * A (k + 1) - A k)`. Establish `h1` using `hAB k`. Establish `h2` using `hAB (k + 1)`. Rewrite `h2` using `[pow_succ]`.

Take the linear combination `h2 - h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, mul_comm Pinv, hPinv, one_mul]`. Use `_ = _ := by rw [e]; ring`. Establish `hcauchy : ∀ {m n : ℕ}, m ≤ n → B m - B n ∈ Ideal.span {T.π ^ m}`.

Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `add_mem ih (T.span_pow_anti hmn (hstep n))` as an intermediate fact.

Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Take `⟨Binf, hBinf⟩` from `IsPrecomplete.prec' (I := T.I) B fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]`. Conclude with `hcauchy hmn`. Establish `hBinf' : ∀ k, B k - Binf ∈ Ideal.span {T.π ^ k}` using `fun k => by`.

Use `hBinf k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]`. Then use the resulting hypothesis. Establish `hmem : Binf ∈ T.int` using `T.mem_int_of_approx _ fun N => ⟨B N, hB N, by`. Use `neg_mem (hBinf' N)` as an intermediate fact. Rewrite using `[neg_sub] at this⟩` and apply the resulting hypothesis.

Use `⟨Binf, hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus' (I := T.I) _ fun k => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]`. Establish `: Y - (ξ : Γ) * Binf = T.π ^ k * A k + (ξ : Γ) * (B k - Binf)`.

Rewrite using `[hAB k]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (T.π_pow_mul_mem le_rfl _) (Ideal.mul_mem_left _ _ (hBinf' k))`.
-/
theorem eq_mul_of_forall_approx {Y : Γ} (hY : Y ∈ T.int)
    (h : ∀ k : ℕ, ∃ A ∈ T.int, ∃ B ∈ T.int, Y = T.π ^ k * A + (ξ : Γ) * B) :
    ∃ B ∈ T.int, Y = (ξ : Γ) * B := by
  haveI := T.isAdicComplete
  choose A hA B hB hAB using h
  obtain ⟨Pinv, hPinv⟩ := (T.isUnit_coe_ξ hξ).exists_right_inv
  have hstep : ∀ k, B k - B (k + 1) ∈ Ideal.span {T.π ^ k} := by
    intro k
    refine T.mem_span_pow.2 ⟨Pinv * (T.π * A (k + 1) - A k), ?_⟩
    have e : (ξ : Γ) * (B k - B (k + 1)) = T.π ^ k * (T.π * A (k + 1) - A k) := by
      have h1 := hAB k
      have h2 := hAB (k + 1)
      rw [pow_succ] at h2
      linear_combination h2 - h1
    calc B k - B (k + 1) = Pinv * ((ξ : Γ) * (B k - B (k + 1))) := by
          rw [← mul_assoc, mul_comm Pinv, hPinv, one_mul]
      _ = _ := by rw [e]; ring
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → B m - B n ∈ Ideal.span {T.π ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (T.span_pow_anti hmn (hstep n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨Binf, hBinf⟩ := IsPrecomplete.prec' (I := T.I) B fun {m n} hmn => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]; exact hcauchy hmn
  have hBinf' : ∀ k, B k - Binf ∈ Ideal.span {T.π ^ k} := fun k => by
    have := hBinf k
    rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow] at this
  have hmem : Binf ∈ T.int := T.mem_int_of_approx _ fun N => ⟨B N, hB N, by
    have := neg_mem (hBinf' N); rwa [neg_sub] at this⟩
  refine ⟨Binf, hmem, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := T.I) _ fun k => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]
  have : Y - (ξ : Γ) * Binf = T.π ^ k * A k + (ξ : Γ) * (B k - Binf) := by
    rw [hAB k]; ring
  rw [this]
  exact add_mem (T.π_pow_mul_mem le_rfl _) (Ideal.mul_mem_left _ _ (hBinf' k))

/- English proof (translation)
Use `T.zcoeff_π_pow 1` as an intermediate fact. Rewrite `this` using `[pow_one]`. Rewrite using `[this, gaussNorm_pi_single _ _ hρ, norm_one, one_mul, Nat.cast_one, zpow_one]`.
-/
theorem gaussNorm_π {ρ : ℝ} (hρ : 0 < ρ) : gaussNorm (T.zcoeff T.π) ρ = ρ := by
  have := T.zcoeff_π_pow 1
  rw [pow_one] at this
  rw [this, gaussNorm_pi_single _ _ hρ, norm_one, one_mul, Nat.cast_one, zpow_one]

/- English proof (translation)
Rewrite using `[zcoeff_teich, gaussNorm_pi_single _ _ hρ, zpow_zero, mul_one]`.
-/
theorem gaussNorm_teich (z : L) {ρ : ℝ} (hρ : 0 < ρ) : gaussNorm (T.zcoeff (T.teich z)) ρ = ‖z‖ := by
  rw [zcoeff_teich, gaussNorm_pi_single _ _ hρ, zpow_zero, mul_one]

/- English proof (translation)
Use `T.zcoeff_π_pow 1` as an intermediate fact. Rewrite `this` using `[pow_one]`. Rewrite using `[this]`. Conclude with `convergesAt_pi_single _ _ _`.
-/
theorem convergesAt_π (ρ : ℝ) : ConvergesAt (T.zcoeff T.π) ρ := by
  have := T.zcoeff_π_pow 1
  rw [pow_one] at this
  rw [this]; exact convergesAt_pi_single _ _ _

/- English proof (translation)
Rewrite using `[zcoeff_teich]`. Conclude with `convergesAt_pi_single _ _ _`.
-/
theorem convergesAt_teich (z : L) (ρ : ℝ) : ConvergesAt (T.zcoeff (T.teich z)) ρ := by
  rw [zcoeff_teich]; exact convergesAt_pi_single _ _ _

/- English proof (translation)
Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Break down `lt_or_ge n 0 with hn | hn` into its components or cases. Rewrite using `[T.zcoeff_of_neg _ hn, norm_zero, zero_mul]`. Conclude with `gaussNorm_nonneg (hρ.trans_le hle)`. Conclude with `(mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hn hρ.le hle) (norm_nonneg _)).trans (hx'.le_gaussNorm n)`.
-/
theorem gaussNorm_mono {x : Γ} {ρ ρ' : ℝ} (hρ : 0 < ρ) (hle : ρ ≤ ρ')
    (hx' : ConvergesAt (T.zcoeff x) ρ') :
    gaussNorm (T.zcoeff x) ρ ≤ gaussNorm (T.zcoeff x) ρ' := by
  refine gaussNorm_le fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact gaussNorm_nonneg (hρ.trans_le hle)
  · exact (mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hn hρ.le hle) (norm_nonneg _)).trans
      (hx'.le_gaussNorm n)

include hξ in
/- English proof (translation)
Establish `hV` using `(T.ξtail ξ).2`. Establish `h1 : ‖T.red (T.ξtail ξ : Γ)‖ = 1`. Use `hξ.norm_coeff_one` as an intermediate fact. Rewrite `this` using `[coeff_succ, coeff_zero]`. Then use the resulting hypothesis. Rewrite using `[T.gaussNorm_zcoeff_mul hρ hρ1 (T.convergesAt_π ρ) (T.convergesAt_of_mem_int hV hρ hρ1), T.gaussNorm_π hρ, T.gaussNorm_eq_one_of_mem_int hV h1 hρ hρ1, mul_one]`.
-/
theorem gaussNorm_πξtail {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    gaussNorm (T.zcoeff (T.π * (T.ξtail ξ : Γ))) ρ = ρ := by
  have hV := (T.ξtail ξ).2
  have h1 : ‖T.red (T.ξtail ξ : Γ)‖ = 1 := by
    have := hξ.norm_coeff_one; rwa [coeff_succ, coeff_zero] at this
  rw [T.gaussNorm_zcoeff_mul hρ hρ1 (T.convergesAt_π ρ) (T.convergesAt_of_mem_int hV hρ hρ1),
    T.gaussNorm_π hρ, T.gaussNorm_eq_one_of_mem_int hV h1 hρ hρ1, mul_one]

include hξ in
/- English proof (translation)
Establish `hρ1 : ρ < 1` using `hρr.trans hξ.norm_coeff_zero_lt`. Establish `ht` using `T.convergesAt_teich (T.coeff ξ 0) ρ`. Establish `hw` using `T.convergesAt_of_mem_int (Subring.mul_mem _ T.π_mem_int (T.ξtail ξ).2) hρ hρ1`. Establish `hnw` using `T.convergesAt_zcoeff_neg hρ hρ1 hw`. Use `conv_lhs => rw [T.coe_eq_teich_add ξ]`.

Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `(T.gaussNorm_zcoeff_add_le hρ hρ1.le ht hw).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[T.gaussNorm_teich _ hρ]`. Rewrite using `[T.gaussNorm_πξtail hξ hρ hρ1]`. Conclude with `hρr.le`.

Establish `hS` using `T.convergesAt_zcoeff_add hρ hρ1 ht hw`. Use `T.gaussNorm_zcoeff_add_le hρ hρ1.le hS hnw` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right, T.gaussNorm_teich _ hρ, T.gaussNorm_zcoeff_neg hρ hρ1 hw, T.gaussNorm_πξtail hξ hρ hρ1]`. Break down `le_total (gaussNorm (T.zcoeff (T.teich (T.coeff ξ 0) + T.π * (T.ξtail ξ : Γ))) ρ) ρ with h | h` into its components or cases. Rewrite `this` using `[max_eq_right h]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `this` using `[max_eq_left h]`. Conclude with `this`.
-/
theorem gaussNorm_ξ_of_lt {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < ‖T.coeff ξ 0‖) :
    gaussNorm (T.zcoeff (ξ : Γ)) ρ = ‖T.coeff ξ 0‖ := by
  have hρ1 : ρ < 1 := hρr.trans hξ.norm_coeff_zero_lt
  have ht := T.convergesAt_teich (T.coeff ξ 0) ρ
  have hw := T.convergesAt_of_mem_int (Subring.mul_mem _ T.π_mem_int (T.ξtail ξ).2) hρ hρ1
  have hnw := T.convergesAt_zcoeff_neg hρ hρ1 hw
  conv_lhs => rw [T.coe_eq_teich_add ξ]
  refine le_antisymm ?_ ?_
  · refine (T.gaussNorm_zcoeff_add_le hρ hρ1.le ht hw).trans (max_le ?_ ?_)
    · rw [T.gaussNorm_teich _ hρ]
    · rw [T.gaussNorm_πξtail hξ hρ hρ1]; exact hρr.le
  · have hS := T.convergesAt_zcoeff_add hρ hρ1 ht hw
    have := T.gaussNorm_zcoeff_add_le hρ hρ1.le hS hnw
    rw [add_neg_cancel_right, T.gaussNorm_teich _ hρ, T.gaussNorm_zcoeff_neg hρ hρ1 hw,
      T.gaussNorm_πξtail hξ hρ hρ1] at this
    rcases le_total (gaussNorm (T.zcoeff (T.teich (T.coeff ξ 0) + T.π * (T.ξtail ξ : Γ))) ρ) ρ
      with h | h
    · rw [max_eq_right h] at this; linarith
    · rw [max_eq_left h] at this; exact this

include hξ in
/- English proof (translation)
Establish `hρ : 0 < ρ` using `(norm_nonneg _).trans_lt hρr`. Establish `ht` using `T.convergesAt_teich (T.coeff ξ 0) ρ`. Establish `hnt` using `T.convergesAt_zcoeff_neg hρ hρ1 ht`. Establish `hw` using `T.convergesAt_of_mem_int (Subring.mul_mem _ T.π_mem_int (T.ξtail ξ).2) hρ hρ1`. Use `conv_lhs => rw [T.coe_eq_teich_add ξ]`.

Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `(T.gaussNorm_zcoeff_add_le hρ hρ1.le ht hw).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[T.gaussNorm_teich _ hρ]`. Conclude with `hρr.le`. Rewrite using `[T.gaussNorm_πξtail hξ hρ hρ1]`.

Establish `hS` using `T.convergesAt_zcoeff_add hρ hρ1 ht hw`. Use `T.gaussNorm_zcoeff_add_le hρ hρ1.le hS hnt` as an intermediate fact. Rewrite `this` using `[show T.teich (T.coeff ξ 0) + T.π * (T.ξtail ξ : Γ) + -T.teich (T.coeff ξ 0) = T.π * (T.ξtail ξ : Γ) by ring, T.gaussNorm_πξtail hξ hρ hρ1, T.gaussNorm_zcoeff_neg hρ hρ1 ht, T.gaussNorm_teich _ hρ]`. Break down `le_total (gaussNorm (T.zcoeff (T.teich (T.coeff ξ 0) + T.π * (T.ξtail ξ : Γ))) ρ) ‖T.coeff ξ 0‖ with h | h` into its components or cases. Rewrite `this` using `[max_eq_right h]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `this` using `[max_eq_left h]`. Conclude with `this`.
-/
theorem gaussNorm_ξ_of_gt {ρ : ℝ} (hρr : ‖T.coeff ξ 0‖ < ρ) (hρ1 : ρ < 1) :
    gaussNorm (T.zcoeff (ξ : Γ)) ρ = ρ := by
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hρr
  have ht := T.convergesAt_teich (T.coeff ξ 0) ρ
  have hnt := T.convergesAt_zcoeff_neg hρ hρ1 ht
  have hw := T.convergesAt_of_mem_int (Subring.mul_mem _ T.π_mem_int (T.ξtail ξ).2) hρ hρ1
  conv_lhs => rw [T.coe_eq_teich_add ξ]
  refine le_antisymm ?_ ?_
  · refine (T.gaussNorm_zcoeff_add_le hρ hρ1.le ht hw).trans (max_le ?_ ?_)
    · rw [T.gaussNorm_teich _ hρ]; exact hρr.le
    · rw [T.gaussNorm_πξtail hξ hρ hρ1]
  · have hS := T.convergesAt_zcoeff_add hρ hρ1 ht hw
    have := T.gaussNorm_zcoeff_add_le hρ hρ1.le hS hnt
    rw [show T.teich (T.coeff ξ 0) + T.π * (T.ξtail ξ : Γ) + -T.teich (T.coeff ξ 0) =
        T.π * (T.ξtail ξ : Γ) by ring, T.gaussNorm_πξtail hξ hρ hρ1,
      T.gaussNorm_zcoeff_neg hρ hρ1 ht, T.gaussNorm_teich _ hρ] at this
    rcases le_total (gaussNorm (T.zcoeff (T.teich (T.coeff ξ 0) + T.π * (T.ξtail ξ : Γ))) ρ)
      ‖T.coeff ξ 0‖ with h | h
    · rw [max_eq_right h] at this; linarith
    · rw [max_eq_left h] at this; exact this

include hξ in

/- English proof (translation)
Rewrite using `[Ne, toUntilt_eq_zero_iff]`. Introduce and unpack `⟨B, hB, hzB⟩`. Rewrite `hzB` using `[coe_teichInt]`. Use `set r := ‖T.coeff ξ 0‖ with hrdef`. Establish `hr0 : 0 < r` using `norm_pos_iff.2 hξ.coeff_zero_ne`.

Establish `hr1 : r < 1` using `hξ.norm_coeff_zero_lt`. Establish `hzpos : 0 < ‖z‖` using `norm_pos_iff.2 hz0`. Use `set ρ₁ := r / 2 with hρ₁def`. Use `set ρ₂ := (r + 1) / 2 with hρ₂def`. Establish `hρ₁ : 0 < ρ₁` using `by rw [hρ₁def]; positivity`.

Establish `hρ₁r : ρ₁ < r` using `by rw [hρ₁def]; linarith`. Establish `hrρ₂ : r < ρ₂` using `by rw [hρ₂def]; linarith`. Establish `hρ₂1 : ρ₂ < 1` using `by rw [hρ₂def]; linarith`. Establish `hρ₂ : 0 < ρ₂` using `hr0.trans hrρ₂`. Establish `e1` using `T.gaussNorm_zcoeff_mul hρ₁ (hρ₁r.trans hr1) (T.convergesAt_of_mem_int ξ.2 hρ₁ (hρ₁r.trans hr1)) (T.convergesAt_of_mem_int hB hρ₁ (hρ₁r.trans hr1))`.

Establish `e2` using `T.gaussNorm_zcoeff_mul hρ₂ hρ₂1 (T.convergesAt_of_mem_int ξ.2 hρ₂ hρ₂1) (T.convergesAt_of_mem_int hB hρ₂ hρ₂1)`. Rewrite `e1` using `[← hzB, T.gaussNorm_teich z hρ₁, T.gaussNorm_ξ_of_lt hξ hρ₁ hρ₁r]`. Rewrite `e2` using `[← hzB, T.gaussNorm_teich z hρ₂, T.gaussNorm_ξ_of_gt hξ hrρ₂ hρ₂1]`. Establish `hmono` using `T.gaussNorm_mono hρ₁ (hρ₁r.le.trans hrρ₂.le) (T.convergesAt_of_mem_int hB hρ₂ hρ₂1)`. Establish `h1 : gaussNorm (T.zcoeff B) ρ₁ = ‖z‖ / r` using `by field_simp; linarith`.

Establish `h2 : gaussNorm (T.zcoeff B) ρ₂ = ‖z‖ / ρ₂` using `by field_simp; linarith`. Rewrite `hmono` using `[h1, h2, div_le_div_iff_of_pos_left hzpos hr0 hρ₂]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem toUntilt_teich_ne_zero {z : L} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) :
    T.toUntilt ξ (T.teichInt hz) ≠ 0 := by
  rw [Ne, toUntilt_eq_zero_iff]
  rintro ⟨B, hB, hzB⟩
  rw [coe_teichInt] at hzB
  set r := ‖T.coeff ξ 0‖ with hrdef
  have hr0 : 0 < r := norm_pos_iff.2 hξ.coeff_zero_ne
  have hr1 : r < 1 := hξ.norm_coeff_zero_lt
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set ρ₁ := r / 2 with hρ₁def
  set ρ₂ := (r + 1) / 2 with hρ₂def
  have hρ₁ : 0 < ρ₁ := by rw [hρ₁def]; positivity
  have hρ₁r : ρ₁ < r := by rw [hρ₁def]; linarith
  have hrρ₂ : r < ρ₂ := by rw [hρ₂def]; linarith
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂def]; linarith
  have hρ₂ : 0 < ρ₂ := hr0.trans hrρ₂
  have e1 := T.gaussNorm_zcoeff_mul hρ₁ (hρ₁r.trans hr1) (T.convergesAt_of_mem_int ξ.2 hρ₁
    (hρ₁r.trans hr1)) (T.convergesAt_of_mem_int hB hρ₁ (hρ₁r.trans hr1))
  have e2 := T.gaussNorm_zcoeff_mul hρ₂ hρ₂1 (T.convergesAt_of_mem_int ξ.2 hρ₂ hρ₂1)
    (T.convergesAt_of_mem_int hB hρ₂ hρ₂1)
  rw [← hzB, T.gaussNorm_teich z hρ₁, T.gaussNorm_ξ_of_lt hξ hρ₁ hρ₁r] at e1
  rw [← hzB, T.gaussNorm_teich z hρ₂, T.gaussNorm_ξ_of_gt hξ hrρ₂ hρ₂1] at e2
  have hmono := T.gaussNorm_mono hρ₁ (hρ₁r.le.trans hrρ₂.le) (T.convergesAt_of_mem_int hB hρ₂ hρ₂1)
  have h1 : gaussNorm (T.zcoeff B) ρ₁ = ‖z‖ / r := by field_simp; linarith
  have h2 : gaussNorm (T.zcoeff B) ρ₂ = ‖z‖ / ρ₂ := by field_simp; linarith
  rw [h1, h2, div_le_div_iff_of_pos_left hzpos hr0 hρ₂] at hmono
  linarith

include hξ in

/- English proof (translation)
Introduce `h`. Take `⟨v, hv⟩` from `h.exists_right_inv`. Take `⟨V, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Rewrite `hv` using `[← map_mul, ← map_one (T.toUntilt ξ), toUntilt_eq_iff]`. Take `⟨B, hB, hVB⟩` from `hv`.

Use `congrArg T.red hVB` as an intermediate fact. Simplify using `only [Subring.coe_mul, coe_πInt, Subring.coe_one, map_sub, map_mul, red_π, zero_mul, map_one, zero_sub] at this`. Rewrite `this` using `[← coeff_zero]`. Establish `h1` using `T.norm_red_le_one B hB`. Establish `hr1` using `hξ.norm_coeff_zero_lt`.

Establish `h2 : ‖T.coeff ξ 0‖ * ‖T.red B‖ = 1`. Use `congrArg norm this` as an intermediate fact. Rewrite `this` using `[norm_neg, norm_one, norm_mul]`. Conclude with `this.symm`. Use polynomial arithmetic with `[norm_nonneg (T.coeff ξ 0), norm_nonneg (T.red B)]`.
-/
theorem not_isUnit_toUntilt_π : ¬ IsUnit (T.toUntilt ξ T.πInt) := by
  intro h
  obtain ⟨v, hv⟩ := h.exists_right_inv
  obtain ⟨V, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← map_one (T.toUntilt ξ), toUntilt_eq_iff] at hv
  obtain ⟨B, hB, hVB⟩ := hv
  have := congrArg T.red hVB
  simp only [Subring.coe_mul, coe_πInt, Subring.coe_one, map_sub, map_mul, red_π,
    zero_mul, map_one, zero_sub] at this
  rw [← coeff_zero] at this
  have h1 := T.norm_red_le_one B hB
  have hr1 := hξ.norm_coeff_zero_lt
  have h2 : ‖T.coeff ξ 0‖ * ‖T.red B‖ = 1 := by
    have := congrArg norm this
    rw [norm_neg, norm_one, norm_mul] at this
    exact this.symm
  nlinarith [norm_nonneg (T.coeff ξ 0), norm_nonneg (T.red B)]

include hξ in

/- English proof (translation)
Establish `hξ0` using `hξ.coeff_zero_ne`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Assume the negation of the conclusion as `hne`. Establish `hlt : ‖w‖ < 1` using `lt_of_le_of_ne hw hne`.

Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.2 hξ0) hlt`. Establish `hq : ‖w ^ N / T.coeff ξ 0‖ ≤ 1`. Rewrite using `[norm_div, norm_pow, div_le_one (norm_pos_iff.2 hξ0)]`. Conclude with `hN.le`. Establish `e : T.teichInt hw ^ N = T.teichInt (T.norm_coeff_zero_le ξ) * T.teichInt hq`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [SubmonoidClass.coe_pow, Subring.coe_mul, coe_teichInt]`. Rewrite using `[← T.teich_pow, ← T.teich_mul, mul_div_cancel₀ _ hξ0]`. Establish `hu'` using `hu.pow N`. Rewrite `hu'` using `[← map_pow, e, map_mul, T.toUntilt_teich_coeff_zero hξ, neg_mul, IsUnit.neg_iff, mul_assoc]`.

Conclude with `T.not_isUnit_toUntilt_π hξ (isUnit_of_mul_isUnit_left hu')`. Introduce `h1`. Conclude with `(T.isUnit_int_iff.2 (by rw [coe_teichInt, red_teich]; exact h1)).map _`.
-/
theorem isUnit_toUntilt_teich_iff {w : L} (hw : ‖w‖ ≤ 1) :
    IsUnit (T.toUntilt ξ (T.teichInt hw)) ↔ ‖w‖ = 1 := by
  have hξ0 := hξ.coeff_zero_ne
  constructor
  · intro hu
    by_contra hne
    have hlt : ‖w‖ < 1 := lt_of_le_of_ne hw hne
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hξ0) hlt
    have hq : ‖w ^ N / T.coeff ξ 0‖ ≤ 1 := by
      rw [norm_div, norm_pow, div_le_one (norm_pos_iff.2 hξ0)]; exact hN.le
    have e : T.teichInt hw ^ N = T.teichInt (T.norm_coeff_zero_le ξ) * T.teichInt hq := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, coe_teichInt]
      rw [← T.teich_pow, ← T.teich_mul, mul_div_cancel₀ _ hξ0]
    have hu' := hu.pow N
    rw [← map_pow, e, map_mul, T.toUntilt_teich_coeff_zero hξ, neg_mul, IsUnit.neg_iff,
      mul_assoc] at hu'
    exact T.not_isUnit_toUntilt_π hξ (isUnit_of_mul_isUnit_left hu')
  · intro h1
    exact (T.isUnit_int_iff.2 (by rw [coe_teichInt, red_teich]; exact h1)).map _

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Take `⟨A, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite `ha` using `[← map_pow, ← map_mul, toUntilt_eq_iff]`.

Take `⟨B, hB, hAB⟩` from `ha`. Use `⟨A, A.2, -B, neg_mem hB, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `[coe_πInt] at hAB`. Take the linear combination `-hAB`. Introduce and unpack `⟨A, hA, B, hB, h⟩`.

Use `⟨T.toUntilt ξ ⟨A, hA⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_mul, toUntilt_eq_iff]`. Use `⟨-B, neg_mem hB, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `[coe_πInt]`. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_span_toUntilt_π_pow_iff {Y : T.int} {k : ℕ} :
    T.toUntilt ξ Y ∈ Ideal.span {T.toUntilt ξ T.πInt ^ k} ↔
      ∃ A ∈ T.int, ∃ B ∈ T.int, (Y : Γ) = T.π ^ k * A + (ξ : Γ) * B := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_pow, ← map_mul, toUntilt_eq_iff] at ha
    obtain ⟨B, hB, hAB⟩ := ha
    refine ⟨A, A.2, -B, neg_mem hB, ?_⟩
    push_cast [coe_πInt] at hAB
    linear_combination -hAB
  · rintro ⟨A, hA, B, hB, h⟩
    refine ⟨T.toUntilt ξ ⟨A, hA⟩, ?_⟩
    rw [← map_pow, ← map_mul, toUntilt_eq_iff]
    refine ⟨-B, neg_mem hB, ?_⟩
    push_cast [coe_πInt]
    rw [h]; ring

include hξ in

/- English proof (translation)
Take `⟨Y, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨B, hB, hYB⟩` from `T.eq_mul_of_forall_approx hξ Y.2 fun k => (T.mem_span_toUntilt_π_pow_iff (ξ := ξ)).1 (h k)`. Conclude with `(T.toUntilt_eq_zero_iff).2 ⟨B, hB, hYB⟩`.
-/
theorem untilt_eq_zero_of_forall_mem {q : T.Untilt ξ}
    (h : ∀ k : ℕ, q ∈ Ideal.span {T.toUntilt ξ T.πInt ^ k}) : q = 0 := by
  obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨B, hB, hYB⟩ := T.eq_mul_of_forall_approx hξ Y.2 fun k =>
    (T.mem_span_toUntilt_π_pow_iff (ξ := ξ)).1 (h k)
  exact (T.toUntilt_eq_zero_iff).2 ⟨B, hB, hYB⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `T.mem_span_pow.1 h`. Conclude with `⟨w, T.exists_int_of_eq_π_pow_mul hx hw, hw⟩`.
-/
theorem mem_span_π_pow_of_int {x : Γ} (hx : x ∈ T.int) {k : ℕ}
    (h : x ∈ Ideal.span {T.π ^ k}) : ∃ w ∈ T.int, x = T.π ^ k * w := by
  obtain ⟨w, hw⟩ := T.mem_span_pow.1 h
  exact ⟨w, T.exists_int_of_eq_π_pow_mul hx hw, hw⟩

/- English proof (translation)
Use `haveI := T.isAdicComplete`. Establish `hstep : ∀ k (Y : T.int), T.toUntilt ξ Y = q k → ∃ Y' : T.int, T.toUntilt ξ Y' = q (k + 1) ∧ ∃ A : T.int, (Y' : Γ) - Y = T.π ^ k * A`. Introduce `k Y hY`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 (h k)`. Take `⟨A, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Use `⟨Y + T.πInt ^ k * A, ?_, A, ?_⟩` and prove the remaining obligations. Establish `ha' : T.toUntilt ξ A * T.toUntilt ξ T.πInt ^ k = q (k + 1) - q k` using `ha`. Rewrite using `[map_add, hY, map_mul, map_pow, mul_comm, ha']`. Expand and normalize the polynomial expressions, which then agree. Move the coercions through the operations in `[coe_πInt]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨Y0, hY0⟩` from `Ideal.Quotient.mk_surjective (q 0)`. Establish `key : ∃ Ys : ℕ → T.int, (∀ k, T.toUntilt ξ (Ys k) = q k) ∧ ∀ k, ∃ A : T.int, (Ys (k + 1) : Γ) - Ys k = T.π ^ k * A` using `by choose F hF1 hF2 using hstep`. Set `seq : (k : ℕ) → {Y : T.int // T.toUntilt ξ Y = q k}` to `fun k => Nat.rec (motive := fun k => {Y : T.int // T.toUntilt ξ Y = q k}) ⟨Y0, hY0⟩ (fun k s => ⟨F k s.1 s.2, hF1 k _ _⟩) k`. Use `⟨fun k => (seq k).1, fun k => (seq k).2, fun k => ?_⟩` and prove the remaining obligations.

Use `show ∃ A : T.int, ((F k (seq k).1 (seq k).2 : T.int) : Γ) - ((seq k).1 : Γ) = T.π ^ k * A`. Conclude with `hF2 k _ _`. Take `⟨Ys, hYs1, hYs2⟩` from `key`. Establish `hcauchy : ∀ {m n : ℕ}, m ≤ n → (Ys m : Γ) - Ys n ∈ Ideal.span {T.π ^ m}`. Introduce `m n hmn`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Take `⟨A, hA⟩` from `hYs2 n`. Establish `h1 : (Ys n : Γ) - Ys (n + 1) ∈ Ideal.span {T.π ^ m}`.

Rewrite using `[← neg_sub, hA]`. Conclude with `neg_mem (T.π_pow_mul_mem hmn _)`. Use `add_mem ih h1` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Take `⟨Yinf, hYinf⟩` from `IsPrecomplete.prec' (I := T.I) (fun k => (Ys k : Γ)) fun {m n} hmn => by`.

Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]`. Conclude with `hcauchy hmn`. Establish `hYinf' : ∀ k, Yinf - Ys k ∈ Ideal.span {T.π ^ k}` using `fun k => by`. Use `hYinf k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]`.

Use `neg_mem this` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Establish `hmem : Yinf ∈ T.int` using `T.mem_int_of_approx _ fun N => ⟨Ys N, (Ys N).2, hYinf' N⟩`. Use `⟨T.toUntilt ξ ⟨Yinf, hmem⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← hYs1 k, ← map_sub]`.

Take `⟨w, hw, hYw⟩` from `T.mem_span_π_pow_of_int (sub_mem hmem (Ys k).2) (hYinf' k)`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨T.toUntilt ξ ⟨w, hw⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_mul]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Move the coercions through the operations in `[coe_πInt]`. Rewrite using `[hYw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_untilt_limit (q : ℕ → T.Untilt ξ)
    (h : ∀ k, q (k + 1) - q k ∈ Ideal.span {T.toUntilt ξ T.πInt ^ k}) :
    ∃ q' : T.Untilt ξ, ∀ k, q' - q k ∈ Ideal.span {T.toUntilt ξ T.πInt ^ k} := by
  haveI := T.isAdicComplete

  have hstep : ∀ k (Y : T.int), T.toUntilt ξ Y = q k →
      ∃ Y' : T.int, T.toUntilt ξ Y' = q (k + 1) ∧ ∃ A : T.int, (Y' : Γ) - Y = T.π ^ k * A := by
    intro k Y hY
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (h k)
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨Y + T.πInt ^ k * A, ?_, A, ?_⟩
    · have ha' : T.toUntilt ξ A * T.toUntilt ξ T.πInt ^ k = q (k + 1) - q k := ha
      rw [map_add, hY, map_mul, map_pow, mul_comm, ha']; ring
    · push_cast [coe_πInt]; ring
  obtain ⟨Y0, hY0⟩ := Ideal.Quotient.mk_surjective (q 0)

  have key : ∃ Ys : ℕ → T.int, (∀ k, T.toUntilt ξ (Ys k) = q k) ∧
      ∀ k, ∃ A : T.int, (Ys (k + 1) : Γ) - Ys k = T.π ^ k * A := by
    choose F hF1 hF2 using hstep
    let seq : (k : ℕ) → {Y : T.int // T.toUntilt ξ Y = q k} := fun k =>
      Nat.rec (motive := fun k => {Y : T.int // T.toUntilt ξ Y = q k}) ⟨Y0, hY0⟩
        (fun k s => ⟨F k s.1 s.2, hF1 k _ _⟩) k
    refine ⟨fun k => (seq k).1, fun k => (seq k).2, fun k => ?_⟩
    show ∃ A : T.int, ((F k (seq k).1 (seq k).2 : T.int) : Γ) - ((seq k).1 : Γ) = T.π ^ k * A
    exact hF2 k _ _
  obtain ⟨Ys, hYs1, hYs2⟩ := key
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → (Ys m : Γ) - Ys n ∈ Ideal.span {T.π ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      obtain ⟨A, hA⟩ := hYs2 n
      have h1 : (Ys n : Γ) - Ys (n + 1) ∈ Ideal.span {T.π ^ m} := by
        rw [← neg_sub, hA]; exact neg_mem (T.π_pow_mul_mem hmn _)
      have := add_mem ih h1
      rwa [sub_add_sub_cancel] at this
  obtain ⟨Yinf, hYinf⟩ := IsPrecomplete.prec' (I := T.I) (fun k => (Ys k : Γ)) fun {m n} hmn => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]; exact hcauchy hmn
  have hYinf' : ∀ k, Yinf - Ys k ∈ Ideal.span {T.π ^ k} := fun k => by
    have := hYinf k
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow] at this
    have := neg_mem this; rwa [neg_sub] at this
  have hmem : Yinf ∈ T.int := T.mem_int_of_approx _ fun N => ⟨Ys N, (Ys N).2, hYinf' N⟩
  refine ⟨T.toUntilt ξ ⟨Yinf, hmem⟩, fun k => ?_⟩
  rw [← hYs1 k, ← map_sub]
  obtain ⟨w, hw, hYw⟩ := T.mem_span_π_pow_of_int (sub_mem hmem (Ys k).2) (hYinf' k)
  rw [Ideal.mem_span_singleton']
  refine ⟨T.toUntilt ξ ⟨w, hw⟩, ?_⟩
  rw [← map_pow, ← map_mul]
  congr 1
  apply Subtype.ext
  push_cast [coe_πInt]
  rw [hYw]; ring

include hξ in

/- English proof (translation)
Establish `hξ0` using `hξ.coeff_zero_ne`. Take `⟨Vinv, hVinv⟩` from `(T.isUnit_ξtail hξ).exists_right_inv`. Establish `hθπ : T.toUntilt ξ T.πInt = -(T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * T.toUntilt ξ Vinv)`. Rewrite using `[T.toUntilt_teich_coeff_zero hξ, neg_mul, neg_neg, mul_assoc, ← map_mul, hVinv, map_one, mul_one]`. Proceed by induction on `k with`.

Consider the case `zero => intro Y`. Use `left`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `Y`.

Use `set y0 := T.coeff (Y : Γ) 0 with hy0def`. Establish `hy0 : ‖y0‖ ≤ 1` using `T.norm_coeff_zero_le Y`. Establish `hYeq : T.toUntilt ξ Y = T.toUntilt ξ (T.teichInt hy0) + T.toUntilt ξ T.πInt * T.toUntilt ξ (T.ξtail Y)`. Rewrite using `[← map_mul, ← map_add]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `T.coe_eq_teich_add Y`. Break down `lt_or_ge ‖T.coeff (ξ : Γ) 0‖ ‖y0‖ with hlt | hle` into its components or cases. Use `right`.

Establish `hy00 : y0 ≠ 0`. Introduce `h`. Rewrite `hlt` using `[h, norm_zero]`. Conclude with `absurd hlt (not_lt.2 (norm_nonneg _))`. Establish `he : ‖T.coeff (ξ : Γ) 0 / y0‖ ≤ 1`.

Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hy00)]`. Conclude with `hlt.le`. Establish `he' : ‖T.coeff (ξ : Γ) 0 / y0‖ < 1`. Rewrite using `[norm_div, div_lt_one (norm_pos_iff.2 hy00)]`. Conclude with `hlt`.

Use `set E : T.int := 1 - T.teichInt he * Vinv * T.ξtail Y`. Establish `hE : IsUnit E`. Rewrite using `[isUnit_int_iff]`. Establish `hsmall : ‖T.red ((T.teichInt he * Vinv * T.ξtail Y : T.int) : Γ)‖ < 1`. Simplify using `only [Subring.coe_mul, coe_teichInt, map_mul, red_teich, norm_mul]`.

Establish `h1` using `T.norm_red_le_one _ Vinv.2`. Establish `h2` using `T.norm_red_le_one _ (T.ξtail Y).2`. Combine the equalities or inequalities in the displayed calculation. Establish `: T.red (E : Γ) = 1 - T.red ((T.teichInt he * Vinv * T.ξtail Y : T.int) : Γ)`. Simplify using `[E]`.

Rewrite using `[this, sub_eq_add_neg]`. Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one, norm_neg]; exact hsmall.ne'), norm_one, norm_neg, max_eq_left hsmall.le]`. Use `⟨y0, hy00, hy0, T.toUntilt ξ E, hE.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[hYeq, hθπ]`. Establish `hsplit : T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) = T.toUntilt ξ (T.teichInt hy0) * T.toUntilt ξ (T.teichInt he)`.

Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subring.coe_mul, coe_teichInt]`. Rewrite using `[← T.teich_mul, mul_div_cancel₀ _ hy00]`.

Rewrite using `[hsplit]`. Simplify using `only [E, map_sub, map_one, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : ‖y0 / T.coeff (ξ : Γ) 0‖ ≤ 1`. Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hξ0)]`.

Conclude with `hle`. Use `set Y'' : T.int := T.ξtail Y - T.ξtail ξ * T.teichInt hq`. Establish `hYY : T.toUntilt ξ Y = T.toUntilt ξ T.πInt * T.toUntilt ξ Y''`. Rewrite using `[hYeq]`. Establish `hsplit : T.toUntilt ξ (T.teichInt hy0) = T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * T.toUntilt ξ (T.teichInt hq)`.

Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subring.coe_mul, coe_teichInt]`. Rewrite using `[← T.teich_mul, mul_div_cancel₀ _ hξ0]`.

Rewrite using `[hsplit, T.toUntilt_teich_coeff_zero hξ]`. Simplify using `only [Y'', map_sub, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Break down `ih Y'' with h1 | ⟨z, hz0, hz, u, hu, h2⟩` into its components or cases. Use `left`.

Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 h1`. Conclude with `Ideal.mem_span_singleton'.2 ⟨a, by rw [hYY, ← ha, pow_succ]; ring⟩`. Use `right`. Establish `hz' : ‖T.coeff (ξ : Γ) 0 * z‖ ≤ 1`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ (T.norm_coeff_zero_le ξ) (norm_nonneg _) hz`. Use `⟨T.coeff (ξ : Γ) 0 * z, mul_ne_zero hξ0 hz0, hz', -(T.toUntilt ξ Vinv * u), ?_, ?_⟩` and prove the remaining obligations. Establish `hVu : IsUnit (T.toUntilt ξ Vinv)` using `isUnit_iff_exists_inv.2 ⟨T.toUntilt ξ (T.ξtail ξ), by rw [← map_mul, mul_comm, hVinv, map_one]⟩`. Conclude with `(hVu.mul hu).neg`. Rewrite using `[hYY, h2, hθπ]`.

Establish `hsplit : T.toUntilt ξ (T.teichInt hz') = T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * T.toUntilt ξ (T.teichInt hz)`. Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subring.coe_mul, coe_teichInt, T.teich_mul]`.

Rewrite using `[hsplit]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toUntilt_dichotomy (k : ℕ) : ∀ Y : T.int,
    T.toUntilt ξ Y ∈ Ideal.span {T.toUntilt ξ T.πInt ^ k} ∨
      ∃ (z : L) (_ : z ≠ 0) (hz : ‖z‖ ≤ 1) (u : T.Untilt ξ), IsUnit u ∧
        T.toUntilt ξ Y = T.toUntilt ξ (T.teichInt hz) * u := by
  have hξ0 := hξ.coeff_zero_ne
  obtain ⟨Vinv, hVinv⟩ := (T.isUnit_ξtail hξ).exists_right_inv
  have hθπ : T.toUntilt ξ T.πInt =
      -(T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * T.toUntilt ξ Vinv) := by
    rw [T.toUntilt_teich_coeff_zero hξ, neg_mul, neg_neg, mul_assoc, ← map_mul, hVinv, map_one,
      mul_one]
  induction k with
  | zero => intro Y; left; simp
  | succ k ih =>
    intro Y
    set y0 := T.coeff (Y : Γ) 0 with hy0def
    have hy0 : ‖y0‖ ≤ 1 := T.norm_coeff_zero_le Y
    have hYeq : T.toUntilt ξ Y = T.toUntilt ξ (T.teichInt hy0) +
        T.toUntilt ξ T.πInt * T.toUntilt ξ (T.ξtail Y) := by
      rw [← map_mul, ← map_add]
      congr 1
      apply Subtype.ext
      push_cast
      exact T.coe_eq_teich_add Y
    rcases lt_or_ge ‖T.coeff (ξ : Γ) 0‖ ‖y0‖ with hlt | hle
    ·
      right
      have hy00 : y0 ≠ 0 := by
        intro h; rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.2 (norm_nonneg _))
      have he : ‖T.coeff (ξ : Γ) 0 / y0‖ ≤ 1 := by
        rw [norm_div, div_le_one (norm_pos_iff.2 hy00)]; exact hlt.le
      have he' : ‖T.coeff (ξ : Γ) 0 / y0‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.2 hy00)]; exact hlt
      set E : T.int := 1 - T.teichInt he * Vinv * T.ξtail Y
      have hE : IsUnit E := by
        rw [isUnit_int_iff]
        have hsmall : ‖T.red ((T.teichInt he * Vinv * T.ξtail Y : T.int) : Γ)‖ < 1 := by
          simp only [Subring.coe_mul, coe_teichInt, map_mul, red_teich, norm_mul]
          have h1 := T.norm_red_le_one _ Vinv.2
          have h2 := T.norm_red_le_one _ (T.ξtail Y).2
          calc ‖T.coeff (ξ : Γ) 0 / y0‖ * ‖T.red (Vinv : Γ)‖ * ‖T.red (T.ξtail Y : Γ)‖
              ≤ ‖T.coeff (ξ : Γ) 0 / y0‖ * 1 * 1 := by gcongr
            _ < 1 := by simpa using he'
        have : T.red (E : Γ) = 1 - T.red ((T.teichInt he * Vinv * T.ξtail Y : T.int) : Γ) := by
          simp [E]
        rw [this, sub_eq_add_neg]
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one, norm_neg]; exact hsmall.ne'),
          norm_one, norm_neg, max_eq_left hsmall.le]
      refine ⟨y0, hy00, hy0, T.toUntilt ξ E, hE.map _, ?_⟩
      rw [hYeq, hθπ]
      have hsplit : T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) =
          T.toUntilt ξ (T.teichInt hy0) * T.toUntilt ξ (T.teichInt he) := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subring.coe_mul, coe_teichInt]
        rw [← T.teich_mul, mul_div_cancel₀ _ hy00]
      rw [hsplit]
      simp only [E, map_sub, map_one, map_mul]
      ring
    ·
      have hq : ‖y0 / T.coeff (ξ : Γ) 0‖ ≤ 1 := by
        rw [norm_div, div_le_one (norm_pos_iff.2 hξ0)]; exact hle
      set Y'' : T.int := T.ξtail Y - T.ξtail ξ * T.teichInt hq
      have hYY : T.toUntilt ξ Y = T.toUntilt ξ T.πInt * T.toUntilt ξ Y'' := by
        rw [hYeq]
        have hsplit : T.toUntilt ξ (T.teichInt hy0) =
            T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * T.toUntilt ξ (T.teichInt hq) := by
          rw [← map_mul]
          congr 1
          apply Subtype.ext
          simp only [Subring.coe_mul, coe_teichInt]
          rw [← T.teich_mul, mul_div_cancel₀ _ hξ0]
        rw [hsplit, T.toUntilt_teich_coeff_zero hξ]
        simp only [Y'', map_sub, map_mul]
        ring
      rcases ih Y'' with h1 | ⟨z, hz0, hz, u, hu, h2⟩
      · left
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
        exact Ideal.mem_span_singleton'.2 ⟨a, by rw [hYY, ← ha, pow_succ]; ring⟩
      · right
        have hz' : ‖T.coeff (ξ : Γ) 0 * z‖ ≤ 1 := by
          rw [norm_mul]; exact mul_le_one₀ (T.norm_coeff_zero_le ξ) (norm_nonneg _) hz
        refine ⟨T.coeff (ξ : Γ) 0 * z, mul_ne_zero hξ0 hz0, hz',
          -(T.toUntilt ξ Vinv * u), ?_, ?_⟩
        · have hVu : IsUnit (T.toUntilt ξ Vinv) :=
            isUnit_iff_exists_inv.2 ⟨T.toUntilt ξ (T.ξtail ξ), by rw [← map_mul, mul_comm, hVinv, map_one]⟩
          exact (hVu.mul hu).neg
        · rw [hYY, h2, hθπ]
          have hsplit : T.toUntilt ξ (T.teichInt hz') =
              T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * T.toUntilt ξ (T.teichInt hz) := by
            rw [← map_mul]
            congr 1
            apply Subtype.ext
            simp only [Subring.coe_mul, coe_teichInt, T.teich_mul]
          rw [hsplit]
          ring

include hξ in

/- English proof (translation)
Take `⟨Y, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Assume the negation of the conclusion as `hcon`. Apply `hq` to reduce the goal to its premises. Use `T.untilt_eq_zero_of_forall_mem hξ fun k => ?_` and prove the remaining obligations. Break down `T.toUntilt_dichotomy hξ k Y with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hcon`.
-/
theorem exists_teich_mul_unit {q : T.Untilt ξ} (hq : q ≠ 0) :
    ∃ (z : L) (_ : z ≠ 0) (hz : ‖z‖ ≤ 1) (u : T.Untilt ξ), IsUnit u ∧
      q = T.toUntilt ξ (T.teichInt hz) * u := by
  obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective q
  by_contra hcon
  apply hq
  refine T.untilt_eq_zero_of_forall_mem hξ fun k => ?_
  rcases T.toUntilt_dichotomy hξ k Y with h | h
  · exact h
  · exact absurd h hcon

/- English proof (translation)
Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subring.coe_mul, coe_teichInt, T.teich_mul]`.
-/
theorem toUntilt_teich_mul {z w : L} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hzw : ‖z * w‖ ≤ 1) :
    T.toUntilt ξ (T.teichInt hzw) = T.toUntilt ξ (T.teichInt hz) * T.toUntilt ξ (T.teichInt hw) := by
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subring.coe_mul, coe_teichInt, T.teich_mul]

include hξ in
/- English proof (translation)
Use `⟨⟨T.toUntilt ξ (T.teichInt (show ‖(1 : L)‖ ≤ 1 by simp)), 0, ?_⟩⟩` and prove the remaining obligations. Conclude with `T.toUntilt_teich_ne_zero hξ one_ne_zero _`.
-/
theorem nontrivial_untilt : Nontrivial (T.Untilt ξ) := by
  refine ⟨⟨T.toUntilt ξ (T.teichInt (show ‖(1 : L)‖ ≤ 1 by simp)), 0, ?_⟩⟩
  exact T.toUntilt_teich_ne_zero hξ one_ne_zero _

include hξ in

/- English proof (translation)
Use `haveI := T.nontrivial_untilt hξ`. Establish `: NoZeroDivisors (T.Untilt ξ)` using `⟨fun {q₁ q₂} h => by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨z₁, hz₁0, hz₁, u₁, hu₁, rfl⟩` from `T.exists_teich_mul_unit hξ hne.1`.

Take `⟨z₂, hz₂0, hz₂, u₂, hu₂, rfl⟩` from `T.exists_teich_mul_unit hξ hne.2`. Establish `hz : ‖z₁ * z₂‖ ≤ 1` using `by rw [norm_mul]; exact mul_le_one₀ hz₁ (norm_nonneg _) hz₂`. Establish `e : T.toUntilt ξ (T.teichInt hz₁) * u₁ * (T.toUntilt ξ (T.teichInt hz₂) * u₂) = T.toUntilt ξ (T.teichInt hz) * (u₁ * u₂)`. Rewrite using `[T.toUntilt_teich_mul hz₁ hz₂ hz]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e]`. Conclude with `T.toUntilt_teich_ne_zero hξ (mul_ne_zero hz₁0 hz₂0) hz ((hu₁.mul hu₂).mul_left_eq_zero.1 h)⟩`. Conclude with `NoZeroDivisors.to_isDomain _`.
-/
theorem isDomain_untilt : IsDomain (T.Untilt ξ) := by
  haveI := T.nontrivial_untilt hξ
  have : NoZeroDivisors (T.Untilt ξ) := ⟨fun {q₁ q₂} h => by
    by_contra hne
    push_neg at hne
    obtain ⟨z₁, hz₁0, hz₁, u₁, hu₁, rfl⟩ := T.exists_teich_mul_unit hξ hne.1
    obtain ⟨z₂, hz₂0, hz₂, u₂, hu₂, rfl⟩ := T.exists_teich_mul_unit hξ hne.2
    have hz : ‖z₁ * z₂‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ hz₁ (norm_nonneg _) hz₂
    have e : T.toUntilt ξ (T.teichInt hz₁) * u₁ * (T.toUntilt ξ (T.teichInt hz₂) * u₂) =
        T.toUntilt ξ (T.teichInt hz) * (u₁ * u₂) := by
      rw [T.toUntilt_teich_mul hz₁ hz₂ hz]; ring
    rw [e] at h
    exact T.toUntilt_teich_ne_zero hξ (mul_ne_zero hz₁0 hz₂0) hz ((hu₁.mul hu₂).mul_left_eq_zero.1 h)⟩
  exact NoZeroDivisors.to_isDomain _

open Classical in

def untiltNorm (hξ : T.IsPrimOne ξ) (q : T.Untilt ξ) : ℝ :=
  if h : q = 0 then 0 else ‖Classical.choose (T.exists_teich_mul_unit hξ h)‖

include hξ in
/- English proof (translation)
Use `haveI := T.isDomain_untilt hξ`. Use `wlog hle : ‖z‖ ≤ ‖z'‖ generalizing z z' u u'`. Conclude with `(this hz'0 hz0 hz' hz hu' hu h.symm (le_of_not_ge hle)).symm`. Establish `hw : ‖z / z'‖ ≤ 1` using `by rw [norm_div, div_le_one (norm_pos_iff.2 hz'0)]; exact hle`. Establish `hzz : ‖z' * (z / z')‖ ≤ 1` using `by rw [mul_div_cancel₀ _ hz'0]; exact hz`.

Establish `e1 : T.toUntilt ξ (T.teichInt hz) = T.toUntilt ξ (T.teichInt hz') * T.toUntilt ξ (T.teichInt hw)`. Rewrite using `[← T.toUntilt_teich_mul hz' hw hzz]`. Use `congr 2`. Conclude with `(mul_div_cancel₀ _ hz'0).symm`. Rewrite `h` using `[e1, mul_assoc]`.

Establish `h2` using `mul_left_cancel₀ (T.toUntilt_teich_ne_zero hξ hz'0 hz') h`. Establish `hunit : IsUnit (T.toUntilt ξ (T.teichInt hw))`. Use `hu'.mul hu.unit⁻¹.isUnit` as an intermediate fact. Rewrite `this` using `[← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]`. Conclude with `this`.

Rewrite `hunit` using `[T.isUnit_toUntilt_teich_iff hξ]`. Rewrite `hunit` using `[norm_div, div_eq_one_iff_eq (norm_pos_iff.2 hz'0).ne']`. Conclude with `hunit`.
-/
theorem norm_eq_of_teich_mul_unit {z z' : L} (hz0 : z ≠ 0) (hz'0 : z' ≠ 0) (hz : ‖z‖ ≤ 1)
    (hz' : ‖z'‖ ≤ 1) {u u' : T.Untilt ξ} (hu : IsUnit u) (hu' : IsUnit u')
    (h : T.toUntilt ξ (T.teichInt hz) * u = T.toUntilt ξ (T.teichInt hz') * u') : ‖z‖ = ‖z'‖ := by
  haveI := T.isDomain_untilt hξ

  wlog hle : ‖z‖ ≤ ‖z'‖ generalizing z z' u u'
  · exact (this hz'0 hz0 hz' hz hu' hu h.symm (le_of_not_ge hle)).symm
  have hw : ‖z / z'‖ ≤ 1 := by rw [norm_div, div_le_one (norm_pos_iff.2 hz'0)]; exact hle
  have hzz : ‖z' * (z / z')‖ ≤ 1 := by rw [mul_div_cancel₀ _ hz'0]; exact hz
  have e1 : T.toUntilt ξ (T.teichInt hz) =
      T.toUntilt ξ (T.teichInt hz') * T.toUntilt ξ (T.teichInt hw) := by
    rw [← T.toUntilt_teich_mul hz' hw hzz]
    congr 2
    exact (mul_div_cancel₀ _ hz'0).symm
  rw [e1, mul_assoc] at h
  have h2 := mul_left_cancel₀ (T.toUntilt_teich_ne_zero hξ hz'0 hz') h
  have hunit : IsUnit (T.toUntilt ξ (T.teichInt hw)) := by
    have := hu'.mul hu.unit⁻¹.isUnit
    rw [← h2, mul_assoc, IsUnit.mul_val_inv, mul_one] at this
    exact this
  rw [T.isUnit_toUntilt_teich_iff hξ] at hunit
  rw [norm_div, div_eq_one_iff_eq (norm_pos_iff.2 hz'0).ne'] at hunit
  exact hunit

include hξ in
/- English proof (translation)
Use `haveI := T.isDomain_untilt hξ`. Establish `hq : q ≠ 0`. Rewrite using `[h]`. Conclude with `mul_ne_zero (T.toUntilt_teich_ne_zero hξ hz0 hz) hu.ne_zero`. Rewrite using `[untiltNorm, dif_neg hq]`.

Take `⟨hz'0, hz', u', hu', h'⟩` from `Classical.choose_spec (T.exists_teich_mul_unit hξ hq)`. Conclude with `T.norm_eq_of_teich_mul_unit hξ hz'0 hz0 hz' hz hu' hu (h'.symm.trans h)`.
-/
theorem untiltNorm_eq {q : T.Untilt ξ} {z : L} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) {u : T.Untilt ξ}
    (hu : IsUnit u) (h : q = T.toUntilt ξ (T.teichInt hz) * u) : T.untiltNorm hξ q = ‖z‖ := by
  haveI := T.isDomain_untilt hξ
  have hq : q ≠ 0 := by
    rw [h]; exact mul_ne_zero (T.toUntilt_teich_ne_zero hξ hz0 hz) hu.ne_zero
  rw [untiltNorm, dif_neg hq]
  obtain ⟨hz'0, hz', u', hu', h'⟩ := Classical.choose_spec (T.exists_teich_mul_unit hξ hq)
  exact T.norm_eq_of_teich_mul_unit hξ hz'0 hz0 hz' hz hu' hu (h'.symm.trans h)

/- English proof (translation)
Rewrite using `[untiltNorm, dif_pos rfl]`.
-/
@[simp] theorem untiltNorm_zero : T.untiltNorm hξ 0 = 0 := by rw [untiltNorm, dif_pos rfl]

/- English proof (translation)
Distinguish the cases in `hz0 : z = 0`. Substitute `hz0` using the available equality. Establish `: T.teichInt hz = 0` using `Subtype.ext (by simp)`. Rewrite using `[this, map_zero, untiltNorm_zero, norm_zero]`. Conclude with `T.untiltNorm_eq hξ hz0 hz isUnit_one (mul_one _).symm`.
-/
theorem untiltNorm_teich {z : L} (hz : ‖z‖ ≤ 1) :
    T.untiltNorm hξ (T.toUntilt ξ (T.teichInt hz)) = ‖z‖ := by
  by_cases hz0 : z = 0
  · subst hz0
    have : T.teichInt hz = 0 := Subtype.ext (by simp)
    rw [this, map_zero, untiltNorm_zero, norm_zero]
  · exact T.untiltNorm_eq hξ hz0 hz isUnit_one (mul_one _).symm

/- English proof (translation)
Apply the tactic sequence `unfold untiltNorm; split_ifs <;> simp`.
-/
theorem untiltNorm_nonneg (q : T.Untilt ξ) : 0 ≤ T.untiltNorm hξ q := by
  unfold untiltNorm; split_ifs <;> simp

/- English proof (translation)
Distinguish the cases in `hq : q = 0`. Rewrite using `[hq, untiltNorm_zero]`. Conclude with `zero_le_one`. Take `⟨z, hz0, hz, u, hu, rfl⟩` from `T.exists_teich_mul_unit hξ hq`. Rewrite using `[T.untiltNorm_eq hξ hz0 hz hu rfl]`.

Conclude with `hz`.
-/
theorem untiltNorm_le_one (q : T.Untilt ξ) : T.untiltNorm hξ q ≤ 1 := by
  by_cases hq : q = 0
  · rw [hq, untiltNorm_zero]; exact zero_le_one
  obtain ⟨z, hz0, hz, u, hu, rfl⟩ := T.exists_teich_mul_unit hξ hq
  rw [T.untiltNorm_eq hξ hz0 hz hu rfl]; exact hz

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hq`. Take `⟨z, hz0, hz, u, hu, rfl⟩` from `T.exists_teich_mul_unit hξ hq`. Rewrite `h` using `[T.untiltNorm_eq hξ hz0 hz hu rfl]`.

Conclude with `hz0 (norm_eq_zero.1 h)`. Introduce and unpack `rfl`. Conclude with `T.untiltNorm_zero hξ`.
-/
theorem untiltNorm_eq_zero_iff {q : T.Untilt ξ} : T.untiltNorm hξ q = 0 ↔ q = 0 := by
  constructor
  · intro h
    by_contra hq
    obtain ⟨z, hz0, hz, u, hu, rfl⟩ := T.exists_teich_mul_unit hξ hq
    rw [T.untiltNorm_eq hξ hz0 hz hu rfl] at h
    exact hz0 (norm_eq_zero.1 h)
  · rintro rfl; exact T.untiltNorm_zero hξ

/- English proof (translation)
Distinguish the cases in `h₁ : q₁ = 0`. Rewrite using `[h₁, zero_mul, untiltNorm_zero, zero_mul]`. Distinguish the cases in `h₂ : q₂ = 0`. Rewrite using `[h₂, mul_zero, untiltNorm_zero, mul_zero]`. Take `⟨z₁, hz₁0, hz₁, u₁, hu₁, rfl⟩` from `T.exists_teich_mul_unit hξ h₁`.

Take `⟨z₂, hz₂0, hz₂, u₂, hu₂, rfl⟩` from `T.exists_teich_mul_unit hξ h₂`. Establish `hz : ‖z₁ * z₂‖ ≤ 1` using `by rw [norm_mul]; exact mul_le_one₀ hz₁ (norm_nonneg _) hz₂`. Rewrite using `[T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl, T.untiltNorm_eq hξ hz₂0 hz₂ hu₂ rfl, T.untiltNorm_eq hξ (mul_ne_zero hz₁0 hz₂0) hz (hu₁.mul hu₂) (by rw [T.toUntilt_teich_mul hz₁ hz₂ hz]; ring), norm_mul]`.
-/
theorem untiltNorm_mul (q₁ q₂ : T.Untilt ξ) :
    T.untiltNorm hξ (q₁ * q₂) = T.untiltNorm hξ q₁ * T.untiltNorm hξ q₂ := by
  by_cases h₁ : q₁ = 0
  · rw [h₁, zero_mul, untiltNorm_zero, zero_mul]
  by_cases h₂ : q₂ = 0
  · rw [h₂, mul_zero, untiltNorm_zero, mul_zero]
  obtain ⟨z₁, hz₁0, hz₁, u₁, hu₁, rfl⟩ := T.exists_teich_mul_unit hξ h₁
  obtain ⟨z₂, hz₂0, hz₂, u₂, hu₂, rfl⟩ := T.exists_teich_mul_unit hξ h₂
  have hz : ‖z₁ * z₂‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ hz₁ (norm_nonneg _) hz₂
  rw [T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl, T.untiltNorm_eq hξ hz₂0 hz₂ hu₂ rfl,
    T.untiltNorm_eq hξ (mul_ne_zero hz₁0 hz₂0) hz (hu₁.mul hu₂)
      (by rw [T.toUntilt_teich_mul hz₁ hz₂ hz]; ring), norm_mul]

/- English proof (translation)
Use `T.untiltNorm_eq hξ one_ne_zero (show ‖(1 : L)‖ ≤ 1 by simp) hu (q := u) (by` as an intermediate fact. Establish `: T.teichInt (show ‖(1 : L)‖ ≤ 1 by simp) = 1` using `Subtype.ext (by simp)`. Rewrite using `[this, map_one, one_mul])`. Rewrite `this` using `[norm_one]`. Then use the resulting hypothesis.
-/
theorem untiltNorm_unit {u : T.Untilt ξ} (hu : IsUnit u) : T.untiltNorm hξ u = 1 := by
  have := T.untiltNorm_eq hξ one_ne_zero (show ‖(1 : L)‖ ≤ 1 by simp) hu (q := u) (by
    have : T.teichInt (show ‖(1 : L)‖ ≤ 1 by simp) = 1 := Subtype.ext (by simp)
    rw [this, map_one, one_mul])
  rwa [norm_one] at this

/- English proof (translation)
Use `wlog hle : T.untiltNorm hξ q₂ ≤ T.untiltNorm hξ q₁ generalizing q₁ q₂`. Rewrite using `[add_comm, max_comm]`. Conclude with `this q₂ q₁ (le_of_not_ge hle)`. Distinguish the cases in `h₁ : q₁ = 0`. Rewrite `hle`, the goal using `[h₁, untiltNorm_zero]`.

Use `le_antisymm hle (T.untiltNorm_nonneg hξ q₂)` as an intermediate fact. Rewrite using `[(T.untiltNorm_eq_zero_iff hξ).1 this, add_zero, untiltNorm_zero, max_self]`. Take `⟨z₁, hz₁0, hz₁, u₁, hu₁, rfl⟩` from `T.exists_teich_mul_unit hξ h₁`. Rewrite using `[T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl, max_eq_left (by rwa [T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl] at hle)]`. Distinguish the cases in `h₂ : q₂ = 0`.

Rewrite using `[h₂, add_zero, T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl]`. Take `⟨z₂, hz₂0, hz₂, u₂, hu₂, rfl⟩` from `T.exists_teich_mul_unit hξ h₂`. Rewrite `hle` using `[T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl, T.untiltNorm_eq hξ hz₂0 hz₂ hu₂ rfl]`. Establish `hw : ‖z₂ / z₁‖ ≤ 1` using `by rw [norm_div, div_le_one (norm_pos_iff.2 hz₁0)]; exact hle`. Establish `hzz : ‖z₁ * (z₂ / z₁)‖ ≤ 1` using `by rw [mul_div_cancel₀ _ hz₁0]; exact hz₂`.

Establish `e : T.toUntilt ξ (T.teichInt hz₂) = T.toUntilt ξ (T.teichInt hz₁) * T.toUntilt ξ (T.teichInt hw)`. Rewrite using `[← T.toUntilt_teich_mul hz₁ hw hzz]`. Use `congr 2`. Conclude with `(mul_div_cancel₀ _ hz₁0).symm`. Rewrite using `[e, show T.toUntilt ξ (T.teichInt hz₁) * u₁ + T.toUntilt ξ (T.teichInt hz₁) * T.toUntilt ξ (T.teichInt hw) * u₂ = T.toUntilt ξ (T.teichInt hz₁) * (u₁ + T.toUntilt ξ (T.teichInt hw) * u₂) by ring, untiltNorm_mul, T.untiltNorm_teich hξ hz₁]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (T.untiltNorm_le_one hξ _)`.
-/
theorem untiltNorm_add_le (q₁ q₂ : T.Untilt ξ) :
    T.untiltNorm hξ (q₁ + q₂) ≤ max (T.untiltNorm hξ q₁) (T.untiltNorm hξ q₂) := by
  wlog hle : T.untiltNorm hξ q₂ ≤ T.untiltNorm hξ q₁ generalizing q₁ q₂
  · rw [add_comm, max_comm]; exact this q₂ q₁ (le_of_not_ge hle)
  by_cases h₁ : q₁ = 0
  · rw [h₁, untiltNorm_zero] at hle ⊢
    have := le_antisymm hle (T.untiltNorm_nonneg hξ q₂)
    rw [(T.untiltNorm_eq_zero_iff hξ).1 this, add_zero, untiltNorm_zero, max_self]
  obtain ⟨z₁, hz₁0, hz₁, u₁, hu₁, rfl⟩ := T.exists_teich_mul_unit hξ h₁
  rw [T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl, max_eq_left (by rwa [T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl] at hle)]
  by_cases h₂ : q₂ = 0
  · rw [h₂, add_zero, T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl]
  obtain ⟨z₂, hz₂0, hz₂, u₂, hu₂, rfl⟩ := T.exists_teich_mul_unit hξ h₂
  rw [T.untiltNorm_eq hξ hz₁0 hz₁ hu₁ rfl, T.untiltNorm_eq hξ hz₂0 hz₂ hu₂ rfl] at hle
  have hw : ‖z₂ / z₁‖ ≤ 1 := by rw [norm_div, div_le_one (norm_pos_iff.2 hz₁0)]; exact hle
  have hzz : ‖z₁ * (z₂ / z₁)‖ ≤ 1 := by rw [mul_div_cancel₀ _ hz₁0]; exact hz₂
  have e : T.toUntilt ξ (T.teichInt hz₂) =
      T.toUntilt ξ (T.teichInt hz₁) * T.toUntilt ξ (T.teichInt hw) := by
    rw [← T.toUntilt_teich_mul hz₁ hw hzz]
    congr 2
    exact (mul_div_cancel₀ _ hz₁0).symm
  rw [e, show T.toUntilt ξ (T.teichInt hz₁) * u₁ +
      T.toUntilt ξ (T.teichInt hz₁) * T.toUntilt ξ (T.teichInt hw) * u₂ =
      T.toUntilt ξ (T.teichInt hz₁) * (u₁ + T.toUntilt ξ (T.teichInt hw) * u₂) by ring,
    untiltNorm_mul, T.untiltNorm_teich hξ hz₁]
  exact mul_le_of_le_one_right (norm_nonneg _) (T.untiltNorm_le_one hξ _)

/- English proof (translation)
Take `⟨Vinv, hVinv⟩` from `(T.isUnit_ξtail hξ).exists_right_inv`. Establish `hVu : IsUnit (T.toUntilt ξ Vinv)` using `isUnit_iff_exists_inv.2 ⟨T.toUntilt ξ (T.ξtail ξ), by rw [← map_mul, mul_comm, hVinv, map_one]⟩`. Establish `hθπ : T.toUntilt ξ T.πInt = T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * (-(T.toUntilt ξ Vinv))`. Rewrite using `[mul_neg, T.toUntilt_teich_coeff_zero hξ, neg_mul, neg_neg, mul_assoc, ← map_mul, hVinv, map_one, mul_one]`. Conclude with `T.untiltNorm_eq hξ hξ.coeff_zero_ne _ hVu.neg hθπ`.
-/
theorem untiltNorm_π : T.untiltNorm hξ (T.toUntilt ξ T.πInt) = ‖T.coeff (ξ : Γ) 0‖ := by
  obtain ⟨Vinv, hVinv⟩ := (T.isUnit_ξtail hξ).exists_right_inv
  have hVu : IsUnit (T.toUntilt ξ Vinv) :=
    isUnit_iff_exists_inv.2 ⟨T.toUntilt ξ (T.ξtail ξ), by rw [← map_mul, mul_comm, hVinv, map_one]⟩
  have hθπ : T.toUntilt ξ T.πInt =
      T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * (-(T.toUntilt ξ Vinv)) := by
    rw [mul_neg, T.toUntilt_teich_coeff_zero hξ, neg_mul, neg_neg, mul_assoc, ← map_mul, hVinv,
      map_one, mul_one]
  exact T.untiltNorm_eq hξ hξ.coeff_zero_ne _ hVu.neg hθπ

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero, T.untiltNorm_unit hξ isUnit_one]`. Consider the case `succ k ih => rw [pow_succ, untiltNorm_mul, ih, pow_succ]`.
-/
theorem untiltNorm_pow (q : T.Untilt ξ) (k : ℕ) :
    T.untiltNorm hξ (q ^ k) = T.untiltNorm hξ q ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, T.untiltNorm_unit hξ isUnit_one]
  | succ k ih => rw [pow_succ, untiltNorm_mul, ih, pow_succ]

include hξ in
/- English proof (translation)
Take `⟨Vinv, hVinv⟩` from `(T.isUnit_ξtail hξ).exists_right_inv`. Establish `hVu : IsUnit (T.toUntilt ξ Vinv)` using `isUnit_iff_exists_inv.2 ⟨T.toUntilt ξ (T.ξtail ξ), by rw [← map_mul, mul_comm, hVinv, map_one]⟩`. Establish `hθπ : T.toUntilt ξ T.πInt = T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * (-(T.toUntilt ξ Vinv))`. Rewrite using `[mul_neg, T.toUntilt_teich_coeff_zero hξ, neg_mul, neg_neg, mul_assoc, ← map_mul, hVinv, map_one, mul_one]`. Use `⟨(-(T.toUntilt ξ Vinv)) ^ k, hVu.neg.pow k, ?_⟩` and prove the remaining obligations.

Rewrite using `[hθπ, mul_pow]`. Use `congr 1`. Rewrite using `[← map_pow]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [SubmonoidClass.coe_pow, coe_teichInt, T.teich_pow]`.
-/
theorem exists_π_pow_teich_unit (k : ℕ) : ∃ w : T.Untilt ξ, IsUnit w ∧
    T.toUntilt ξ T.πInt ^ k =
      T.toUntilt ξ (T.teichInt (show ‖T.coeff (ξ : Γ) 0 ^ k‖ ≤ 1 by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (T.norm_coeff_zero_le ξ))) * w := by
  obtain ⟨Vinv, hVinv⟩ := (T.isUnit_ξtail hξ).exists_right_inv
  have hVu : IsUnit (T.toUntilt ξ Vinv) :=
    isUnit_iff_exists_inv.2 ⟨T.toUntilt ξ (T.ξtail ξ), by rw [← map_mul, mul_comm, hVinv, map_one]⟩
  have hθπ : T.toUntilt ξ T.πInt =
      T.toUntilt ξ (T.teichInt (T.norm_coeff_zero_le ξ)) * (-(T.toUntilt ξ Vinv)) := by
    rw [mul_neg, T.toUntilt_teich_coeff_zero hξ, neg_mul, neg_neg, mul_assoc, ← map_mul, hVinv,
      map_one, mul_one]
  refine ⟨(-(T.toUntilt ξ Vinv)) ^ k, hVu.neg.pow k, ?_⟩
  rw [hθπ, mul_pow]
  congr 1
  rw [← map_pow]
  congr 1
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, coe_teichInt, T.teich_pow]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Distinguish the cases in `hq : q = 0`. Rewrite using `[hq]`. Conclude with `zero_mem _`.

Take `⟨z, hz0, hz, u, hu, rfl⟩` from `T.exists_teich_mul_unit hξ hq`. Rewrite `h` using `[T.untiltNorm_eq hξ hz0 hz hu rfl]`. Take `⟨w, hw, hπw⟩` from `T.exists_π_pow_teich_unit hξ k`. Establish `hξk : T.coeff (ξ : Γ) 0 ^ k ≠ 0` using `pow_ne_zero _ hξ.coeff_zero_ne`. Establish `hd : ‖z / T.coeff (ξ : Γ) 0 ^ k‖ ≤ 1`.

Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hξk), norm_pow]`. Conclude with `h`. Establish `hk1 : ‖T.coeff (ξ : Γ) 0 ^ k‖ ≤ 1`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (T.norm_coeff_zero_le ξ)`.

Establish `hzz : ‖T.coeff (ξ : Γ) 0 ^ k * (z / T.coeff (ξ : Γ) 0 ^ k)‖ ≤ 1`. Rewrite using `[mul_div_cancel₀ _ hξk]`. Conclude with `hz`. Establish `e : T.toUntilt ξ (T.teichInt hz) = T.toUntilt ξ (T.teichInt hk1) * T.toUntilt ξ (T.teichInt hd)`. Rewrite using `[← T.toUntilt_teich_mul hk1 hd hzz]`.

Use `congr 2`. Conclude with `(mul_div_cancel₀ _ hξk).symm`. Use `Ideal.mem_span_singleton'.2 ⟨hw.unit⁻¹ * T.toUntilt ξ (T.teichInt hd) * u, ?_⟩` and prove the remaining obligations. Rewrite using `[hπw, e]`. Establish `: (hw.unit⁻¹ : (T.Untilt ξ)ˣ) * w = 1`.

Conclude with `hw.val_inv_mul`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [this, one_mul]`. Introduce `h`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 h`. Rewrite using `[untiltNorm_mul, untiltNorm_pow, T.untiltNorm_π hξ]`. Conclude with `mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (T.untiltNorm_le_one hξ a)`.
-/
theorem untiltNorm_le_pow_iff {q : T.Untilt ξ} {k : ℕ} :
    T.untiltNorm hξ q ≤ ‖T.coeff (ξ : Γ) 0‖ ^ k ↔ q ∈ Ideal.span {T.toUntilt ξ T.πInt ^ k} := by
  constructor
  · intro h
    by_cases hq : q = 0
    · rw [hq]; exact zero_mem _
    obtain ⟨z, hz0, hz, u, hu, rfl⟩ := T.exists_teich_mul_unit hξ hq
    rw [T.untiltNorm_eq hξ hz0 hz hu rfl] at h
    obtain ⟨w, hw, hπw⟩ := T.exists_π_pow_teich_unit hξ k
    have hξk : T.coeff (ξ : Γ) 0 ^ k ≠ 0 := pow_ne_zero _ hξ.coeff_zero_ne
    have hd : ‖z / T.coeff (ξ : Γ) 0 ^ k‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.2 hξk), norm_pow]; exact h
    have hk1 : ‖T.coeff (ξ : Γ) 0 ^ k‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (T.norm_coeff_zero_le ξ)
    have hzz : ‖T.coeff (ξ : Γ) 0 ^ k * (z / T.coeff (ξ : Γ) 0 ^ k)‖ ≤ 1 := by
      rw [mul_div_cancel₀ _ hξk]; exact hz
    have e : T.toUntilt ξ (T.teichInt hz) =
        T.toUntilt ξ (T.teichInt hk1) * T.toUntilt ξ (T.teichInt hd) := by
      rw [← T.toUntilt_teich_mul hk1 hd hzz]
      congr 2
      exact (mul_div_cancel₀ _ hξk).symm
    refine Ideal.mem_span_singleton'.2 ⟨hw.unit⁻¹ * T.toUntilt ξ (T.teichInt hd) * u, ?_⟩
    rw [hπw, e]
    have : (hw.unit⁻¹ : (T.Untilt ξ)ˣ) * w = 1 := by
      exact hw.val_inv_mul
    calc (↑hw.unit⁻¹ * T.toUntilt ξ (T.teichInt hd) * u) * (T.toUntilt ξ (T.teichInt hk1) * w)
        = (↑hw.unit⁻¹ * w) * (T.toUntilt ξ (T.teichInt hk1) * T.toUntilt ξ (T.teichInt hd) * u) := by
          ring
      _ = _ := by rw [this, one_mul]
  · intro h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
    rw [untiltNorm_mul, untiltNorm_pow, T.untiltNorm_π hξ]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (T.untiltNorm_le_one hξ a)

def UntiltFrac (_hξ : T.IsPrimOne ξ) : Type _ := FractionRing (T.Untilt ξ)

instance : CommRing (T.UntiltFrac hξ) := inferInstanceAs (CommRing (FractionRing (T.Untilt ξ)))

instance : Algebra (T.Untilt ξ) (T.UntiltFrac hξ) :=
  inferInstanceAs (Algebra (T.Untilt ξ) (FractionRing (T.Untilt ξ)))

instance : IsFractionRing (T.Untilt ξ) (T.UntiltFrac hξ) :=
  inferInstanceAs (IsFractionRing (T.Untilt ξ) (FractionRing (T.Untilt ξ)))

noncomputable instance : Field (T.UntiltFrac hξ) := by
  haveI := T.isDomain_untilt hξ
  exact IsFractionRing.toField (T.Untilt ξ)

/- English proof (translation)
Use `haveI := T.isDomain_untilt hξ`. Conclude with `IsFractionRing.injective _ _`.
-/
theorem algebraMap_untiltFrac_injective :
    Function.Injective (algebraMap (T.Untilt ξ) (T.UntiltFrac hξ)) := by
  haveI := T.isDomain_untilt hξ
  exact IsFractionRing.injective _ _

include hξ in
/- English proof (translation)
Use `haveI := T.nontrivial_untilt hξ`. Conclude with `nonZeroDivisors.ne_zero hb`.
-/
theorem ne_zero_of_mem_nonZeroDivisors {b : T.Untilt ξ} (hb : b ∈ nonZeroDivisors (T.Untilt ξ)) :
    b ≠ 0 := by
  haveI := T.nontrivial_untilt hξ
  exact nonZeroDivisors.ne_zero hb

def fracRep (x : T.UntiltFrac hξ) : T.Untilt ξ × nonZeroDivisors (T.Untilt ξ) :=
  Classical.choose (IsLocalization.mk'_surjective (nonZeroDivisors (T.Untilt ξ)) x)

/- English proof (translation)
The claim follows from `Classical.choose_spec (IsLocalization.mk'_surjective (nonZeroDivisors (T.Untilt ξ)) x)`.
-/
theorem fracRep_spec (x : T.UntiltFrac hξ) :
    IsLocalization.mk' (T.UntiltFrac hξ) (T.fracRep hξ x).1 (T.fracRep hξ x).2 = x :=
  Classical.choose_spec (IsLocalization.mk'_surjective (nonZeroDivisors (T.Untilt ξ)) x)

def untiltAbsFun (x : T.UntiltFrac hξ) : ℝ :=
  T.untiltNorm hξ (T.fracRep hξ x).1 / T.untiltNorm hξ ((T.fracRep hξ x).2 : T.Untilt ξ)

/- English proof (translation)
The claim follows from `lt_of_le_of_ne (T.untiltNorm_nonneg hξ b) fun h => T.ne_zero_of_mem_nonZeroDivisors hξ hb ((T.untiltNorm_eq_zero_iff hξ).1 h.symm)`.
-/
theorem untiltNorm_pos_of_nonZeroDivisors {b : T.Untilt ξ} (hb : b ∈ nonZeroDivisors (T.Untilt ξ)) :
    0 < T.untiltNorm hξ b :=
  lt_of_le_of_ne (T.untiltNorm_nonneg hξ b) fun h =>
    T.ne_zero_of_mem_nonZeroDivisors hξ hb ((T.untiltNorm_eq_zero_iff hξ).1 h.symm)

/- English proof (translation)
Establish `hspec` using `T.fracRep_spec hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b)`. Use `set a' := (T.fracRep hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b)).1`. Use `set b' := (T.fracRep hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b)).2`. Rewrite `hspec` using `[IsLocalization.mk'_eq_iff_eq]`. Establish `h` using `T.algebraMap_untiltFrac_injective hξ hspec`.

Establish `hn` using `congrArg (T.untiltNorm hξ) h`. Rewrite `hn` using `[untiltNorm_mul, untiltNorm_mul]`. Establish `hb` using `T.untiltNorm_pos_of_nonZeroDivisors hξ b.2`. Establish `hb'` using `T.untiltNorm_pos_of_nonZeroDivisors hξ b'.2`. Use `show T.untiltNorm hξ a' / T.untiltNorm hξ (b' : T.Untilt ξ) = _`.

Rewrite using `[div_eq_div_iff hb'.ne' hb.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem untiltAbsFun_mk' (a : T.Untilt ξ) (b : nonZeroDivisors (T.Untilt ξ)) :
    T.untiltAbsFun hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b) =
      T.untiltNorm hξ a / T.untiltNorm hξ (b : T.Untilt ξ) := by
  have hspec := T.fracRep_spec hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b)
  set a' := (T.fracRep hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b)).1
  set b' := (T.fracRep hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b)).2
  rw [IsLocalization.mk'_eq_iff_eq] at hspec
  have h := T.algebraMap_untiltFrac_injective hξ hspec
  have hn := congrArg (T.untiltNorm hξ) h
  rw [untiltNorm_mul, untiltNorm_mul] at hn
  have hb := T.untiltNorm_pos_of_nonZeroDivisors hξ b.2
  have hb' := T.untiltNorm_pos_of_nonZeroDivisors hξ b'.2
  show T.untiltNorm hξ a' / T.untiltNorm hξ (b' : T.Untilt ξ) = _
  rw [div_eq_div_iff hb'.ne' hb.ne']
  linarith

def untiltAbs : AbsoluteValue (T.UntiltFrac hξ) ℝ where
  toFun := T.untiltAbsFun hξ
  map_mul' x y := by
    rw [← T.fracRep_spec hξ x, ← T.fracRep_spec hξ y, ← IsLocalization.mk'_mul,
      untiltAbsFun_mk', untiltAbsFun_mk', untiltAbsFun_mk', Submonoid.coe_mul, untiltNorm_mul,
      untiltNorm_mul, mul_div_mul_comm]
  nonneg' x := div_nonneg (T.untiltNorm_nonneg hξ _) (T.untiltNorm_nonneg hξ _)
  eq_zero' x := by
    constructor
    · intro h
      rw [← T.fracRep_spec hξ x]
      have hb := T.untiltNorm_pos_of_nonZeroDivisors hξ (T.fracRep hξ x).2.2
      have : T.untiltNorm hξ (T.fracRep hξ x).1 = 0 := by
        have h' : T.untiltAbsFun hξ x = 0 := h
        rw [untiltAbsFun, div_eq_zero_iff] at h'
        rcases h' with h' | h'
        · exact h'
        · linarith
      rw [(T.untiltNorm_eq_zero_iff hξ).1 this, IsLocalization.mk'_zero]
    · rintro rfl
      show T.untiltAbsFun hξ 0 = 0
      rw [← IsLocalization.mk'_zero (S := T.UntiltFrac hξ) (1 : nonZeroDivisors (T.Untilt ξ)),
        untiltAbsFun_mk', untiltNorm_zero, zero_div]
  add_le' x y := by
    show T.untiltAbsFun hξ (x + y) ≤ T.untiltAbsFun hξ x + T.untiltAbsFun hξ y
    rw [← T.fracRep_spec hξ x, ← T.fracRep_spec hξ y, ← IsLocalization.mk'_add,
      untiltAbsFun_mk', untiltAbsFun_mk', untiltAbsFun_mk']
    set a := (T.fracRep hξ x).1
    set b := (T.fracRep hξ x).2
    set a' := (T.fracRep hξ y).1
    set b' := (T.fracRep hξ y).2
    have hb := T.untiltNorm_pos_of_nonZeroDivisors hξ b.2
    have hb' := T.untiltNorm_pos_of_nonZeroDivisors hξ b'.2
    have ha := T.untiltNorm_nonneg hξ a
    have ha' := T.untiltNorm_nonneg hξ a'
    rw [Submonoid.coe_mul, untiltNorm_mul]
    have h1 := T.untiltNorm_add_le hξ (a * (b' : T.Untilt ξ)) (a' * (b : T.Untilt ξ))
    rw [untiltNorm_mul, untiltNorm_mul] at h1
    rw [div_add_div _ _ hb.ne' hb'.ne', div_le_div_iff_of_pos_right (mul_pos hb hb')]
    refine h1.trans (max_le ?_ ?_)
    · nlinarith [mul_nonneg hb.le ha']
    · nlinarith [mul_nonneg hb'.le ha]

/- English proof (translation)
Use `show T.untiltAbsFun hξ _ = _`. Rewrite using `[← IsLocalization.mk'_one (M := nonZeroDivisors (T.Untilt ξ)), untiltAbsFun_mk', OneMemClass.coe_one, T.untiltNorm_unit hξ isUnit_one, div_one]`.
-/
theorem untiltAbs_algebraMap (q : T.Untilt ξ) :
    T.untiltAbs hξ (algebraMap (T.Untilt ξ) (T.UntiltFrac hξ) q) = T.untiltNorm hξ q := by
  show T.untiltAbsFun hξ _ = _
  rw [← IsLocalization.mk'_one (M := nonZeroDivisors (T.Untilt ξ)), untiltAbsFun_mk',
    OneMemClass.coe_one, T.untiltNorm_unit hξ isUnit_one, div_one]

/- English proof (translation)
Use `show T.untiltAbsFun hξ (x + y) ≤ max (T.untiltAbsFun hξ x) (T.untiltAbsFun hξ y)`. Rewrite using `[← T.fracRep_spec hξ x, ← T.fracRep_spec hξ y, ← IsLocalization.mk'_add, untiltAbsFun_mk', untiltAbsFun_mk', untiltAbsFun_mk']`. Use `set a := (T.fracRep hξ x).1`. Use `set b := (T.fracRep hξ x).2`. Use `set a' := (T.fracRep hξ y).1`.

Use `set b' := (T.fracRep hξ y).2`. Establish `hb` using `T.untiltNorm_pos_of_nonZeroDivisors hξ b.2`. Establish `hb'` using `T.untiltNorm_pos_of_nonZeroDivisors hξ b'.2`. Rewrite using `[Submonoid.coe_mul, untiltNorm_mul]`. Establish `h1` using `T.untiltNorm_add_le hξ (a * (b' : T.Untilt ξ)) (a' * (b : T.Untilt ξ))`.

Rewrite `h1` using `[untiltNorm_mul, untiltNorm_mul]`. Rewrite using `[div_le_iff₀ (mul_pos hb hb')]`. Use `h1.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[max_mul_of_nonneg _ _ (mul_pos hb hb').le]`. Apply the tactic sequence `congr 1 <;> field_simp`.
-/
theorem isNonarchimedean_untiltAbs (x y : T.UntiltFrac hξ) :
    T.untiltAbs hξ (x + y) ≤ max (T.untiltAbs hξ x) (T.untiltAbs hξ y) := by
  show T.untiltAbsFun hξ (x + y) ≤ max (T.untiltAbsFun hξ x) (T.untiltAbsFun hξ y)
  rw [← T.fracRep_spec hξ x, ← T.fracRep_spec hξ y, ← IsLocalization.mk'_add,
    untiltAbsFun_mk', untiltAbsFun_mk', untiltAbsFun_mk']
  set a := (T.fracRep hξ x).1
  set b := (T.fracRep hξ x).2
  set a' := (T.fracRep hξ y).1
  set b' := (T.fracRep hξ y).2
  have hb := T.untiltNorm_pos_of_nonZeroDivisors hξ b.2
  have hb' := T.untiltNorm_pos_of_nonZeroDivisors hξ b'.2
  rw [Submonoid.coe_mul, untiltNorm_mul]
  have h1 := T.untiltNorm_add_le hξ (a * (b' : T.Untilt ξ)) (a' * (b : T.Untilt ξ))
  rw [untiltNorm_mul, untiltNorm_mul] at h1
  rw [div_le_iff₀ (mul_pos hb hb')]
  refine h1.trans (le_of_eq ?_)
  rw [max_mul_of_nonneg _ _ (mul_pos hb hb').le]
  congr 1 <;> field_simp

/- English proof (translation)
Use `haveI := T.isDomain_untilt hξ`. Rewrite `hx`, the goal using `[← T.fracRep_spec hξ x]`. Use `set a := (T.fracRep hξ x).1`. Use `set b := (T.fracRep hξ x).2`. Establish `hb0` using `T.ne_zero_of_mem_nonZeroDivisors hξ b.2`.

Distinguish the cases in `ha0 : a = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, ha0, IsLocalization.mk'_zero]`. Use `show ∃ q, _ = IsLocalization.mk' (T.UntiltFrac hξ) a b`. Establish `hx' : T.untiltAbsFun hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b) ≤ 1` using `hx`.

Rewrite `hx'` using `[untiltAbsFun_mk', div_le_one (T.untiltNorm_pos_of_nonZeroDivisors hξ b.2)]`. Take `⟨za, hza0, hza, ua, hua, hae⟩` from `T.exists_teich_mul_unit hξ ha0`. Take `⟨zb, hzb0, hzb, ub, hub, hbe⟩` from `T.exists_teich_mul_unit hξ hb0`. Rewrite `hx'` using `[hae, hbe, T.untiltNorm_eq hξ hza0 hza hua rfl, T.untiltNorm_eq hξ hzb0 hzb hub rfl]`. Establish `hd : ‖za / zb‖ ≤ 1` using `by rw [norm_div, div_le_one (norm_pos_iff.2 hzb0)]; exact hx'`.

Establish `hzz : ‖zb * (za / zb)‖ ≤ 1` using `by rw [mul_div_cancel₀ _ hzb0]; exact hza`. Use `⟨T.toUntilt ξ (T.teichInt hd) * ua * hub.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]`. Use `congr 1`. Rewrite using `[hae, hbe]`.

Establish `e : T.toUntilt ξ (T.teichInt hza) = T.toUntilt ξ (T.teichInt hzb) * T.toUntilt ξ (T.teichInt hd)`. Rewrite using `[← T.toUntilt_teich_mul hzb hd hzz]`. Use `congr 2`. Conclude with `(mul_div_cancel₀ _ hzb0).symm`. Rewrite using `[e]`.

Establish `: (hub.unit⁻¹ : (T.Untilt ξ)ˣ) * ub = 1` using `hub.val_inv_mul`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [this, one_mul]`.
-/
theorem mem_range_of_untiltAbs_le_one {x : T.UntiltFrac hξ} (hx : T.untiltAbs hξ x ≤ 1) :
    ∃ q : T.Untilt ξ, algebraMap (T.Untilt ξ) (T.UntiltFrac hξ) q = x := by
  haveI := T.isDomain_untilt hξ
  rw [← T.fracRep_spec hξ x] at hx ⊢
  set a := (T.fracRep hξ x).1
  set b := (T.fracRep hξ x).2
  have hb0 := T.ne_zero_of_mem_nonZeroDivisors hξ b.2
  by_cases ha0 : a = 0
  · refine ⟨0, ?_⟩; rw [map_zero, ha0, IsLocalization.mk'_zero]
  show ∃ q, _ = IsLocalization.mk' (T.UntiltFrac hξ) a b
  have hx' : T.untiltAbsFun hξ (IsLocalization.mk' (T.UntiltFrac hξ) a b) ≤ 1 := hx
  rw [untiltAbsFun_mk', div_le_one (T.untiltNorm_pos_of_nonZeroDivisors hξ b.2)] at hx'
  obtain ⟨za, hza0, hza, ua, hua, hae⟩ := T.exists_teich_mul_unit hξ ha0
  obtain ⟨zb, hzb0, hzb, ub, hub, hbe⟩ := T.exists_teich_mul_unit hξ hb0
  rw [hae, hbe, T.untiltNorm_eq hξ hza0 hza hua rfl, T.untiltNorm_eq hξ hzb0 hzb hub rfl] at hx'
  have hd : ‖za / zb‖ ≤ 1 := by rw [norm_div, div_le_one (norm_pos_iff.2 hzb0)]; exact hx'
  have hzz : ‖zb * (za / zb)‖ ≤ 1 := by rw [mul_div_cancel₀ _ hzb0]; exact hza
  refine ⟨T.toUntilt ξ (T.teichInt hd) * ua * hub.unit⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]
  congr 1
  rw [hae, hbe]
  have e : T.toUntilt ξ (T.teichInt hza) =
      T.toUntilt ξ (T.teichInt hzb) * T.toUntilt ξ (T.teichInt hd) := by
    rw [← T.toUntilt_teich_mul hzb hd hzz]
    congr 2
    exact (mul_div_cancel₀ _ hzb0).symm
  rw [e]
  have : (hub.unit⁻¹ : (T.Untilt ξ)ˣ) * ub = 1 := hub.val_inv_mul
  calc T.toUntilt ξ (T.teichInt hd) * ua * ↑hub.unit⁻¹ * (T.toUntilt ξ (T.teichInt hzb) * ub)
      = (↑hub.unit⁻¹ * ub) * (T.toUntilt ξ (T.teichInt hzb) * T.toUntilt ξ (T.teichInt hd) * ua) := by
        ring
    _ = _ := by rw [this, one_mul]

abbrev UntiltField := WithAbs (T.untiltAbs hξ)

def toUntiltField : T.Untilt ξ →+* T.UntiltField hξ :=
  (WithAbs.equiv (T.untiltAbs hξ)).symm.toRingHom.comp (algebraMap (T.Untilt ξ) (T.UntiltFrac hξ))

/- English proof (translation)
The claim follows from `T.untiltAbs_algebraMap hξ q`.
-/
theorem norm_toUntiltField (q : T.Untilt ξ) : ‖T.toUntiltField hξ q‖ = T.untiltNorm hξ q :=
  T.untiltAbs_algebraMap hξ q

/- English proof (translation)
The claim follows from `T.isNonarchimedean_untiltAbs hξ (WithAbs.ofAbs x) (WithAbs.ofAbs y)`.
-/
theorem norm_untiltField_add_le (x y : T.UntiltField hξ) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  T.isNonarchimedean_untiltAbs hξ (WithAbs.ofAbs x) (WithAbs.ofAbs y)

/- English proof (translation)
Take `⟨q, hq⟩` from `T.mem_range_of_untiltAbs_le_one hξ (x := WithAbs.ofAbs x) hx`. Conclude with `⟨q, by rw [toUntiltField, RingHom.comp_apply, hq]; rfl⟩`.
-/
theorem exists_toUntiltField_eq {x : T.UntiltField hξ} (hx : ‖x‖ ≤ 1) :
    ∃ q : T.Untilt ξ, T.toUntiltField hξ q = x := by
  obtain ⟨q, hq⟩ := T.mem_range_of_untiltAbs_le_one hξ (x := WithAbs.ofAbs x) hx
  exact ⟨q, by rw [toUntiltField, RingHom.comp_apply, hq]; rfl⟩

instance completeSpace_untiltField : CompleteSpace (T.UntiltField hξ) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  set r := ‖T.coeff (ξ : Γ) 0‖ with hrdef
  have hr0 : 0 < r := norm_pos_iff.2 hξ.coeff_zero_ne
  have hr1 : r < 1 := hξ.norm_coeff_zero_lt
  set πC : T.UntiltField hξ := T.toUntiltField hξ (T.toUntilt ξ T.πInt)
  have hπC : ‖πC‖ = r := by rw [norm_toUntiltField, T.untiltNorm_π hξ]
  have hπC0 : πC ≠ 0 := by
    intro h; rw [h, norm_zero] at hπC; linarith

  obtain ⟨R, hR0, hR⟩ := cauchySeq_bdd hu
  set M := max (‖u 0‖ + R) 1
  have hM : ∀ n, ‖u n‖ ≤ M := fun n => by
    have h1 : ‖u n‖ ≤ ‖u n - u 0‖ + ‖u 0‖ := by
      have := norm_add_le (u n - u 0) (u 0); rwa [sub_add_cancel] at this
    have h2 : ‖u n - u 0‖ < R := by rw [← dist_eq_norm]; exact hR n 0
    exact (h1.trans (by linarith)).trans (le_max_left _ _)
  have hM1 : 1 ≤ M := le_max_right _ _
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le hM1)) hr1
  set y : ℕ → T.UntiltField hξ := fun n => πC ^ K * u n
  have hy1 : ∀ n, ‖y n‖ ≤ 1 := fun n => by
    simp only [y, norm_mul, norm_pow, hπC]
    calc r ^ K * ‖u n‖ ≤ r ^ K * M := mul_le_mul_of_nonneg_left (hM n) (pow_nonneg hr0.le _)
      _ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_right hK.le (by linarith)
      _ = 1 := inv_mul_cancel₀ (by linarith)
  choose w hw using fun n => T.exists_toUntiltField_eq hξ (hy1 n)
  have hyc : CauchySeq y := by
    have h := (uniformContinuous_const_smul (πC ^ K) :
      UniformContinuous fun x : T.UntiltField hξ => (πC ^ K) • x).comp_cauchySeq hu
    simpa [y, smul_eq_mul, Function.comp_def] using h
  obtain ⟨φ, hφ, hφV⟩ := hyc.subseq_mem (V := fun n => {p | dist p.1 p.2 < r ^ n})
    fun n => Metric.dist_mem_uniformity (pow_pos hr0 n)
  have hstep : ∀ n, w (φ (n + 1)) - w (φ n) ∈ Ideal.span {T.toUntilt ξ T.πInt ^ n} := by
    intro n
    rw [← T.untiltNorm_le_pow_iff hξ, ← norm_toUntiltField, map_sub, hw, hw, ← dist_eq_norm]
    exact (hφV n).le
  obtain ⟨q', hq'⟩ := T.exists_untilt_limit (fun n => w (φ n)) hstep
  have hlim : Tendsto (fun n => y (φ n)) atTop (𝓝 (T.toUntiltField hξ q')) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
    rw [← hw, ← map_sub, norm_toUntiltField, ← neg_sub]
    have : T.untiltNorm hξ (-(q' - w (φ n))) = T.untiltNorm hξ (q' - w (φ n)) := by
      rw [neg_eq_neg_one_mul, untiltNorm_mul, T.untiltNorm_unit hξ isUnit_one.neg, one_mul]
    rw [this]
    exact (T.untiltNorm_le_pow_iff hξ).2 (hq' n)
  refine ⟨(πC ^ K)⁻¹ * T.toUntiltField hξ q', tendsto_nhds_of_cauchySeq_of_subseq hu
    hφ.tendsto_atTop ?_⟩
  have := hlim.const_mul (πC ^ K)⁻¹
  refine this.congr fun n => ?_
  simp only [y, Function.comp_apply, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero K hπC0), one_mul]

def ptElt {c : L} (hc : ‖c‖ ≤ 1) : T.int := ⟨T.π - T.teich c, sub_mem T.π_mem_int (T.teich_mem_int hc)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_ptElt {c : L} (hc : ‖c‖ ≤ 1) : (T.ptElt hc : Γ) = T.π - T.teich c := rfl

/- English proof (translation)
Rewrite using `[coeff_zero, coe_ptElt, map_sub, red_π, red_teich, zero_sub, neg_ne_zero]`. Conclude with `hc0`. Use `norm_coeff_zero_lt := by`. Rewrite using `[coeff_zero, coe_ptElt, map_sub, red_π, red_teich, zero_sub, norm_neg]`. Conclude with `hc1`.

Use `norm_coeff_one := by`. Rewrite using `[coe_ptElt]`. Use `set D := T.π - T.teich c with hDdef`. Establish `hDint : D ∈ T.int` using `(T.ptElt hc1.le).2`. Establish `hH : T.PrefixLe (T.teich c + T.teich (-c)) 1 ‖c‖`.

Establish `h` using `T.prefixLe_teich_add_sub_of_le (a := c) (e := -c) (B := ‖c‖) (δ := ‖c‖) le_rfl (by rw [norm_neg]) (norm_nonneg _) le_rfl 1`. Rewrite `h` using `[add_neg_cancel, T.teich_zero, ← Real.rpow_add' (norm_nonneg c) (by simp), sub_add_cancel, Real.rpow_one]`. Rewrite using `[← T.prefixLe_neg_iff]`. Simplify `h` using `[sub_eq_add_neg, add_comm]`. Establish `hredD : T.red D = -c` using `by rw [hDdef, map_sub, red_π, red_teich, zero_sub]`.

Establish `hD : D = T.teich (-c) + T.π * T.tail D`. Use `T.eq_teich_add_π_mul_tail D` as an intermediate fact. Rewrite `this` using `[hredD]`. Then use the resulting hypothesis. Establish `hπt : T.π * T.tail D = T.π - (T.teich c + T.teich (-c))`. Establish `e` using `hD`.

Rewrite `e`, the goal using `[hDdef]`. Take the linear combination `-e`. Establish `hc1D : T.coeff D 1 = T.coeff (T.π - (T.teich c + T.teich (-c))) 1`. Rewrite using `[← hπt, coeff_π_mul_succ, coeff_succ]`. Rewrite using `[hc1D]`.

Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[← hc1D]`. Conclude with `(T.mem_int_iff.1 hDint) 1`. Assume the negation of the conclusion as `hlt push_neg at hlt set β := max ‖c‖ ‖T.coeff (T.π - (T.teich c + T.teich (-c))) 1‖`. Establish `hβ : β < 1` using `max_lt hc1 hlt`.

Establish `h1 : T.PrefixLe (T.π - (T.teich c + T.teich (-c))) 1 β`. Introduce `m hm`. Break down `(show m = 0 ∨ m = 1 by omega) with rfl | rfl` into its components or cases. Rewrite using `[← hπt, coeff_π_mul_zero, norm_zero]`. Conclude with `le_max_of_le_left (norm_nonneg _)`.

Conclude with `le_max_right _ _`. Establish `h2` using `T.prefixLe_add h1 (hH.mono (le_max_left _ _))`. Rewrite `h2` using `[sub_add_cancel]`. Establish `h3` using `h2 1 le_rfl`. Establish `h4 : T.coeff T.π 1 = 1`.

Use `T.coeff_π_mul_succ 1 0` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this, coeff_zero, map_one]`. Rewrite `h3` using `[h4, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isPrimOne_ptElt {c : L} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) : T.IsPrimOne (T.ptElt hc1.le) where
  coeff_zero_ne := by
    rw [coeff_zero, coe_ptElt, map_sub, red_π, red_teich, zero_sub, neg_ne_zero]; exact hc0
  norm_coeff_zero_lt := by
    rw [coeff_zero, coe_ptElt, map_sub, red_π, red_teich, zero_sub, norm_neg]; exact hc1
  norm_coeff_one := by
    rw [coe_ptElt]
    set D := T.π - T.teich c with hDdef
    have hDint : D ∈ T.int := (T.ptElt hc1.le).2
    have hH : T.PrefixLe (T.teich c + T.teich (-c)) 1 ‖c‖ := by
      have h := T.prefixLe_teich_add_sub_of_le (a := c) (e := -c) (B := ‖c‖) (δ := ‖c‖) le_rfl
        (by rw [norm_neg]) (norm_nonneg _) le_rfl 1
      rw [add_neg_cancel, T.teich_zero, ← Real.rpow_add' (norm_nonneg c) (by simp), sub_add_cancel,
        Real.rpow_one] at h
      rw [← T.prefixLe_neg_iff]
      simpa [sub_eq_add_neg, add_comm] using h
    have hredD : T.red D = -c := by rw [hDdef, map_sub, red_π, red_teich, zero_sub]
    have hD : D = T.teich (-c) + T.π * T.tail D := by
      have := T.eq_teich_add_π_mul_tail D; rwa [hredD] at this
    have hπt : T.π * T.tail D = T.π - (T.teich c + T.teich (-c)) := by
      have e := hD; rw [hDdef] at e ⊢; linear_combination -e
    have hc1D : T.coeff D 1 = T.coeff (T.π - (T.teich c + T.teich (-c))) 1 := by
      rw [← hπt, coeff_π_mul_succ, coeff_succ]
    rw [hc1D]
    refine le_antisymm ?_ ?_
    · rw [← hc1D]; exact (T.mem_int_iff.1 hDint) 1
    · by_contra hlt
      push_neg at hlt
      set β := max ‖c‖ ‖T.coeff (T.π - (T.teich c + T.teich (-c))) 1‖
      have hβ : β < 1 := max_lt hc1 hlt
      have h1 : T.PrefixLe (T.π - (T.teich c + T.teich (-c))) 1 β := by
        intro m hm
        rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
        · rw [← hπt, coeff_π_mul_zero, norm_zero]; exact le_max_of_le_left (norm_nonneg _)
        · exact le_max_right _ _
      have h2 := T.prefixLe_add h1 (hH.mono (le_max_left _ _))
      rw [sub_add_cancel] at h2
      have h3 := h2 1 le_rfl
      have h4 : T.coeff T.π 1 = 1 := by
        have := T.coeff_π_mul_succ 1 0
        rw [mul_one] at this
        rw [this, coeff_zero, map_one]
      rw [h4, norm_one] at h3
      linarith

end TeichLift

end GroundTheory.PAdicHodge
