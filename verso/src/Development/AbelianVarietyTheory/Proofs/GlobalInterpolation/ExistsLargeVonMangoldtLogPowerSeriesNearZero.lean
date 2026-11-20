import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBoundRight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.NearZeroDeriv

/- English proof (translation)
Establish `hK1 : 1 ≤ K` using `hm.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ).trans hK)`. Set `ι` to `(Σ w : Z, Fin (m w)) ⊕ Fin (K - ∑ w ∈ Z, m w)`. Establish `hc : Fintype.card ι = K`. Simplify using `only [ι, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]`. Rewrite using `[Finset.sum_coe_sort Z m]`.

Use linear arithmetic over natural numbers and integers. Set `e : ι ≃ Fin K` to `Fintype.equivFinOfCardEq hc`. Set `g : ι → ℂ` to `Sum.elim (fun p => f p.1) (fun _ => 0)`. Take `⟨j, h1, h2, h3⟩` from `hT K K (fun i => g (e.symm i)) (e (Sum.inl ⟨⟨ρ, hρ⟩, ⟨0, hm⟩⟩))`. Use `⟨j, h1, by omega, ?_⟩` and prove the remaining obligations.

Establish `hj : j ≠ 0` using `by omega`. Establish `es : ∑ i, g (e.symm i) ^ j = ∑ w ∈ Z, (m w : ℂ) * f w ^ j`. Rewrite using `[Equiv.sum_comp e.symm (fun x => g x ^ j), Fintype.sum_sum_type, Fintype.sum_sigma]`. Simplify using `[g, hj, Finset.sum_attach Z (fun w => (m w : ℂ) * f w ^ j)]`. Rewrite `h3` using `[es, Equiv.symm_apply_apply]`.

Use `le_trans ?_ h3` and prove the remaining obligations. Establish `hKp : (0 : ℝ) < K` using `by exact_mod_cast hK1`. Establish `e1 : (K : ℝ) / (C * (K + K)) = 1 / (2 * C)` using `by field_simp; ring`. Rewrite using `[e1, div_eq_mul_one_div, mul_pow, mul_comm]`. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations.

Conclude with `pow_le_pow_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; linarith) (by omega)`.
-/
theorem power_sum_mult {C : ℝ} (hC : 1 ≤ C)
    (hT : ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖)
    (Z : Finset ℂ) (m : ℂ → ℕ) (f : ℂ → ℂ) (K : ℕ) (hK : ∑ w ∈ Z, m w ≤ K) (ρ : ℂ) (hρ : ρ ∈ Z)
    (hm : 1 ≤ m ρ) : ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      (‖f ρ‖ / (2 * C)) ^ j ≤ ‖∑ w ∈ Z, (m w : ℂ) * f w ^ j‖ := by
  have hK1 : 1 ≤ K := hm.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ).trans hK)
  let ι := (Σ w : Z, Fin (m w)) ⊕ Fin (K - ∑ w ∈ Z, m w)
  have hc : Fintype.card ι = K := by
    simp only [ι, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    rw [Finset.sum_coe_sort Z m]; omega
  let e : ι ≃ Fin K := Fintype.equivFinOfCardEq hc
  let g : ι → ℂ := Sum.elim (fun p => f p.1) (fun _ => 0)
  obtain ⟨j, h1, h2, h3⟩ := hT K K (fun i => g (e.symm i)) (e (Sum.inl ⟨⟨ρ, hρ⟩, ⟨0, hm⟩⟩))
  refine ⟨j, h1, by omega, ?_⟩
  have hj : j ≠ 0 := by omega
  have es : ∑ i, g (e.symm i) ^ j = ∑ w ∈ Z, (m w : ℂ) * f w ^ j := by
    rw [Equiv.sum_comp e.symm (fun x => g x ^ j), Fintype.sum_sum_type, Fintype.sum_sigma]
    simp [g, hj, Finset.sum_attach Z (fun w => (m w : ℂ) * f w ^ j)]
  rw [es, Equiv.symm_apply_apply] at h3
  refine le_trans ?_ h3
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK1
  have e1 : (K : ℝ) / (C * (K + K)) = 1 / (2 * C) := by field_simp; ring
  rw [e1, div_eq_mul_one_div, mul_pow, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    (by omega)

/- English proof (translation)
Use `set D := 8 * C * r with hD`. Establish `hDp : 0 < D` using `by positivity`. Establish `hB' : D ^ 2 * ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 ≤ K / 4`. Combine the equalities or inequalities in the displayed calculation. Establish `hsub : ∀ (p : ℂ → Prop) [DecidablePred p], ∑ w ∈ Z.filter p, (m w : ℝ) / ‖s - w‖ ^ 2 ≤ ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2` using `fun p _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)`.

Establish `hcount : ∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), m w ≤ K`. Establish `: ((∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), m w : ℕ) : ℝ) ≤ K`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations.

Rewrite `hw` using `[Finset.mem_filter]`. Establish `h0 : 0 < ‖s - w‖` using `norm_pos_iff.2 (hs w hw.1)`. Rewrite using `[mul_div_assoc', le_div_iff₀ (by positivity), mul_comm (D ^ 2)]`. Use `gcongr`. Conclude with `hw.2`.

Use `_ ≤ D ^ 2 * ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 := by`. Rewrite using `[← Finset.mul_sum]`. Use `gcongr`. Conclude with `Finset.filter_subset _ _`. Use `_ ≤ K := by have : (0 : ℝ) ≤ K := by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Establish `hρ' : ρ ∈ Z.filter (fun w => ‖s - w‖ ≤ D)` using `Finset.mem_filter.2 ⟨hρ, hd.trans (by rw [hD]; nlinarith)⟩`. Establish `hK1 : 1 ≤ K` using `hm.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ').trans hcount)`. Take `⟨j, h1, h2, h3⟩` from `power_sum_mult hC hT _ m (fun w => 1 / (s - w)) K hcount ρ hρ' hm`.

Use `⟨j, h1, h2, ?_⟩` and prove the remaining obligations. Establish `h0 : 0 < ‖s - ρ‖` using `norm_pos_iff.2 (hs ρ hρ)`. Establish `h4 : (1 / (4 * C * r)) ^ j ≤ ‖∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ j‖`. Simplify using `only [one_div_pow, mul_one_div] at h3`. Use `le_trans (pow_le_pow_left₀ (by positivity) ?_ _) h3` and prove the remaining obligations.

Rewrite using `[norm_div, norm_one, div_div]`. Conclude with `one_div_le_one_div_of_le (by positivity) (by nlinarith)`. Take `⟨i, rfl⟩ : ∃ i, j = i + 2` from `⟨j - 2, by omega⟩`. Establish `h5 : ‖∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2)‖ ≤ 1 / 4 * (1 / (4 * C * r)) ^ (i + 2)`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)` and prove the remaining obligations. Rewrite `hw` using `[Finset.mem_filter, not_le]`. Establish `h0 : 0 < ‖s - w‖` using `hDp.trans hw.2`. Establish `e : (1 / D ^ (i + 2)) * (D ^ 2 * ((m w : ℝ) / ‖s - w‖ ^ 2)) = (m w : ℝ) / (D ^ i * ‖s - w‖ ^ 2)` using `by field_simp; ring`. Rewrite using `[e, norm_div, norm_pow, Complex.norm_natCast, pow_add]`.

Use `gcongr`. Conclude with `hw.2.le`. Use `_ ≤ (1 / D ^ (i + 2)) * (K / 4) := by`. Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum]`. Use `gcongr`.

Conclude with `le_trans (mul_le_mul_of_nonneg_left (hsub _) (by positivity)) hB'`. Use `_ ≤ (1 / D ^ (i + 2)) * (2 ^ (i + 2) / 4) := by gcongr`. Establish `: K ≤ 2 ^ (i + 2)` using `le_trans (by omega) (Nat.lt_two_pow_self (n := i + 2)).le`. Conclude with `this` after adjusting the coercions. Use `_ = _ := by`.

Rewrite using `[show D = 2 * (4 * C * r) by rw [hD]; ring, mul_pow, one_div_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Z (fun w => ‖s - w‖ ≤ D)]`. Use `norm_sub_le (∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2) + ∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2)) (∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2))` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem power_sum_large {C : ℝ} (hC : 1 ≤ C)
    (hT : ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖)
    (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (r B : ℝ) (K : ℕ) (hr : 0 < r)
    (hs : ∀ w ∈ Z, s - w ≠ 0)
    (hB : ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 ≤ B / r ^ 2) (hK : 4 * (8 * C) ^ 2 * B ≤ K)
    (ρ : ℂ) (hρ : ρ ∈ Z) (hm : 1 ≤ m ρ) (hd : ‖s - ρ‖ ≤ 2 * r) :
    ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      3 / 4 * (1 / (4 * C * r)) ^ j ≤ ‖∑ w ∈ Z, (m w : ℂ) / (s - w) ^ j‖ := by
  set D := 8 * C * r with hD
  have hDp : 0 < D := by positivity
  have hB' : D ^ 2 * ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 ≤ K / 4 := by
    calc _ ≤ D ^ 2 * (B / r ^ 2) := by gcongr
      _ = (8 * C) ^ 2 * B := by rw [hD]; field_simp
      _ ≤ _ := by linarith
  have hsub : ∀ (p : ℂ → Prop) [DecidablePred p], ∑ w ∈ Z.filter p, (m w : ℝ) / ‖s - w‖ ^ 2
      ≤ ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 := fun p _ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  have hcount : ∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), m w ≤ K := by
    have : ((∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), m w : ℕ) : ℝ) ≤ K := by
      push_cast
      calc _ ≤ ∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), D ^ 2 * ((m w : ℝ) / ‖s - w‖ ^ 2) := by
            refine Finset.sum_le_sum fun w hw => ?_
            rw [Finset.mem_filter] at hw
            have h0 : 0 < ‖s - w‖ := norm_pos_iff.2 (hs w hw.1)
            rw [mul_div_assoc', le_div_iff₀ (by positivity), mul_comm (D ^ 2)]
            gcongr
            exact hw.2
        _ ≤ D ^ 2 * ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 := by
            rw [← Finset.mul_sum]; gcongr; exact Finset.filter_subset _ _
        _ ≤ K := by have : (0 : ℝ) ≤ K := by positivity
                    linarith
    exact_mod_cast this
  have hρ' : ρ ∈ Z.filter (fun w => ‖s - w‖ ≤ D) :=
    Finset.mem_filter.2 ⟨hρ, hd.trans (by rw [hD]; nlinarith)⟩
  have hK1 : 1 ≤ K :=
    hm.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ').trans hcount)
  obtain ⟨j, h1, h2, h3⟩ := power_sum_mult hC hT _ m (fun w => 1 / (s - w)) K hcount ρ hρ' hm
  refine ⟨j, h1, h2, ?_⟩
  have h0 : 0 < ‖s - ρ‖ := norm_pos_iff.2 (hs ρ hρ)
  have h4 : (1 / (4 * C * r)) ^ j ≤
      ‖∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ j‖ := by
    simp only [one_div_pow, mul_one_div] at h3
    refine le_trans (pow_le_pow_left₀ (by positivity) ?_ _) h3
    rw [norm_div, norm_one, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have h5 : ‖∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2)‖
      ≤ 1 / 4 * (1 / (4 * C * r)) ^ (i + 2) := by
    calc _ ≤ ∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D),
            (1 / D ^ (i + 2)) * (D ^ 2 * ((m w : ℝ) / ‖s - w‖ ^ 2)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)
          rw [Finset.mem_filter, not_le] at hw
          have h0 : 0 < ‖s - w‖ := hDp.trans hw.2
          have e : (1 / D ^ (i + 2)) * (D ^ 2 * ((m w : ℝ) / ‖s - w‖ ^ 2))
              = (m w : ℝ) / (D ^ i * ‖s - w‖ ^ 2) := by field_simp; ring
          rw [e, norm_div, norm_pow, Complex.norm_natCast, pow_add]
          gcongr
          exact hw.2.le
      _ ≤ (1 / D ^ (i + 2)) * (K / 4) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          gcongr
          exact le_trans (mul_le_mul_of_nonneg_left (hsub _) (by positivity)) hB'
      _ ≤ (1 / D ^ (i + 2)) * (2 ^ (i + 2) / 4) := by
          gcongr
          have : K ≤ 2 ^ (i + 2) := le_trans (by omega) (Nat.lt_two_pow_self (n := i + 2)).le
          exact_mod_cast this
      _ = _ := by
          rw [show D = 2 * (4 * C * r) by rw [hD]; ring, mul_pow, one_div_pow]
          field_simp
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun w => ‖s - w‖ ≤ D)]
  have := norm_sub_le (∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2) +
    ∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2))
    (∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2))
  rw [add_sub_cancel_right] at this
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `LFunction_ne_zero_of_one_le_re χ hw.2.1 (not_lt.1 h) hw.2.2`.
-/
theorem re_lt_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c w : ℂ} {R : ℝ}
    (hw : w ∈ zerosDisc χ c R) : w.re < 1 := by
  by_contra h
  exact LFunction_ne_zero_of_one_le_re χ hw.2.1 (not_lt.1 h) hw.2.2

/- English proof (translation)
Rewrite using `[div_eq_mul_inv (m : ℂ), ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_eq_norm_sq, mul_div_assoc', mul_div_assoc', mul_comm]`. Use `gcongr`.
-/
theorem inv_sq_le_re {s w : ℂ} {r : ℝ} (m : ℕ) (h : r ≤ (s - w).re) :
    r * ((m : ℝ) / ‖s - w‖ ^ 2) ≤ ((m : ℂ) / (s - w)).re := by
  rw [div_eq_mul_inv (m : ℂ), ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.inv_re,
    Complex.normSq_eq_norm_sq, mul_div_assoc', mul_div_assoc', mul_comm]
  gcongr

/- English proof (translation)
Establish `hsum : Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-σ)`. Use `(LSeriesSummable_vonMangoldt (s := σ) (by simpa using hσ)).norm` as an intermediate fact. Use `this.congr fun n => ?_` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq]`. Use `split_ifs with h`.

Simplify using `[h]`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, Complex.ofReal_re, Real.rpow_neg (by positivity), div_eq_mul_inv]`. Establish `e : derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) 0 (σ + (0 : ℝ) * I) = ((∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)`. Rewrite using `[derSeries, Complex.ofReal_tsum]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[MulChar.one_apply (isUnit_of_subsingleton _), Complex.ofReal_mul, Complex.ofReal_cpow (by positivity)]`. Simplify using the standard rewrite rules. Rewrite using `[e, Complex.ofReal_re, derSeries]`. Use `tsum_of_norm_bounded hsum.hasSum fun n => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]`. Establish `h1 : (-((σ : ℂ) + t * I)).re = -σ` using `by simp`. Rewrite using `[h1]`. Use `hc n` as an intermediate fact.

Establish `h2 : (0 : ℝ) ≤ Λ n` using `vonMangoldt_nonneg`. Simplify using `only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, norm_one, mul_one]`. Use `gcongr`. Conclude with `mul_le_of_le_one_right h2 this`.
-/
theorem norm_derSeries_zero_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (σ t : ℝ) (hσ : 1 < σ) :
    ‖derSeries c 0 (σ + t * I)‖ ≤
      (derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) 0 (σ + (0 : ℝ) * I)).re := by
  have hsum : Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-σ) := by
    have := (LSeriesSummable_vonMangoldt (s := σ) (by simpa using hσ)).norm
    refine this.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · simp [h]
    · rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, Complex.ofReal_re,
        Real.rpow_neg (by positivity), div_eq_mul_inv]
  have e : derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) 0 (σ + (0 : ℝ) * I)
      = ((∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [derSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [MulChar.one_apply (isUnit_of_subsingleton _), Complex.ofReal_mul,
      Complex.ofReal_cpow (by positivity)]
    simp
  rw [e, Complex.ofReal_re, derSeries]
  refine tsum_of_norm_bounded hsum.hasSum fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    have h1 : (-((σ : ℂ) + t * I)).re = -σ := by simp
    rw [h1]
    have := hc n
    have h2 : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, norm_one, mul_one]
    gcongr
    exact mul_le_of_le_one_right h2 this

/- English proof (translation)
Take `⟨C₁, hC₁, H⟩` from `GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros`. Take `⟨T, hT1, hT⟩` from `GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients`. Use `⟨8 * T, 4 * (8 * T) ^ 2 * (2 * C₁ + 2), 1 / (8 * T), by linarith, by positivity, by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ τ r L K ρ hχ hL hLr hr0 hK hρ hd`. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast NeZero.one_le`.

Establish `hlog : 0 < Real.log (q * (|τ| + 2))` using `Real.log_pos (by nlinarith [abs_nonneg τ])`. Establish `hLp : 0 < L` using `hlog.trans_le hL`. Establish `hr : 0 < r` using `lt_of_lt_of_le (by positivity) hLr`. Establish `hTr : 8 * T * r ≤ 1`. Rewrite using `[le_div_iff₀ (by positivity)] at hr0; linarith`.

Establish `hr8 : r ≤ 1 / 8` using `by nlinarith`. Establish `hrL : 1 ≤ r * L` using `by rwa [div_le_iff₀ hLp] at hLr`. Establish `hL1 : 1 ≤ L` using `by nlinarith`. Establish `hrL' : 1 / r ≤ L` using `by rw [div_le_iff₀ hr]; linarith`. Use `set s : ℂ := ((1 + r : ℝ) : ℂ) + τ * I with hs`.

Establish `hfin` using `(H q χ (1 + r) τ 0 (by linarith) (by linarith)).1`. Use `set Z := hfin.toFinset with hZ`. Establish `hre : ∀ w ∈ Z, r ≤ (s - w).re` using `fun w hw => by`. Use `re_lt_one ((Set.Finite.mem_toFinset _).1 hw)` as an intermediate fact. Simplify using `[hs]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : ∀ w ∈ Z, s - w ≠ 0` using `fun w hw h => by`. Use `hre w hw` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ∀ k : ℕ, ‖∑ w ∈ Z, (ord χ w : ℂ) / (s - w) ^ (k + 1)‖ ≤ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k s‖ + (1 + C₁) * L` using `fun k => by`. Establish `h` using `(H q χ (1 + r) τ k (by linarith) (by linarith)).2.2`. Rewrite `h` using `[finsum_mem_eq_finite_toFinset_sum _ hfin, ← hs, ← hZ]`. Establish `h1 : C₁ * Real.log (q * (|τ| + 2)) / (1 + r) ^ k ≤ C₁ * L` using `(div_le_self (by positivity) (one_le_pow₀ (by linarith))).trans (by gcongr)`.

Establish `h2 : ‖(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0 : ℂ)‖ ≤ 1` using `by split_ifs with h1`. Establish `h3 : 2 ≤ |τ|` using `hχ.resolve_left (not_not.2 h1)`. Establish `h4 : |τ| ≤ ‖s - 1‖` using `by simpa [hs] using Complex.abs_im_le_norm (s - 1)`. Rewrite using `[norm_div, norm_one, norm_pow]`. Conclude with `div_le_one_of_le₀ (one_le_pow₀ (by linarith)) (by positivity)`.

Simplify using the standard rewrite rules. Generalize the expression as in `(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0 : ℂ) = P at h h2`. Generalize the expression as in `(∑ w ∈ Z, (ord χ w : ℂ) / (s - w) ^ (k + 1)) = S at h ⊢`. Generalize the expression as in `derSeries (fun n : ℕ => χ (n : ZMod q)) k s = D at h ⊢`. Establish `e : S = (D - P + S) - D + P` using `by ring`.

Use `norm_add_le ((D - P + S) - D) P` as an intermediate fact. Use `norm_sub_le (D - P + S) D` as an intermediate fact. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hD0 : ‖derSeries (fun n : ℕ => χ (n : ZMod q)) 0 s‖ ≤ 1 / r + C₁`.

Use `(norm_derSeries_zero_le _ (fun n => χ.norm_le_one _) (1 + r) τ (by linarith)).trans ?_` and prove the remaining obligations. Take `⟨hf, -, h⟩` from `H 1 1 (1 + r) 0 0 (by linarith) (by linarith)`. Rewrite `h` using `[finsum_mem_eq_finite_toFinset_sum _ hf, if_pos rfl]`. Establish `h1` using `(Complex.re_le_norm _).trans h`. Rewrite `h1` using `[Complex.add_re, Complex.sub_re, Complex.re_sum]`.

Establish `h2 : 0 ≤ ∑ w ∈ hf.toFinset, ((ord (1 : DirichletCharacter ℂ 1) w : ℂ) / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - w) ^ (0 + 1)).re`. Use `Finset.sum_nonneg fun w hw => ?_` and prove the remaining obligations. Use `re_lt_one ((Set.Finite.mem_toFinset _).1 hw)` as an intermediate fact. Rewrite using `[zero_add, pow_one]`. Use `le_trans (by simp) (inv_sq_le_re (r := 0) _ ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (1 / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1)).re = 1 / r`. Establish `: (1 / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1)) = ((1 / r : ℝ) : ℂ)`. Simplify using the standard rewrite rules.

Rewrite using `[this, Complex.ofReal_re]`. Establish `h4 : C₁ * Real.log (((1 : ℕ) : ℝ) * (|(0 : ℝ)| + 2)) / (1 + r) ^ 0 ≤ C₁`. Use `Real.log_two_lt_d9` as an intermediate fact. Simplify using `only [Nat.cast_one, abs_zero, zero_add, one_mul, pow_zero, div_one]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : ∑ w ∈ Z, (ord χ w : ℝ) / ‖s - w‖ ^ 2 ≤ (2 * C₁ + 2) * r * L / r ^ 2`. Establish `h1 : r * ∑ w ∈ Z, (ord χ w : ℝ) / ‖s - w‖ ^ 2 ≤ (2 * C₁ + 2) * L`. Establish `h` using `key 0`. Simplify using `only [zero_add, pow_one] at h`.

Establish `h2` using `(Complex.re_le_norm _).trans h`. Rewrite `h2` using `[Complex.re_sum]`. Rewrite using `[Finset.mul_sum]`. Use `(Finset.sum_le_sum fun w hw => inv_sq_le_re _ (hre w hw)).trans (h2.trans ?_)` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[le_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hρ1 : ρ ≠ 1`. Introduce and unpack `rfl`. Break down `hχ with h | h` into its components or cases.

Conclude with `LFunction_apply_one_ne_zero h hρ`. Establish `: |τ| ≤ r` using `by simpa using hd`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρZ : ρ ∈ Z`. Use `(Set.Finite.mem_toFinset _).2 ⟨?_, Or.inr hρ1, hρ⟩` and prove the remaining obligations.

Establish `e : ρ - (2 + τ * I) = (ρ - (1 + τ * I)) - 1` using `by ring`. Use `norm_sub_le (ρ - (1 + τ * I)) 1` as an intermediate fact. Rewrite using `[e]`. Rewrite `this` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hd' : ‖s - ρ‖ ≤ 2 * r`. Establish `e : s - ρ = (r : ℂ) - (ρ - (1 + τ * I))` using `by rw [hs]; push_cast; ring`. Use `norm_sub_le (r : ℂ) (ρ - (1 + τ * I))` as an intermediate fact. Rewrite `this` using `[Complex.norm_real, Real.norm_of_nonneg hr.le]`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨j, h1, h2, h3⟩` from `power_sum_large hT1 hT Z (ord χ) s r _ K hr hne hB (by linarith) ρ hρZ (GlobalTheory.GoodHeight.one_le_order χ hρ1 hρ) hd'`. Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`. Use `⟨k, by omega, by omega, ?_⟩` and prove the remaining obligations. Establish `h4` using `key k`.

Use `set x := 1 / (4 * T * r) with hx`. Establish `hx2 : 2 ≤ x` using `by rw [hx, le_div_iff₀ (by positivity)]; linarith`. Establish `h5 : (1 + C₁) * L ≤ 1 / 4 * x ^ (k + 1)`. Establish `a : (K : ℝ) ≤ x ^ k`. Establish `: K ≤ 2 ^ k` using `le_trans (by omega) (Nat.lt_two_pow_self (n := k)).le`.

Establish `: (K : ℝ) ≤ 2 ^ k` using `by exact_mod_cast this`. Conclude with `this.trans (by gcongr)`. Establish `b : 4 * (8 * T) ^ 2 * (2 * C₁ + 2) * r * L * x = 128 * T * ((1 + C₁) * L)`. Rewrite using `[hx]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `c : 4 * (8 * T) ^ 2 * (2 * C₁ + 2) * r * L * x ≤ x ^ k * x` using `mul_le_mul_of_nonneg_right (hK.trans a) (by linarith)`. Establish `d : 0 ≤ (1 + C₁) * L` using `by positivity`. Rewrite using `[pow_succ]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h6 : 1 / (8 * T * r) ^ (k + 1) ≤ 1 / 2 * x ^ (k + 1)`. Establish `e : 1 / (8 * T * r) = 1 / 2 * x` using `by rw [hx]; field_simp; ring`. Rewrite using `[← one_div_pow, e, mul_pow]`. Use `gcongr`. Conclude with `pow_le_of_le_one (by norm_num) (by norm_num) (by omega)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_large_derSeries : ∃ A C r₀ : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) → Real.log (q * (|τ| + 2)) ≤ L → 1 / L ≤ r → r ≤ r₀ → C * r * L ≤ K → LFunction χ ρ = 0 → ‖ρ - (1 + τ * I)‖ ≤ r → ∃ k : ℕ, K ≤ k ∧ k ≤ 2 * K ∧ 1 / (A * r) ^ (k + 1) ≤ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k ((1 + r : ℝ) + τ * I)‖ := by
  obtain ⟨C₁, hC₁, H⟩ := GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros
  obtain ⟨T, hT1, hT⟩ := GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients
  refine ⟨8 * T, 4 * (8 * T) ^ 2 * (2 * C₁ + 2), 1 / (8 * T), by linarith, by positivity,
    by positivity, ?_⟩
  intro q _ χ τ r L K ρ hχ hL hLr hr0 hK hρ hd
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hlog : 0 < Real.log (q * (|τ| + 2)) := Real.log_pos (by nlinarith [abs_nonneg τ])
  have hLp : 0 < L := hlog.trans_le hL
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hLr
  have hTr : 8 * T * r ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hr0; linarith
  have hr8 : r ≤ 1 / 8 := by nlinarith
  have hrL : 1 ≤ r * L := by rwa [div_le_iff₀ hLp] at hLr
  have hL1 : 1 ≤ L := by nlinarith
  have hrL' : 1 / r ≤ L := by rw [div_le_iff₀ hr]; linarith
  set s : ℂ := ((1 + r : ℝ) : ℂ) + τ * I with hs
  have hfin := (H q χ (1 + r) τ 0 (by linarith) (by linarith)).1
  set Z := hfin.toFinset with hZ
  have hre : ∀ w ∈ Z, r ≤ (s - w).re := fun w hw => by
    have := re_lt_one ((Set.Finite.mem_toFinset _).1 hw)
    simp [hs]; linarith
  have hne : ∀ w ∈ Z, s - w ≠ 0 := fun w hw h => by
    have := hre w hw
    rw [h] at this; simp at this; linarith
  have key : ∀ k : ℕ, ‖∑ w ∈ Z, (ord χ w : ℂ) / (s - w) ^ (k + 1)‖ ≤
      ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k s‖ + (1 + C₁) * L := fun k => by
    have h := (H q χ (1 + r) τ k (by linarith) (by linarith)).2.2
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← hs, ← hZ] at h
    have h1 : C₁ * Real.log (q * (|τ| + 2)) / (1 + r) ^ k ≤ C₁ * L :=
      (div_le_self (by positivity) (one_le_pow₀ (by linarith))).trans (by gcongr)
    have h2 : ‖(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0 : ℂ)‖ ≤ 1 := by
      split_ifs with h1
      · have h3 : 2 ≤ |τ| := hχ.resolve_left (not_not.2 h1)
        have h4 : |τ| ≤ ‖s - 1‖ := by simpa [hs] using Complex.abs_im_le_norm (s - 1)
        rw [norm_div, norm_one, norm_pow]
        exact div_le_one_of_le₀ (one_le_pow₀ (by linarith)) (by positivity)
      · simp
    generalize (if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0 : ℂ) = P at h h2
    generalize (∑ w ∈ Z, (ord χ w : ℂ) / (s - w) ^ (k + 1)) = S at h ⊢
    generalize derSeries (fun n : ℕ => χ (n : ZMod q)) k s = D at h ⊢
    have e : S = (D - P + S) - D + P := by ring
    have := norm_add_le ((D - P + S) - D) P
    have := norm_sub_le (D - P + S) D
    rw [e]; nlinarith
  have hD0 : ‖derSeries (fun n : ℕ => χ (n : ZMod q)) 0 s‖ ≤ 1 / r + C₁ := by
    refine (norm_derSeries_zero_le _ (fun n => χ.norm_le_one _) (1 + r) τ (by linarith)).trans ?_
    obtain ⟨hf, -, h⟩ := H 1 1 (1 + r) 0 0 (by linarith) (by linarith)
    rw [finsum_mem_eq_finite_toFinset_sum _ hf, if_pos rfl] at h
    have h1 := (Complex.re_le_norm _).trans h
    rw [Complex.add_re, Complex.sub_re, Complex.re_sum] at h1
    have h2 : 0 ≤ ∑ w ∈ hf.toFinset, ((ord (1 : DirichletCharacter ℂ 1) w : ℂ) /
        (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - w) ^ (0 + 1)).re := by
      refine Finset.sum_nonneg fun w hw => ?_
      have := re_lt_one ((Set.Finite.mem_toFinset _).1 hw)
      rw [zero_add, pow_one]
      refine le_trans (by simp) (inv_sq_le_re (r := 0) _ ?_)
      simp; linarith
    have h3 : (1 / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1)).re = 1 / r := by
      have : (1 / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1)) = ((1 / r : ℝ) : ℂ) := by
        simp
      rw [this, Complex.ofReal_re]
    have h4 : C₁ * Real.log (((1 : ℕ) : ℝ) * (|(0 : ℝ)| + 2)) / (1 + r) ^ 0 ≤ C₁ := by
      have := Real.log_two_lt_d9
      simp only [Nat.cast_one, abs_zero, zero_add, one_mul, pow_zero, div_one]
      nlinarith
    linarith
  have hB : ∑ w ∈ Z, (ord χ w : ℝ) / ‖s - w‖ ^ 2 ≤ (2 * C₁ + 2) * r * L / r ^ 2 := by
    have h1 : r * ∑ w ∈ Z, (ord χ w : ℝ) / ‖s - w‖ ^ 2 ≤ (2 * C₁ + 2) * L := by
      have h := key 0
      simp only [zero_add, pow_one] at h
      have h2 := (Complex.re_le_norm _).trans h
      rw [Complex.re_sum] at h2
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun w hw => inv_sq_le_re _ (hre w hw)).trans (h2.trans ?_)
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    rcases hχ with h | h
    · exact LFunction_apply_one_ne_zero h hρ
    · have : |τ| ≤ r := by simpa using hd
      linarith
  have hρZ : ρ ∈ Z := by
    refine (Set.Finite.mem_toFinset _).2 ⟨?_, Or.inr hρ1, hρ⟩
    have e : ρ - (2 + τ * I) = (ρ - (1 + τ * I)) - 1 := by ring
    have := norm_sub_le (ρ - (1 + τ * I)) 1
    rw [e]; rw [norm_one] at this; linarith
  have hd' : ‖s - ρ‖ ≤ 2 * r := by
    have e : s - ρ = (r : ℂ) - (ρ - (1 + τ * I)) := by rw [hs]; push_cast; ring
    have := norm_sub_le (r : ℂ) (ρ - (1 + τ * I))
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at this
    rw [e]; linarith
  obtain ⟨j, h1, h2, h3⟩ := power_sum_large hT1 hT Z (ord χ) s r _ K hr hne hB
    (by linarith) ρ hρZ (GlobalTheory.GoodHeight.one_le_order χ hρ1 hρ) hd'
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  refine ⟨k, by omega, by omega, ?_⟩
  have h4 := key k
  set x := 1 / (4 * T * r) with hx
  have hx2 : 2 ≤ x := by rw [hx, le_div_iff₀ (by positivity)]; linarith
  have h5 : (1 + C₁) * L ≤ 1 / 4 * x ^ (k + 1) := by
    have a : (K : ℝ) ≤ x ^ k := by
      have : K ≤ 2 ^ k := le_trans (by omega) (Nat.lt_two_pow_self (n := k)).le
      have : (K : ℝ) ≤ 2 ^ k := by exact_mod_cast this
      exact this.trans (by gcongr)
    have b : 4 * (8 * T) ^ 2 * (2 * C₁ + 2) * r * L * x = 128 * T * ((1 + C₁) * L) := by
      rw [hx]; field_simp; ring
    have c : 4 * (8 * T) ^ 2 * (2 * C₁ + 2) * r * L * x ≤ x ^ k * x :=
      mul_le_mul_of_nonneg_right (hK.trans a) (by linarith)
    have d : 0 ≤ (1 + C₁) * L := by positivity
    rw [pow_succ]
    nlinarith
  have h6 : 1 / (8 * T * r) ^ (k + 1) ≤ 1 / 2 * x ^ (k + 1) := by
    have e : 1 / (8 * T * r) = 1 / 2 * x := by rw [hx]; field_simp; ring
    rw [← one_div_pow, e, mul_pow]
    gcongr
    exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

end GlobalTheory.NearZeroDeriv
