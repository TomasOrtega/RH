import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSubLeMaxOfUltrametricField

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda.OneTerm

variable {K : Type} [NormedField K]

/- English proof (translation)
Unfold `frobOp`. Rewrite using `[coeff_subst_X_pow (pow_ne_zero _ hq)]`. Simplify using `[coeff_map]`.
-/
theorem coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (i : ℕ) (f : K⟦X⟧) (n : ℕ) :
    coeff n (frobOp τ q i f) = if q ^ i ∣ n then (τ ^ i) (coeff (n / q ^ i) f) else 0 := by
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ hq)]
  simp [coeff_map]

/- English proof (translation)
Rewrite using `[pow_add]`. Both sides reduce to the same expression.
-/
theorem pow_apply_pow (τ : K →+* K) (i k : ℕ) (x : K) : (τ ^ i) ((τ ^ k) x) = (τ ^ (i + k)) x := by
  rw [pow_add]; rfl

/- English proof (translation)
Proceed by induction on `i generalizing x with`. Consider the case `zero => rfl`. Consider the case `succ i ih => rw [← pow_apply_pow, ih, pow_one, hτ]`.
-/
theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) : ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => rw [← pow_apply_pow, ih, pow_one, hτ]

/- English proof (translation)
Rewrite using `[coeff_frobOp τ (by omega)]`. Use `split_ifs with hd`. Establish `hlt : n < q ^ k` using `lt_of_le_of_lt h (Nat.lt_pow_self (by omega))`. Establish `h0 : n = 0` using `Nat.eq_zero_of_dvd_of_lt hd hlt`. Substitute `h0` using the available equality.

Simplify using `[hf]`. Both sides reduce to the same expression.
-/
theorem coeff_frobOp_eq_zero (τ : K →+* K) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    {k n : ℕ} (h : n ≤ k) : coeff n (frobOp τ q k f) = 0 := by
  rw [coeff_frobOp τ (by omega)]
  split_ifs with hd
  · have hlt : n < q ^ k := lt_of_le_of_lt h (Nat.lt_pow_self (by omega))
    have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    subst h0
    simp [hf]
  · rfl

/- English proof (translation)
Rewrite using `[coeff_frobOp τ hq, coeff_frobOp τ hq, pow_add q i k]`. Distinguish the cases in `h : q ^ i * q ^ k ∣ n`. Rewrite using `[if_pos h, if_pos ((Nat.dvd_div_iff_mul_dvd hd).2 h), pow_apply_pow, Nat.div_div_eq_div_mul]`. Rewrite using `[if_neg h, if_neg (fun h' => h ((Nat.dvd_div_iff_mul_dvd hd).1 h')), map_zero]`.
-/
theorem pow_apply_coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (f : K⟦X⟧) (i k : ℕ) {n : ℕ} (hd : q ^ i ∣ n) :
    (τ ^ i) (coeff (n / q ^ i) (frobOp τ q k f)) = coeff n (frobOp τ q (i + k) f) := by
  rw [coeff_frobOp τ hq, coeff_frobOp τ hq, pow_add q i k]
  by_cases h : q ^ i * q ^ k ∣ n
  · rw [if_pos h, if_pos ((Nat.dvd_div_iff_mul_dvd hd).2 h), pow_apply_pow, Nat.div_div_eq_div_mul]
  · rw [if_neg h, if_neg (fun h' => h ((Nat.dvd_div_iff_mul_dvd hd).1 h')), map_zero]

/- English proof (translation)
Establish `hq0 : q ≠ 0` using `by omega`. Rewrite using `[coeff_frobOp τ hq0]`. Distinguish the cases in `hd : q ^ i ∣ n`. Rewrite using `[if_pos hd, coeff_frobOp τ hq0 i f, if_pos hd, map_sub, coeff_C_mul, hondaSum, coeff_mk, ← Finset.eventually_constant_sum (N := n / q ^ i) (n := N) (fun j hj => by rw [coeff_frobOp_eq_zero τ hq hf (by omega), mul_zero]) (le_trans (Nat.div_le_self _ _) hN), map_sub, map_mul, map_n …`. Use `congr 1`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, pow_apply_coeff_frobOp τ hq0 f i (j + 1) hd]`. Rewrite using `[if_neg hd, coeff_frobOp τ hq0 i f, if_neg hd, mul_zero, Finset.sum_eq_zero, sub_zero]`. Introduce `j _`. Rewrite using `[coeff_frobOp τ hq0, if_neg, mul_zero]`.

Conclude with `fun h => hd (dvd_trans (pow_dvd_pow q (Nat.le_add_right _ _)) h)`.
-/
theorem coeff_frobOp_sub_hondaSum (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c : ℕ → K) (i n N : ℕ) (hN : n ≤ N) :
    coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range N, (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
  have hq0 : q ≠ 0 := by omega
  rw [coeff_frobOp τ hq0]
  by_cases hd : q ^ i ∣ n
  · rw [if_pos hd, coeff_frobOp τ hq0 i f, if_pos hd, map_sub, coeff_C_mul, hondaSum, coeff_mk,
      ← Finset.eventually_constant_sum (N := n / q ^ i) (n := N)
        (fun j hj => by rw [coeff_frobOp_eq_zero τ hq hf (by omega), mul_zero])
        (le_trans (Nat.div_le_self _ _) hN),
      map_sub, map_mul, map_natCast, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, pow_apply_coeff_frobOp τ hq0 f i (j + 1) hd]
  · rw [if_neg hd, coeff_frobOp τ hq0 i f, if_neg hd, mul_zero, Finset.sum_eq_zero, sub_zero]
    intro j _
    rw [coeff_frobOp τ hq0, if_neg, mul_zero]
    exact fun h => hd (dvd_trans (pow_dvd_pow q (Nat.le_add_right _ _)) h)

/- English proof (translation)
Rewrite using `[Finset.sum_range_diag_flip]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Finset.eventually_constant_sum (fun j hj => hF i j (by omega)) (Nat.sub_le _ _)`.
-/
theorem sum_square_eq_sum_diag (N : ℕ) (F : ℕ → ℕ → K) (hF : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j =
      ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range (m + 1), F i (m - i) := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.eventually_constant_sum (fun j hj => hF i j (by omega)) (Nat.sub_le _ _)

/- English proof (translation)
Establish `hq0 : q ≠ 0` using `by omega`. Establish `h1 : ∀ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) = (l : K) * t i * coeff n (frobOp τ q i f) - ∑ j ∈ Finset.range (n + 1), t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f)`. Introduce `i _`. Rewrite using `[coeff_frobOp_sub_hondaSum τ l hq hf c i n (n + 1) (Nat.le_succ n), mul_sub, Finset.mul_sum]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_sub_distrib, sum_square_eq_sum_diag (n + 1) (fun i j => t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f)) (fun i j hij => by simp only [coeff_frobOp_eq_zero τ hq hf (show n ≤ i + (j + 1) by omega), mul_zero])]`. Establish `h2 : ∀ m ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i)) * coeff n (frobOp τ q (i + (m - i + 1)) f) = (∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i))) * coeff n (frobOp τ q (m + 1) f)`. Introduce `m _`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `: i + (m - i + 1) = m + 1` using `by have := Finset.mem_range.1 hi; omega`. Rewrite using `[this]`. Rewrite using `[Finset.sum_congr rfl h2, Finset.sum_range_succ', Finset.sum_range_succ _ n, coeff_frobOp_eq_zero τ hq hf (Nat.le_succ n), mul_zero, add_zero, add_sub_right_comm, ← Finset.sum_sub_distrib, Finset.sum_eq_single 0]`.

Establish `h0 : coeff n (frobOp τ q 0 f) = coeff n f`. Rewrite using `[coeff_frobOp τ hq0]`. Simplify using the standard rewrite rules. Rewrite using `[h0, ht0]`. Simplify using `only [zero_add, Finset.sum_range_one, pow_zero, Nat.sub_zero, ht0, RingHom.one_def, RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m _ hm`. Rewrite using `[ht (m + 1) (by omega), Nat.add_sub_cancel, sub_self]`. Introduce `h`. Establish `hn : n = 0` using `by simpa using h`.

Rewrite using `[coeff_frobOp_eq_zero τ hq hf (show n ≤ 0 + 1 by omega), mul_zero, mul_zero, sub_self]`.
-/
theorem coeff_identity (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c t : ℕ → K) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → (l : K) * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n f - (c 0 - l * t 1) * coeff n (frobOp τ q 1 f) := by
  have hq0 : q ≠ 0 := by omega
  have h1 : ∀ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * t i * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range (n + 1), t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
    intro i _
    rw [coeff_frobOp_sub_hondaSum τ l hq hf c i n (n + 1) (Nat.le_succ n), mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_square_eq_sum_diag (n + 1) (fun i j => t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f))
      (fun i j hij => by simp only [coeff_frobOp_eq_zero τ hq hf (show n ≤ i + (j + 1) by omega), mul_zero])]
  have h2 : ∀ m ∈ Finset.range (n + 1),
      ∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i)) * coeff n (frobOp τ q (i + (m - i + 1)) f) =
      (∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i))) * coeff n (frobOp τ q (m + 1) f) := by
    intro m _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i + (m - i + 1) = m + 1 := by have := Finset.mem_range.1 hi; omega
    rw [this]
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ', Finset.sum_range_succ _ n,
    coeff_frobOp_eq_zero τ hq hf (Nat.le_succ n), mul_zero, add_zero, add_sub_right_comm,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
  · have h0 : coeff n (frobOp τ q 0 f) = coeff n f := by
      rw [coeff_frobOp τ hq0]; simp
    rw [h0, ht0]
    simp only [zero_add, Finset.sum_range_one, pow_zero, Nat.sub_zero, ht0, RingHom.one_def, RingHom.id_apply]
    ring
  · intro m _ hm
    rw [ht (m + 1) (by omega), Nat.add_sub_cancel, sub_self]
  · intro h
    have hn : n = 0 := by simpa using h
    rw [coeff_frobOp_eq_zero τ hq hf (show n ≤ 0 + 1 by omega), mul_zero, mul_zero, sub_self]

/- English proof (translation)
Introduce `K _ _ _ _ l q τ hq hl hτ f hf c hc hc0 hg`. Take `⟨t, ht0, ht1, ht⟩` from `GlobalTheory.Honda.exists_twisted_division K τ hτ (l : K) hl c hc0 hc`. Use `⟨c 0 - l * t 1, ?_, fun n => ?_⟩` and prove the remaining obligations. Establish `hlt : ‖-((l : K) * t 1)‖ < ‖c 0‖`. Rewrite using `[norm_neg, norm_mul, hc0]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (ht1 1)) hl`. Rewrite using `[sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hc0]`. Rewrite using `[map_sub, coeff_C_mul, coeff_C_mul, ← coeff_identity τ l hq hf c t ht0 ht n]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use `le_trans (mul_le_of_le_one_left (norm_nonneg _) (ht1 i)) ?_` and prove the remaining obligations. Rewrite using `[coeff_frobOp τ (by omega)]`. Use `split_ifs`. Rewrite using `[norm_pow_apply τ hτ]`. Conclude with `hg _`.

Simplify using the standard rewrite rules.
-/
theorem exists_one_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
    (l q : ℕ) (τ : K →+* K), 2 ≤ q → ‖(l : K)‖ < 1 → (∀ x, ‖τ x‖ = ‖x‖) → ∀ (f : K⟦X⟧), constantCoeff f = 0 →
    ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → ‖c 0‖ = 1 → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum τ q c f) →
    ∃ c' : K, ‖c'‖ = 1 ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - C c' * frobOp τ q 1 f) := by
  intro K _ _ _ _ l q τ hq hl hτ f hf c hc hc0 hg
  obtain ⟨t, ht0, ht1, ht⟩ := GlobalTheory.Honda.exists_twisted_division K τ hτ (l : K) hl c hc0 hc
  refine ⟨c 0 - l * t 1, ?_, fun n => ?_⟩
  · have hlt : ‖-((l : K) * t 1)‖ < ‖c 0‖ := by
      rw [norm_neg, norm_mul, hc0]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (ht1 1)) hl
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hc0]
  · rw [map_sub, coeff_C_mul, coeff_C_mul, ← coeff_identity τ l hq hf c t ht0 ht n]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (ht1 i)) ?_
    rw [coeff_frobOp τ (by omega)]
    split_ifs
    · rw [norm_pow_apply τ hτ]; exact hg _
    · simp

end GlobalTheory.Honda.OneTerm
