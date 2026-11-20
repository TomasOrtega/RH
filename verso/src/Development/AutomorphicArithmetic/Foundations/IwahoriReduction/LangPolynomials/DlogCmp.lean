import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

noncomputable section

open GlobalTheory.Col

namespace UpperTheory.Kd.C7

/- English proof (translation)
Introduce `R _ p hp m n N hm F g w hF hg hw hL`. Take `⟨j, rfl⟩ : ∃ j, m = j + 1` from `⟨m - 1, by omega⟩`. Use `set k := min n (min (j + 1 - 1) N) with hk`. Establish `hkn : k ≤ n` using `by omega`. Establish `hkj : k ≤ j` using `by omega`.

Establish `hkN : k ≤ N` using `by omega`. Use `set D := PowerSeries.derivative R with hD`. Use `set W := w ^ p ^ n with hW`. Set `J : Ideal (PowerSeries R)` to `Ideal.span {(p : PowerSeries R) ^ k, cyc R p (j + 1)}`. Establish `hpow : ∀ i, k ≤ i → ∀ y : PowerSeries R, (p : PowerSeries R) ^ i * y ∈ J`.

Introduce `i hi y`. Establish `e : (p : PowerSeries R) ^ i * y = (p : PowerSeries R) ^ k * ((p : PowerSeries R) ^ (i - k) * y)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi]`. Rewrite using `[e]`. Conclude with `J.mul_mem_right _ (Ideal.subset_span (by simp))`.

Establish `hcyc : ∀ y, cyc R p (j + 1) * y ∈ J` using `fun y => J.mul_mem_right _ (Ideal.subset_span (by simp))`. Establish `hev : ∀ x ∈ J, ev R p (j + 1) x ∈ Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k}`. Introduce `x hx`. Establish `hle : J ≤ (Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k}).comap (ev R p (j + 1))`. Rewrite using `[Ideal.span_le]`.

Introduce `z hz`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz`. Break down `hz with rfl | rfl` into its components or cases. Simplify using `only [SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]`. Conclude with `Ideal.subset_span rfl`.

Simplify using `only [SetLike.mem_coe, Ideal.mem_comap]`. Establish `h0 : ev R p (j + 1) (cyc R p (j + 1)) = 0`. Unfold `ev`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)`. Rewrite using `[h0]`.

Conclude with `Ideal.zero_mem _`. Conclude with `hle hx`. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b : PowerSeries R, F - g * W = (p : PowerSeries R) ^ N * a + cyc R p (j + 1) * b := by`. Unfold `LC at hL`. Rewrite `hL` using `[← map_sub]`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hL`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {cyc R p (j + 1)}) c`. Establish `h0 : ev R p (j + 1) (F - g * W - (p : PowerSeries R) ^ N * a) = 0`. Establish `hea : ev R p (j + 1) a = c`. Unfold `ev`.

Conclude with `ha`. Rewrite using `[map_sub, ← hc, map_mul, map_pow, map_natCast, hea, mul_comm]`. Conclude with `sub_self _`. Unfold `ev at h0`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)`.

Conclude with `⟨a, b, by linear_combination -hb⟩`. Establish `hEJ : F - g * W ∈ J`. Rewrite using `[hab]`. Conclude with `J.add_mem (hpow N hkN a) (hcyc b)`. Establish `hDcyc : D (cyc R p (j + 1)) ∈ J`.

Establish `hc : cyc R p (j + 1) = ∑ i ∈ Finset.range p, (1 + PowerSeries.X) ^ (p ^ j * i)`. Unfold `cyc`. Rewrite using `[Polynomial.cyclotomic_prime_pow_eq_geom_sum hp.out, Polynomial.eval₂_finset_sum]`. Simplify using `only [Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_mul]`. Rewrite using `[hc, map_sum]`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz_pow, map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_assoc]`. Conclude with `hpow j hkj _`. Establish `hDE : D (F - g * W) ∈ J`. Rewrite using `[hab, map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_natCast]`.

Simplify using `only [smul_zero, mul_zero, add_zero, smul_eq_mul]`. Conclude with `J.add_mem (hpow N hkN _) (J.add_mem (hcyc _) (J.mul_mem_left _ hDcyc))`. Establish `hDW : D W ∈ J`. Rewrite using `[hW, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow]`. Conclude with `hpow n hkn _`.

Establish `hdd : ∀ x, dd x = (1 + PowerSeries.X) * D x`. Introduce `x`. Unfold `dd`. Both sides reduce to the same expression. Establish `hFi` using `Ring.mul_inverse_cancel F hF`.

Establish `hgi` using `Ring.mul_inverse_cancel g hg`. Establish `key : dl F - dl g = Ring.inverse F * Ring.inverse g * ((1 + PowerSeries.X) * (D F * g - D g * F))`. Unfold `dl`. Rewrite using `[hdd F, hdd g]`. Take the linear combination `(-(1 + PowerSeries.X) * D F * Ring.inverse F) * hgi + ((1 + PowerSeries.X) * D g * Ring.inverse g) * hFi`.

Establish `hmid : D F * g - D g * F = g * g * D W + g * D (F - g * W) - D g * (F - g * W)`. Establish `hDF : D F = D (F - g * W) + g * D W + W * D g`. Rewrite using `[map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hDF]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `LC`. Rewrite using `[← map_sub]`. Apply `hev` to reduce the goal to its premises. Rewrite using `[key]`.

Use `J.mul_mem_left _ (J.mul_mem_left _ ?_)` and prove the remaining obligations. Rewrite using `[hmid]`. Conclude with `J.sub_mem (J.add_mem (J.mul_mem_left _ hDW) (J.mul_mem_left _ hDE)) (J.mul_mem_left _ hEJ)`.
-/
theorem pDlogCmp : SDlogCmp := by
  intro R _ p hp m n N hm F g w hF hg hw hL
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  set k := min n (min (j + 1 - 1) N) with hk
  have hkn : k ≤ n := by omega
  have hkj : k ≤ j := by omega
  have hkN : k ≤ N := by omega
  set D := PowerSeries.derivative R with hD
  set W := w ^ p ^ n with hW
  let J : Ideal (PowerSeries R) := Ideal.span {(p : PowerSeries R) ^ k, cyc R p (j + 1)}
  have hpow : ∀ i, k ≤ i → ∀ y : PowerSeries R, (p : PowerSeries R) ^ i * y ∈ J := by
    intro i hi y
    have e : (p : PowerSeries R) ^ i * y = (p : PowerSeries R) ^ k * ((p : PowerSeries R) ^ (i - k) * y) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi]
    rw [e]
    exact J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hcyc : ∀ y, cyc R p (j + 1) * y ∈ J := fun y =>
    J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hev : ∀ x ∈ J, ev R p (j + 1) x ∈ Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k} := by
    intro x hx
    have hle : J ≤ (Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k}).comap (ev R p (j + 1)) := by
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
        exact Ideal.subset_span rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap]
        have h0 : ev R p (j + 1) (cyc R p (j + 1)) = 0 := by
          unfold ev
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [h0]
        exact Ideal.zero_mem _
    exact hle hx
  obtain ⟨a, b, hab⟩ : ∃ a b : PowerSeries R,
      F - g * W = (p : PowerSeries R) ^ N * a + cyc R p (j + 1) * b := by
    unfold LC at hL
    rw [← map_sub] at hL
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hL
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {cyc R p (j + 1)}) c
    have h0 : ev R p (j + 1) (F - g * W - (p : PowerSeries R) ^ N * a) = 0 := by
      have hea : ev R p (j + 1) a = c := by
        unfold ev
        exact ha
      rw [map_sub, ← hc, map_mul, map_pow, map_natCast, hea, mul_comm]
      exact sub_self _
    unfold ev at h0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact ⟨a, b, by linear_combination -hb⟩
  have hEJ : F - g * W ∈ J := by
    rw [hab]
    exact J.add_mem (hpow N hkN a) (hcyc b)
  have hDcyc : D (cyc R p (j + 1)) ∈ J := by
    have hc : cyc R p (j + 1) = ∑ i ∈ Finset.range p, (1 + PowerSeries.X) ^ (p ^ j * i) := by
      unfold cyc
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp.out, Polynomial.eval₂_finset_sum]
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_mul]
    rw [hc, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz_pow, map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      zero_add, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_assoc]
    exact hpow j hkj _
  have hDE : D (F - g * W) ∈ J := by
    rw [hab, map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.map_natCast]
    simp only [smul_zero, mul_zero, add_zero, smul_eq_mul]
    exact J.add_mem (hpow N hkN _) (J.add_mem (hcyc _) (J.mul_mem_left _ hDcyc))
  have hDW : D W ∈ J := by
    rw [hW, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow]
    exact hpow n hkn _
  have hdd : ∀ x, dd x = (1 + PowerSeries.X) * D x := by
    intro x
    unfold dd
    rfl
  have hFi := Ring.mul_inverse_cancel F hF
  have hgi := Ring.mul_inverse_cancel g hg
  have key : dl F - dl g =
      Ring.inverse F * Ring.inverse g * ((1 + PowerSeries.X) * (D F * g - D g * F)) := by
    unfold dl
    rw [hdd F, hdd g]
    linear_combination (-(1 + PowerSeries.X) * D F * Ring.inverse F) * hgi +
      ((1 + PowerSeries.X) * D g * Ring.inverse g) * hFi
  have hmid : D F * g - D g * F = g * g * D W + g * D (F - g * W) - D g * (F - g * W) := by
    have hDF : D F = D (F - g * W) + g * D W + W * D g := by
      rw [map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hDF]
    ring
  unfold LC
  rw [← map_sub]
  apply hev
  rw [key]
  refine J.mul_mem_left _ (J.mul_mem_left _ ?_)
  rw [hmid]
  exact J.sub_mem (J.add_mem (J.mul_mem_left _ hDW) (J.mul_mem_left _ hDE)) (J.mul_mem_left _ hEJ)

end UpperTheory.Kd.C7
