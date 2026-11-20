import Formalism.WindowSums.Statement

noncomputable section

namespace Formalism.WindowSums

open PowerSeries

/- English proof (translation)
Introduce `O _ _ ϖ hϖ hnu ι I w e m B s hw he`. Prove the components needed by the constructor for the conclusion. Introduce `hmem`. Assume the negation of the conclusion as `hbad`. Use `push_neg at hbad`.

Take `⟨i₁, hi₁, hb₁, hs₁⟩` from `hbad`. Establish `hJne : (I.filter fun i => e i < B ∧ m i < s).Nonempty` using `⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hb₁, hs₁⟩⟩`. Take `⟨i₀, hi₀J, hmin⟩` from `(I.filter fun i => e i < B ∧ m i < s).exists_min_image e hJne`. Take `⟨hi₀, hB, hs⟩` from `Finset.mem_filter.mp hi₀J`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.mp hmem`.

Establish `hcoef` using `congrArg (PowerSeries.coeff (e i₀)) hab`. Rewrite `hcoef` using `[map_add, mul_comm a, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add, PowerSeries.coeff_mul_C, map_sum]`. Establish `hterm : ∀ i ∈ I, PowerSeries.coeff (e i₀) (w i * X ^ e i * C (ϖ ^ m i)) = (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i`. Introduce `i _`. Rewrite using `[PowerSeries.coeff_mul_C, mul_comm (w i), PowerSeries.coeff_X_pow_mul']`.

Rewrite `hcoef` using `[Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ hi₀, if_pos le_rfl, Nat.sub_self]`. Establish `hrest : ϖ ^ s ∣ ∑ i ∈ I.erase i₀, (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i`. Use `Finset.dvd_sum fun i hi => ?_` and prove the remaining obligations. Take `⟨hne, hiI⟩` from `Finset.mem_erase.mp hi`. Distinguish the cases in `hle : e i ≤ e i₀`.

Rewrite using `[if_pos hle]`. Establish `hlt : e i < e i₀` using `lt_of_le_of_ne hle fun h => hne (he hiI hi₀ h)`. Establish `hms : s ≤ m i`. Assume the negation of the conclusion as `hms`. Use `push_neg at hms`.

Use `hmin i (Finset.mem_filter.mpr ⟨hiI, by omega, hms⟩)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow ϖ hms) _`. Rewrite using `[if_neg hle, zero_mul]`. Conclude with `dvd_zero _`.

Establish `hdvd : ϖ ^ s ∣ PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀`. Establish `h2 : PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ = PowerSeries.coeff (e i₀) b * ϖ ^ s - ∑ i ∈ I.erase i₀, (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i`. Rewrite using `[hcoef]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Conclude with `dvd_sub (dvd_mul_left _ _) hrest`. Establish `hu : IsUnit (PowerSeries.coeff 0 (w i₀))`. Use `(hw i₀ hi₀).map (PowerSeries.constantCoeff (R := O))` as an intermediate fact. Simplify using `using this`. Establish `hsplit : ϖ ^ s = ϖ ^ m i₀ * ϖ ^ (s - m i₀)`.

Rewrite using `[← pow_add, Nat.add_sub_cancel' hs.le]`. Rewrite `hdvd` using `[hsplit, mul_comm (PowerSeries.coeff 0 (w i₀))]`. Establish `hd2` using `(mul_dvd_mul_iff_left (pow_ne_zero _ hϖ)).mp hdvd`. Establish `hd3 : ϖ ∣ PowerSeries.coeff 0 (w i₀)` using `(dvd_pow_self ϖ (by omega)).trans hd2`. Conclude with `hnu (isUnit_of_dvd_unit hd3 hu)`.

Introduce `h`. Use `Ideal.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Break down `h i hi with hb | hs` into its components or cases. Establish `hx : (X : PowerSeries O) ^ B ∈ Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)}` using `Ideal.subset_span (Set.mem_insert _ _)`. Establish `heq : w i * X ^ e i * C (ϖ ^ m i) = X ^ B * (w i * X ^ (e i - B) * C (ϖ ^ m i))`.

Rewrite using `[show e i = B + (e i - B) by omega, pow_add]`. Simplify using `only [Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `Ideal.mul_mem_right _ _ hx`.

Establish `hc : C (ϖ ^ s) ∈ Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)}` using `Ideal.subset_span (Set.mem_insert_of_mem _ rfl)`. Establish `heq : w i * X ^ e i * C (ϖ ^ m i) = C (ϖ ^ s) * (w i * X ^ e i * C (ϖ ^ (m i - s)))`. Rewrite using `[show m i = s + (m i - s) by omega, pow_add, map_mul]`. Simplify using `only [Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `Ideal.mul_mem_right _ _ hc`.
-/
theorem mem_span_iff_of_distinct_exponents : DistinctTerms := by
  intro O _ _ ϖ hϖ hnu ι I w e m B s hw he
  classical
  constructor
  · intro hmem
    by_contra hbad
    push_neg at hbad
    obtain ⟨i₁, hi₁, hb₁, hs₁⟩ := hbad
    have hJne : (I.filter fun i => e i < B ∧ m i < s).Nonempty :=
      ⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hb₁, hs₁⟩⟩
    obtain ⟨i₀, hi₀J, hmin⟩ := (I.filter fun i => e i < B ∧ m i < s).exists_min_image e hJne
    obtain ⟨hi₀, hB, hs⟩ := Finset.mem_filter.mp hi₀J
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    have hcoef := congrArg (PowerSeries.coeff (e i₀)) hab
    rw [map_add, mul_comm a, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_mul_C, map_sum] at hcoef
    have hterm : ∀ i ∈ I, PowerSeries.coeff (e i₀) (w i * X ^ e i * C (ϖ ^ m i)) =
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      intro i _
      rw [PowerSeries.coeff_mul_C, mul_comm (w i), PowerSeries.coeff_X_pow_mul']
    rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ hi₀, if_pos le_rfl,
      Nat.sub_self] at hcoef
    have hrest : ϖ ^ s ∣ ∑ i ∈ I.erase i₀,
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      refine Finset.dvd_sum fun i hi => ?_
      obtain ⟨hne, hiI⟩ := Finset.mem_erase.mp hi
      by_cases hle : e i ≤ e i₀
      · rw [if_pos hle]
        have hlt : e i < e i₀ := lt_of_le_of_ne hle fun h => hne (he hiI hi₀ h)
        have hms : s ≤ m i := by
          by_contra hms
          push_neg at hms
          have := hmin i (Finset.mem_filter.mpr ⟨hiI, by omega, hms⟩)
          omega
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hms) _
      · rw [if_neg hle, zero_mul]
        exact dvd_zero _
    have hdvd : ϖ ^ s ∣ PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ := by
      have h2 : PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ =
          PowerSeries.coeff (e i₀) b * ϖ ^ s - ∑ i ∈ I.erase i₀,
            (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
        rw [hcoef]; ring
      rw [h2]
      exact dvd_sub (dvd_mul_left _ _) hrest
    have hu : IsUnit (PowerSeries.coeff 0 (w i₀)) := by
      have := (hw i₀ hi₀).map (PowerSeries.constantCoeff (R := O))
      simpa using this
    have hsplit : ϖ ^ s = ϖ ^ m i₀ * ϖ ^ (s - m i₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hs.le]
    rw [hsplit, mul_comm (PowerSeries.coeff 0 (w i₀))] at hdvd
    have hd2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ)).mp hdvd
    have hd3 : ϖ ∣ PowerSeries.coeff 0 (w i₀) :=
      (dvd_pow_self ϖ (by omega)).trans hd2
    exact hnu (isUnit_of_dvd_unit hd3 hu)
  · intro h
    refine Ideal.sum_mem _ fun i hi => ?_
    rcases h i hi with hb | hs
    · have hx : (X : PowerSeries O) ^ B ∈
          Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert _ _)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = X ^ B * (w i * X ^ (e i - B) * C (ϖ ^ m i)) := by
        rw [show e i = B + (e i - B) by omega, pow_add]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hx
    · have hc : C (ϖ ^ s) ∈ Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = C (ϖ ^ s) * (w i * X ^ e i * C (ϖ ^ (m i - s))) := by
        rw [show m i = s + (m i - s) by omega, pow_add, map_mul]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hc

end Formalism.WindowSums
