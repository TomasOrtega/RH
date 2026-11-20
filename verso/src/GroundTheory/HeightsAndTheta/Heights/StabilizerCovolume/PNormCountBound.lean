import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using induction_on_primes with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one`.

Introduce `_ h`. Conclude with `absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top`. Consider the case `prime_mul p a hp ih`. Introduce `hpa h`. Rewrite `h` using `[Nat.cast_mul]`.

Break down `hP.mem_or_mem h with h | h` into its components or cases. Conclude with `⟨p, hp, h⟩`. Conclude with `ih (right_ne_zero_of_mul hpa) h`.
-/
theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ P := by
  intro n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    intro hpa h
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (right_ne_zero_of_mul hpa) h

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Use `exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal) ?_ (Ideal.absNorm_mem _)` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`.
-/
theorem exists_prime_mem_heightOneSpectrum {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ v.asIdeal := by
  have := v.isPrime
  refine exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal) ?_ (Ideal.absNorm_mem _)
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

/- English proof (translation)
Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `h : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Conclude with `Nat.one_le_iff_ne_zero.mpr h` after adjusting the coercions.
-/
theorem log_absNorm_heightOneSpectrum_nonneg {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  apply Real.log_nonneg
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

/- English proof (translation)
Establish `hfac` using `FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := L) hI`. Rewrite `hfac` using `[finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]`. Establish `h1 : (FractionalIdeal.absNorm I : ℝ) = ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ (FractionalIdeal.count L v I)` using `by conv_lhs => rw [← hfac]`. Rewrite using `[map_prod, Rat.cast_prod]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]`. Rewrite using `[h1, Real.log_prod]`. Conclude with `Finset.sum_congr rfl fun v _ => Real.log_zpow _ _`. Introduce `v _`. Apply `zpow_ne_zero` to reduce the goal to its premises.

Rewrite using `[Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Introduce `v hv`. Rewrite `hv` using `[Function.mem_mulSupport]`. Apply `hT v` to reduce the goal to its premises.

Introduce `h0`. Apply `hv` to reduce the goal to its premises. Rewrite using `[h0, zpow_zero]`.
-/
theorem log_absNorm_eq_sum {L : Type} [Field L] [NumberField L] {I : FractionalIdeal (𝓞 L)⁰ L}
    (hI : I ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, FractionalIdeal.count L v I ≠ 0 → v ∈ T) :
    Real.log (FractionalIdeal.absNorm I : ℝ) =
      ∑ v ∈ T, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := L) hI
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hfac
  · have h1 : (FractionalIdeal.absNorm I : ℝ) =
        ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ (FractionalIdeal.count L v I) := by
      conv_lhs => rw [← hfac]
      rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    rw [h1, Real.log_prod]
    · exact Finset.sum_congr rfl fun v _ => Real.log_zpow _ _
    · intro v _
      apply zpow_ne_zero
      rw [Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    apply hT v
    intro h0
    apply hv
    rw [h0, zpow_zero]

/- English proof (translation)
Rewrite using `[primeFrac, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_span_natCast, RingOfIntegers.rank]`. Use `push_cast`. Rewrite using `[Real.log_pow]`.
-/
theorem log_absNorm_primeFrac (L : Type) [Field L] [NumberField L] (q : ℕ) :
    Real.log (FractionalIdeal.absNorm (primeFrac L q) : ℝ) = Module.finrank ℚ L * Real.log q := by
  rw [primeFrac, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  push_cast
  rw [Real.log_pow]

/- English proof (translation)
Introduce `L _ _ 𝔠 𝔇 S a b h𝔠 h𝔇 ha hb hloc`. Establish `fin : ∀ J : FractionalIdeal (𝓞 L)⁰ L, {v : HeightOneSpectrum (𝓞 L) | FractionalIdeal.count L v J ≠ 0}.Finite` using `fun J => Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)`. Set `P` to `S.filter Nat.Prime`. Set `T : Finset (HeightOneSpectrum (𝓞 L))` to `(fin 𝔠).toFinset ∪ (fin (𝔇 : FractionalIdeal (𝓞 L)⁰ L)).toFinset ∪ P.biUnion (fun q => (fin (primeFrac L q)).toFinset)`. Establish `h𝔠T : ∀ v, FractionalIdeal.count L v 𝔠 ≠ 0 → v ∈ T` using `fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ ((fin 𝔠).mem_toFinset.mpr hv))`.

Establish `h𝔇T : ∀ v, FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 → v ∈ T` using `fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ ((fin _).mem_toFinset.mpr hv))`. Establish `hqT : ∀ q ∈ P, ∀ v, FractionalIdeal.count L v (primeFrac L q) ≠ 0 → v ∈ T` using `fun q hq v hv => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq, (fin _).mem_toFinset.mpr hv⟩)`. Establish `h𝔠eq` using `log_absNorm_eq_sum h𝔠 T h𝔠T`. Establish `h𝔇eq` using `log_absNorm_eq_sum (I := (𝔇 : FractionalIdeal (𝓞 L)⁰ L)) (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact h𝔇) T h𝔇T`. Rewrite `h𝔇eq` using `[FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]`.

Establish `hqeq : ∀ q ∈ P, ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) = Module.finrank ℚ L * Real.log q` using `fun q hq => by`. Rewrite using `[← log_absNorm_eq_sum (primeFrac_ne_zero L (Finset.mem_filter.mp hq).2) T (hqT q hq), log_absNorm_primeFrac]`. Establish `hterm : ∀ q ∈ P, ∀ v : HeightOneSpectrum (𝓞 L), 0 ≤ a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1)` using `fun q hq v => by`. Apply `div_nonneg (mul_nonneg ha (by exact_mod_cast FractionalIdeal.count_coe_nonneg L v _))` to reduce the goal to its premises. Establish `: (1 : ℝ) ≤ q` using `by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv : ∀ v : HeightOneSpectrum (𝓞 L), |(FractionalIdeal.count L v 𝔠 : ℝ)| ≤ ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) + b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)` using `fun v => by`. Take `⟨p, hp, hpv⟩` from `exists_prime_mem_heightOneSpectrum v`. Establish `h1` using `hloc p hp v hpv`. Establish `h2 : (if p ∈ S then a * (FractionalIdeal.count L v (primeFrac L p) : ℝ) / ((p : ℝ) - 1) else 0) ≤ ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1)` using `by split_ifs with hpS`.

Conclude with `Finset.single_le_sum (f := fun q => a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1)) (fun q hq => hterm q hq v) (Finset.mem_filter.mpr ⟨hpS, hp⟩)`. Conclude with `Finset.sum_nonneg fun q hq => hterm q hq v`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS : ∑ q ∈ P, Real.log q / ((q : ℝ) - 1) ≤ ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)`. Apply `Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)` to reduce the goal to its premises.

Introduce `q _ _`. Break down `q with _ | q` into its components or cases. Simplify using the standard rewrite rules. Establish `: (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.le_add_left 1 q`. Conclude with `div_nonneg (Real.log_nonneg this) (by linarith)`.

Establish `hfin : (0 : ℝ) ≤ Module.finrank ℚ L` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h𝔠eq]`. Use `_ ≤ ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| := Finset.abs_sum_le_sum_abs _ _`. Use `_ = ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ)| * Real.log (Ideal.absNorm v.asIdeal : ℝ) := Finset.sum_congr rfl fun v _ => by`.

Rewrite using `[abs_mul, abs_of_nonneg (log_absNorm_heightOneSpectrum_nonneg v)]`. Use `_ ≤ ∑ v ∈ T, (∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) + b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (hv v) (log_absNorm …`. Use `_ = ∑ q ∈ P, a / ((q : ℝ) - 1) * ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) + b * ∑ v ∈ T, (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by`. Simplify using `only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun v _ => by ring`. Conclude with `Finset.sum_congr rfl fun v _ => by ring`. Use `_ = Module.finrank ℚ L * (a * ∑ q ∈ P, Real.log q / ((q : ℝ) - 1)) + b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by`. Rewrite using `[h𝔇eq, Finset.sum_congr rfl fun q hq => by rw [hqeq q hq]]`.

Use `congr 1`. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => by ring`. Use `_ ≤ Module.finrank ℚ L * (a * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)) + b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by gcongr`.
-/
theorem NormCountBound.full : NormCountBound.Statement := by
  intro L _ _ 𝔠 𝔇 S a b h𝔠 h𝔇 ha hb hloc
  classical
  have fin : ∀ J : FractionalIdeal (𝓞 L)⁰ L,
      {v : HeightOneSpectrum (𝓞 L) | FractionalIdeal.count L v J ≠ 0}.Finite :=
    fun J => Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  let P := S.filter Nat.Prime
  let T : Finset (HeightOneSpectrum (𝓞 L)) := (fin 𝔠).toFinset ∪ (fin (𝔇 : FractionalIdeal (𝓞 L)⁰ L)).toFinset ∪
    P.biUnion (fun q => (fin (primeFrac L q)).toFinset)
  have h𝔠T : ∀ v, FractionalIdeal.count L v 𝔠 ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ ((fin 𝔠).mem_toFinset.mpr hv))
  have h𝔇T : ∀ v, FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ ((fin _).mem_toFinset.mpr hv))
  have hqT : ∀ q ∈ P, ∀ v, FractionalIdeal.count L v (primeFrac L q) ≠ 0 → v ∈ T := fun q hq v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq, (fin _).mem_toFinset.mpr hv⟩)
  have h𝔠eq := log_absNorm_eq_sum h𝔠 T h𝔠T
  have h𝔇eq := log_absNorm_eq_sum (I := (𝔇 : FractionalIdeal (𝓞 L)⁰ L))
    (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact h𝔇) T h𝔇T
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h𝔇eq
  have hqeq : ∀ q ∈ P, ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
      Real.log (Ideal.absNorm v.asIdeal : ℝ) = Module.finrank ℚ L * Real.log q := fun q hq => by
    rw [← log_absNorm_eq_sum (primeFrac_ne_zero L (Finset.mem_filter.mp hq).2) T (hqT q hq),
      log_absNorm_primeFrac]
  have hterm : ∀ q ∈ P, ∀ v : HeightOneSpectrum (𝓞 L),
      0 ≤ a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := fun q hq v => by
    apply div_nonneg (mul_nonneg ha (by exact_mod_cast FractionalIdeal.count_coe_nonneg L v _))
    have : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le
    linarith
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), |(FractionalIdeal.count L v 𝔠 : ℝ)| ≤
      ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
        b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) := fun v => by
    obtain ⟨p, hp, hpv⟩ := exists_prime_mem_heightOneSpectrum v
    have h1 := hloc p hp v hpv
    have h2 : (if p ∈ S then a * (FractionalIdeal.count L v (primeFrac L p) : ℝ) / ((p : ℝ) - 1) else 0) ≤
        ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := by
      split_ifs with hpS
      · exact Finset.single_le_sum (f := fun q => a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) /
          ((q : ℝ) - 1)) (fun q hq => hterm q hq v) (Finset.mem_filter.mpr ⟨hpS, hp⟩)
      · exact Finset.sum_nonneg fun q hq => hterm q hq v
    linarith
  have hS : ∑ q ∈ P, Real.log q / ((q : ℝ) - 1) ≤ ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro q _ _
    rcases q with _ | q
    · simp
    · have : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 q
      exact div_nonneg (Real.log_nonneg this) (by linarith)
  have hfin : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  calc |Real.log (FractionalIdeal.absNorm 𝔠 : ℝ)|
      = |∑ v ∈ T, (FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| := by
        rw [h𝔠eq]
    _ ≤ ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ)| * Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_congr rfl fun v _ => by
          rw [abs_mul, abs_of_nonneg (log_absNorm_heightOneSpectrum_nonneg v)]
    _ ≤ ∑ v ∈ T, (∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
          b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_right (hv v) (log_absNorm_heightOneSpectrum_nonneg v)
    _ = ∑ q ∈ P, a / ((q : ℝ) - 1) * ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) +
        b * ∑ v ∈ T, (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        · exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun v _ => by ring
        · exact Finset.sum_congr rfl fun v _ => by ring
    _ = Module.finrank ℚ L * (a * ∑ q ∈ P, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        rw [h𝔇eq, Finset.sum_congr rfl fun q hq => by rw [hqeq q hq]]
        congr 1
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ Module.finrank ℚ L * (a * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        gcongr

end GroundTheory.Heights₂.Heights.NineStatements
