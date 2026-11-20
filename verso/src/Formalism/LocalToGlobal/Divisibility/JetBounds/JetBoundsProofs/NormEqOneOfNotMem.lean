import Formalism.LocalToGlobal.Divisibility.JetBounds.EmbExists
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormInvNatCastLeOfDvd
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.VwEqZeroOfNotMem

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.DworkPowerSeriesWeights

namespace EmbeddingLemmas

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨p, hmon, hev⟩` from `hy`. Establish `hsumle : ∀ (s : Finset ℕ) (f : ℕ → k) (C : ℝ), 0 ≤ C → (∀ i ∈ s, ‖f i‖ ≤ C) → ‖∑ i ∈ s, f i‖ ≤ C`. Introduce `s f C hC`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `using hC`. Consider the case `insert a s ha ih`. Introduce `h`.

Rewrite using `[Finset.sum_insert ha]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))`. Rewrite `hev` using `[hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum]`. Establish `hyn` using `eq_neg_of_add_eq_zero_left hev`. Establish `hy1 : (1 : ℝ) ≤ ‖y‖` using `hlt.le`.

Distinguish the cases in `hn : p.natDegree = 0`. Rewrite `hyn` using `[hn, pow_zero, Finset.range_zero, Finset.sum_empty, neg_zero]`. Conclude with `one_ne_zero hyn`. Establish `hb : ∀ i ∈ Finset.range p.natDegree, ‖Polynomial.eval₂ (algebraMap ℤ k) y (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖y‖ ^ (p.natDegree - 1)`. Introduce `i hi`.

Rewrite using `[Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]`. Establish `hc : ‖(algebraMap ℤ k) (p.coeff i)‖ ≤ 1`. Rewrite using `[algebraMap_int_eq, eq_intCast]`. Conclude with `IsUltrametricDist.norm_intCast_le_one k _`. Establish `hi' : i ≤ p.natDegree - 1`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Establish `hle` using `hsumle _ _ _ (by positivity) hb`. Establish `hle' : ‖y‖ ^ p.natDegree ≤ ‖y‖ ^ (p.natDegree - 1)`.

Rewrite using `[← norm_pow, hyn, norm_neg]`. Conclude with `hle`. Establish `hlt' : ‖y‖ ^ (p.natDegree - 1) < ‖y‖ ^ p.natDegree` using `pow_lt_pow_right₀ hlt (by omega)`. Combine the linear relations using `[hle']`.
-/
theorem norm_le_one_of_isIntegral {k : Type} [NormedField k] [IsUltrametricDist k] {y : k}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hmon, hev⟩ := hy
  have hsumle : ∀ (s : Finset ℕ) (f : ℕ → k) (C : ℝ), 0 ≤ C → (∀ i ∈ s, ‖f i‖ ≤ C) → ‖∑ i ∈ s, f i‖ ≤ C := by
    intro s f C hC
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hC
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hev
  have hyn := eq_neg_of_add_eq_zero_left hev
  have hy1 : (1 : ℝ) ≤ ‖y‖ := hlt.le
  by_cases hn : p.natDegree = 0
  · rw [hn, pow_zero, Finset.range_zero, Finset.sum_empty, neg_zero] at hyn
    exact one_ne_zero hyn
  have hb : ∀ i ∈ Finset.range p.natDegree,
      ‖Polynomial.eval₂ (algebraMap ℤ k) y (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖y‖ ^ (p.natDegree - 1) := by
    intro i hi
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖(algebraMap ℤ k) (p.coeff i)‖ ≤ 1 := by
      rw [algebraMap_int_eq, eq_intCast]
      exact IsUltrametricDist.norm_intCast_le_one k _
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.1 hi
      omega
    calc ‖(algebraMap ℤ k) (p.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (p.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hy1 hi') (by positivity) zero_le_one
      _ = ‖y‖ ^ (p.natDegree - 1) := one_mul _
  have hle := hsumle _ _ _ (by positivity) hb
  have hle' : ‖y‖ ^ p.natDegree ≤ ‖y‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, hyn, norm_neg]
    exact hle
  have hlt' : ‖y‖ ^ (p.natDegree - 1) < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith [hle']

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
The claim follows from `map_add (algebraMap (𝓞 K) K) x y`.
-/
theorem cAdd (x y : 𝓞 K) : ((x + y : 𝓞 K) : K) = (x : K) + (y : K) := map_add (algebraMap (𝓞 K) K) x y

/- English proof (translation)
The claim follows from `map_mul (algebraMap (𝓞 K) K) x y`.
-/
theorem cMul (x y : 𝓞 K) : ((x * y : 𝓞 K) : K) = (x : K) * (y : K) := map_mul (algebraMap (𝓞 K) K) x y

/- English proof (translation)
The claim follows from `map_zero (algebraMap (𝓞 K) K)`.
-/
theorem cZero : ((0 : 𝓞 K) : K) = 0 := map_zero (algebraMap (𝓞 K) K)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cNat (n : ℕ) : ((n : 𝓞 K) : K) = (n : K) := by simp

/- English proof (translation)
Establish `hspan : Ideal.span {x} ≠ (0 : Ideal (𝓞 K))`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hx`. Rewrite using `[Formalism.DivisionValues.ValuationRepresentative.vw_int, FractionalIdeal.count_coe K w hspan, Nat.cast_le, ← Ideal.dvd_span_singleton, ← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]`. Conclude with `Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hspan) w.associates_irreducible`.
-/
theorem mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) (m : ℕ) :
    x ∈ w.asIdeal ^ m ↔ (m : ℤ) ≤ vw w (x : K) := by
  classical
  have hspan : Ideal.span {x} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_int, FractionalIdeal.count_coe K w hspan, Nat.cast_le,
    ← Ideal.dvd_span_singleton, ← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hspan) w.associates_irreducible

/- English proof (translation)
Distinguish the cases in `hb0 : b = 0`. Use `⟨1, 0, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Rewrite using `[hb0, mul_zero, cZero]`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) b`.

Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hyK : (algebraMap (𝓞 K) K y) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Establish `hxK : (algebraMap (𝓞 K) K x) ≠ 0` using `fun h => hb0 (by rw [h, zero_div])`. Establish `hx0 : x ≠ 0` using `fun h => hxK (by rw [h, map_zero])`. Establish `hvy : 0 ≤ vw w (algebraMap (𝓞 K) K y)` using `ValuationRepresentative.vw_int_nonneg w y`.

Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le hvy`. Rewrite `hb` using `[div_eq_mul_inv, ValuationRepresentative.vw_mul w _ _ hxK (inv_ne_zero hyK), ValuationRepresentative.vw_inv]`. Establish `hxm : x ∈ w.asIdeal ^ m` using `(mem_pow_iff w x hx0 m).2 (by`. Express the relevant statement in the definitionally equal form `(m : ℤ) ≤ vw w (algebraMap (𝓞 K) K x)`. Use the proof step `omega)`.

Establish `hym : y ∈ w.asIdeal ^ m` using `(mem_pow_iff w y hy0 m).2 (by`. Express the relevant statement in the definitionally equal form `(m : ℤ) ≤ vw w (algebraMap (𝓞 K) K y)`. Use the proof step `omega)`. Establish `hym1 : y ∉ w.asIdeal ^ (m + 1)` using `fun h => by`. Establish `h2` using `(mem_pow_iff w y hy0 (m + 1)).1 h`.

Express the relevant statement in the definitionally equal form `((m + 1 : ℕ) : ℤ) ≤ vw w (algebraMap (𝓞 K) K y) at h2`. Move the coercions through the operations in `at h2`. Use linear arithmetic over natural numbers and integers. Establish `hdvd : w.asIdeal ^ m ∣ Ideal.span {y}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `hym`. Take `⟨J, hJ⟩` from `hdvd`. Establish `hJw : ¬ J ≤ w.asIdeal` using `fun h => by`. Apply `hym1` to reduce the goal to its premises. Establish `h1 : y ∈ w.asIdeal ^ m * J`.

Rewrite using `[← hJ]`. Conclude with `Ideal.mem_span_singleton_self y`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mono_right h h1`. Take `⟨c, hcJ, hcw⟩` from `SetLike.not_le_iff_exists.1 hJw`.

Establish `hxc : x * c ∈ Ideal.span {y}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul hxm hcJ`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 hxc`. Use `⟨c, z, hcw, ?_⟩` and prove the remaining obligations.

Establish `hz' : (algebraMap (𝓞 K) K z) * (algebraMap (𝓞 K) K y) = (algebraMap (𝓞 K) K x) * (algebraMap (𝓞 K) K c)`. Rewrite using `[← map_mul, ← map_mul, hz]`. Express the relevant statement in the definitionally equal form `(algebraMap (𝓞 K) K c) * _ = algebraMap (𝓞 K) K z`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hz'`.
-/
theorem exists_clear (w : HeightOneSpectrum (𝓞 K)) (b : K) (hb : 0 ≤ vw w b) :
    ∃ c z : 𝓞 K, c ∉ w.asIdeal ∧ (c : K) * b = (z : K) := by
  by_cases hb0 : b = 0
  · refine ⟨1, 0, ?_, ?_⟩
    · exact fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · rw [hb0, mul_zero, cZero]
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : (algebraMap (𝓞 K) K y) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hxK : (algebraMap (𝓞 K) K x) ≠ 0 := fun h => hb0 (by rw [h, zero_div])
  have hx0 : x ≠ 0 := fun h => hxK (by rw [h, map_zero])
  have hvy : 0 ≤ vw w (algebraMap (𝓞 K) K y) := ValuationRepresentative.vw_int_nonneg w y
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hvy
  rw [div_eq_mul_inv, ValuationRepresentative.vw_mul w _ _ hxK (inv_ne_zero hyK), ValuationRepresentative.vw_inv] at hb
  have hxm : x ∈ w.asIdeal ^ m := (mem_pow_iff w x hx0 m).2 (by
    change (m : ℤ) ≤ vw w (algebraMap (𝓞 K) K x)
    omega)
  have hym : y ∈ w.asIdeal ^ m := (mem_pow_iff w y hy0 m).2 (by
    change (m : ℤ) ≤ vw w (algebraMap (𝓞 K) K y)
    omega)
  have hym1 : y ∉ w.asIdeal ^ (m + 1) := fun h => by
    have h2 := (mem_pow_iff w y hy0 (m + 1)).1 h
    change ((m + 1 : ℕ) : ℤ) ≤ vw w (algebraMap (𝓞 K) K y) at h2
    push_cast at h2
    omega
  have hdvd : w.asIdeal ^ m ∣ Ideal.span {y} := by
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hym
  obtain ⟨J, hJ⟩ := hdvd
  have hJw : ¬ J ≤ w.asIdeal := fun h => by
    apply hym1
    have h1 : y ∈ w.asIdeal ^ m * J := by
      rw [← hJ]
      exact Ideal.mem_span_singleton_self y
    rw [pow_succ]
    exact Ideal.mul_mono_right h h1
  obtain ⟨c, hcJ, hcw⟩ := SetLike.not_le_iff_exists.1 hJw
  have hxc : x * c ∈ Ideal.span {y} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hxm hcJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hxc
  refine ⟨c, z, hcw, ?_⟩
  have hz' : (algebraMap (𝓞 K) K z) * (algebraMap (𝓞 K) K y) =
      (algebraMap (𝓞 K) K x) * (algebraMap (𝓞 K) K c) := by
    rw [← map_mul, ← map_mul, hz]
  change (algebraMap (𝓞 K) K c) * _ = algebraMap (𝓞 K) K z
  field_simp
  linear_combination -hz'

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨p, hp, hpx⟩` from `NumberField.RingOfIntegers.isIntegral_coe x`. Use `norm_le_one_of_isIntegral ⟨p, hp, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg σ hpx`. Rewrite `h` using `[map_zero, Polynomial.hom_eval₂]`. Establish `h2 : Polynomial.eval₂ (Int.castRingHom ℂ_[l]) (σ x) p = 0`.

Rewrite using `[← RingHom.ext_int (σ.comp (algebraMap ℤ K)) (Int.castRingHom ℂ_[l])]`. Conclude with `h`. Conclude with `h2`.
-/
theorem norm_int_le (σ : K →+* ℂ_[l]) (x : 𝓞 K) : ‖σ (x : K)‖ ≤ 1 := by
  obtain ⟨p, hp, hpx⟩ := NumberField.RingOfIntegers.isIntegral_coe x
  refine norm_le_one_of_isIntegral ⟨p, hp, ?_⟩
  have h := congrArg σ hpx
  rw [map_zero, Polynomial.hom_eval₂] at h
  have h2 : Polynomial.eval₂ (Int.castRingHom ℂ_[l]) (σ x) p = 0 := by
    rw [← RingHom.ext_int (σ.comp (algebraMap ℤ K)) (Int.castRingHom ℂ_[l])]
    exact h
  exact h2

def normIdeal (σ : K →+* ℂ_[l]) : Ideal (𝓞 K) where
  carrier := {x | ‖σ (x : K)‖ < 1}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [cAdd, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [cZero, map_zero, norm_zero]
    exact one_pos
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_eq_mul, cMul, map_mul, norm_mul]
    calc ‖σ (c : K)‖ * ‖σ (x : K)‖ ≤ 1 * ‖σ (x : K)‖ :=
          mul_le_mul_of_nonneg_right (norm_int_le σ c) (norm_nonneg _)
      _ < 1 := by rwa [one_mul]

end EmbeddingLemmas

/- English proof (translation)
Introduce `K _ _ _ w l hlp ι h`. Assume the negation of the conclusion as `hne`. Establish `hnot : (l : 𝓞 K) ∉ w.asIdeal`. Introduce `hmem`. Rewrite `hmem` using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Establish `hdvd : plc w ∣ l` using `(ringChar.spec (𝓞 K ⧸ w.asIdeal) l).1 hmem`. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.ramBasic K w).1 hlp.out).1 hdvd)`. Establish `hv : vw w (l : K) = 0`. Establish `h2` using `ValuationZeroReduction.vw_eq_zero_of_not_mem w (l : 𝓞 K) hnot`. Rewrite `h2` using `[EmbeddingLemmas.cNat]`. Then use the resulting hypothesis.

Establish `h3` using `h (l : K) (Nat.cast_ne_zero.2 hlp.out.ne_zero)`. Rewrite `h3` using `[map_natCast, hv, Int.cast_zero, zero_div, Real.rpow_zero]`. Conclude with `absurd h3 (norm_l_lt_one l).ne`.
-/
theorem embeddingForces_holds : EmbForces := by
  intro K _ _ _ w l hlp ι h
  by_contra hne
  have hnot : (l : 𝓞 K) ∉ w.asIdeal := by
    intro hmem
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
    have hdvd : plc w ∣ l := (ringChar.spec (𝓞 K ⧸ w.asIdeal) l).1 hmem
    exact hne ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.ramBasic K w).1 hlp.out).1 hdvd)
  have hv : vw w (l : K) = 0 := by
    have h2 := ValuationZeroReduction.vw_eq_zero_of_not_mem w (l : 𝓞 K) hnot
    rwa [EmbeddingLemmas.cNat] at h2
  have h3 := h (l : K) (Nat.cast_ne_zero.2 hlp.out.ne_zero)
  rw [map_natCast, hv, Int.cast_zero, zero_div, Real.rpow_zero] at h3
  exact absurd h3 (norm_l_lt_one l).ne

end Formalism.L2.DIV
