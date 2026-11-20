import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain Ideal

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_inv_sq_le_one_of_two_le (T : Finset ℕ) (hT : ∀ n ∈ T, 2 ≤ n) : ∑ n ∈ T, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
  classical
  have hsub : T ⊆ Finset.Ioc 1 (T.sup id + 1) := by
    intro n hn
    rw [Finset.mem_Ioc]
    exact ⟨by have := hT n hn; omega, le_trans (Finset.le_sup (f := id) hn) (Nat.le_succ _)⟩
  calc ∑ n ∈ T, ((n : ℝ) ^ 2)⁻¹ ≤ ∑ n ∈ Finset.Ioc 1 (T.sup id + 1), ((n : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ((1 : ℕ) : ℝ)⁻¹ - ((T.sup id + 1 : ℕ) : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub one_ne_zero (by omega)
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ ((T.sup id + 1 : ℕ) : ℝ)⁻¹ := by positivity
        simp only [Nat.cast_one, inv_one]
        linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rpow_neg_le_two_pow_inv_sq (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 2 ≤ s) :
    (n : ℝ) ^ (-s) ≤ 2 ^ (2 - s) * ((n : ℝ) ^ 2)⁻¹ := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have e : (n : ℝ) ^ (-s) = (n : ℝ) ^ (2 - s) * ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
    congr 1
    push_cast
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos zero_lt_two hn2 (by linarith)) (by positivity)

/- English proof (translation)
Chain the equalities or inequalities of the calculation.
-/
theorem sum_rpow_neg_le_two_pow (T : Finset ℕ) (hT : ∀ n ∈ T, 2 ≤ n) (s : ℝ) (hs : 2 ≤ s) :
    ∑ n ∈ T, (n : ℝ) ^ (-s) ≤ 2 ^ (2 - s) := by
  calc ∑ n ∈ T, (n : ℝ) ^ (-s) ≤ ∑ n ∈ T, 2 ^ (2 - s) * ((n : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun n hn => rpow_neg_le_two_pow_inv_sq n (hT n hn) s hs)
    _ = 2 ^ (2 - s) * ∑ n ∈ T, ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 ^ (2 - s) * 1 := mul_le_mul_of_nonneg_left (sum_inv_sq_le_one_of_two_le T hT) (by positivity)
    _ = 2 ^ (2 - s) := mul_one _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem card_primes_over_rational_le (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (hn : n.Prime) [DecidableEq (HeightOneSpectrum (𝓞 F))] :
    (S.filter (fun p => absNorm (under ℤ p.asIdeal) = n)).card ≤ Module.finrank ℚ F := by
  classical
  have : Fact n.Prime := ⟨hn⟩
  have hp0 : (span {(n : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, span_singleton_eq_bot]
    exact_mod_cast hn.ne_zero
  refine le_trans (Finset.card_le_card_of_injOn (t := IsDedekindDomain.primesOverFinset (span {(n : ℤ)}) (𝓞 F))
    (fun p => p.asIdeal) ?_ ?_) (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0)
  · intro p hp
    have hp' : absNorm (under ℤ p.asIdeal) = n := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    refine ⟨p.isPrime, ?_⟩
    have := Int.liesOver_span_absNorm p.asIdeal
    rwa [hp'] at this
  · intro p _ p' _ h
    exact HeightOneSpectrum.ext h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem prime_ideal_norm_rpow_sum_le (F : Type) [Field F] [NumberField F] (s : ℝ) (hs : 2 ≤ s) :
    ∑' p : HeightOneSpectrum (𝓞 F), ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-s) ≤ (Module.finrank ℚ F : ℝ) * 2 ^ (2 - s) := by
  classical
  refine Real.tsum_le_of_sum_le (fun p => by positivity) (fun S => ?_)
  have hq_prime : ∀ p : HeightOneSpectrum (𝓞 F), (absNorm (under ℤ p.asIdeal)).Prime := fun p => by
    have : NeZero p.asIdeal := ⟨p.ne_bot⟩
    have := p.isPrime
    exact Nat.absNorm_under_prime p.asIdeal
  have hq_le : ∀ p : HeightOneSpectrum (𝓞 F), absNorm (under ℤ p.asIdeal) ≤ absNorm p.asIdeal := fun p =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [Ne, absNorm_eq_zero_iff]; exact p.ne_bot))
      (Int.absNorm_under_dvd_absNorm p.asIdeal)
  calc ∑ p ∈ S, ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-s)
      ≤ ∑ p ∈ S, ((absNorm (under ℤ p.asIdeal) : ℕ) : ℝ) ^ (-s) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        refine Real.rpow_le_rpow_of_nonpos ?_ (by exact_mod_cast hq_le p) (by linarith)
        exact_mod_cast (hq_prime p).pos
    _ = ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)),
          (S.filter (fun p => absNorm (under ℤ p.asIdeal) = n)).card • ((n : ℝ) ^ (-s)) :=
        Finset.sum_comp (fun n : ℕ => (n : ℝ) ^ (-s)) (fun p : HeightOneSpectrum (𝓞 F) => absNorm (under ℤ p.asIdeal))
    _ ≤ ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)), (Module.finrank ℚ F : ℝ) * ((n : ℝ) ^ (-s)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_primes_over_rational_le F S _ (hq_prime p)
    _ = (Module.finrank ℚ F : ℝ) * ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)), (n : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * 2 ^ (2 - s) := by
        refine mul_le_mul_of_nonneg_left (sum_rpow_neg_le_two_pow _ (fun n hn => ?_) s hs) (by positivity)
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        exact (hq_prime p).two_le

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank_base_field_eq_degree (D : Formalism.BasicNotions.D7) : Module.finrank ℚ D.host.F = D.R.f := by
  exact D.host.finrank_hostF

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem error_sum_le (D : Formalism.BasicNotions.D7) (Ce : ℝ) (hCe : 0 ≤ Ce) (hk : (2 : ℝ) ≤ (D.R.k : ℝ) - 2 * D.R.rS - 3) :
    Formalism.MainNotions.S.eSum D Ce ≤ Ce * ((D.R.f : ℝ) * 2 ^ (2 - ((D.R.k : ℝ) - 2 * D.R.rS - 3))) := by
  unfold Formalism.MainNotions.S.eSum
  refine mul_le_mul_of_nonneg_left ?_ hCe
  have h := prime_ideal_norm_rpow_sum_le D.host.F ((D.R.k : ℝ) - 2 * D.R.rS - 3) hk
  rw [finrank_base_field_eq_degree D] at h
  exact h

end Formalism.MainNotions.BridgeLemma

end
