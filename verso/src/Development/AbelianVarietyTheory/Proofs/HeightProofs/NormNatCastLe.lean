import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

namespace GlobalTheory.AdicNormZpowEstimates

open IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h0 : Valued.v y ≠ 0` using `by simpa using hy`. Rewrite using `[FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]`. Conclude with `⟨_, by push_cast; rfl⟩`.
-/
theorem norm_eq_zpow (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F)
    (hy : y ≠ 0) : ∃ k : ℤ, ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v y ≠ 0 := by simpa using hy
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  exact ⟨_, by push_cast; rfl⟩

/- English proof (translation)
Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm v` after adjusting the coercions.
-/
theorem one_lt_norm (v : HeightOneSpectrum (RingOfIntegers F)) :
    (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

/- English proof (translation)
Establish `h1` using `one_lt_norm v`. Distinguish the cases in `hy : y = 0`. Rewrite using `[hy, norm_zero]`. Check the signs of the components of the expression. Take `⟨k, hk⟩` from `norm_eq_zpow v y hy`.

Rewrite `h`, the goal using `[hk]`. Rewrite `h` using `[zpow_lt_zpow_iff_right₀ h1]`. Conclude with `zpow_le_zpow_right₀ h1.le (by omega)`.
-/
theorem norm_le_of_lt (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F) (m : ℤ)
    (h : ‖y‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ (m + 1)) :
    ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  have h1 := one_lt_norm v
  by_cases hy : y = 0
  · rw [hy, norm_zero]
    positivity
  · obtain ⟨k, hk⟩ := norm_eq_zpow v y hy
    rw [hk] at h ⊢
    rw [zpow_lt_zpow_iff_right₀ h1] at h
    exact zpow_le_zpow_right₀ h1.le (by omega)

/- English proof (translation)
Rewrite using `[map_natCast, map_natCast]`.
-/
theorem natCast_eq (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    (n : v.adicCompletion F)
      = FinitePlace.embedding v (algebraMap (RingOfIntegers F) F (n : RingOfIntegers F)) := by
  rw [map_natCast, map_natCast]

/- English proof (translation)
Rewrite using `[natCast_eq]`. Conclude with `FinitePlace.norm_le_one F v _`.
-/
theorem norm_natCast_le (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  rw [natCast_eq]
  exact FinitePlace.norm_le_one F v _

/- English proof (translation)
Use `norm_le_of_lt v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) (-1) (by` as an intermediate fact. Rewrite using `[natCast_eq, neg_add_cancel, zpow_zero, FinitePlace.norm_lt_one_iff_mem]`. Conclude with `Ideal.absNorm_mem _)`. Simplify using `using this`.
-/
theorem norm_absNorm_le (v : HeightOneSpectrum (RingOfIntegers F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖
      ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have := norm_le_of_lt v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) (-1) (by
    rw [natCast_eq, neg_add_cancel, zpow_zero, FinitePlace.norm_lt_one_iff_mem]
    exact Ideal.absNorm_mem _)
  simpa using this

/- English proof (translation)
Establish `hn : ∀ v : HeightOneSpectrum (RingOfIntegers F), ∃ n : ℕ, (Ideal.absNorm v.asIdeal : ℝ) ^ n ≤ H v ∧ (H v : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (n + 1)` using `fun v => exists_nat_pow_near (by exact_mod_cast h1 v) (one_lt_norm v)`. Use `choose n hle hlt using hn`. Use `⟨∏ v ∈ hfin.toFinset, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Finset.prod_pos fun v _ => pow_pos ?_ _` and prove the remaining obligations. Conclude with `lt_trans Nat.one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)`.

Rewrite using `[finprod_eq_prod_of_mulSupport_subset H (s := hfin.toFinset) (by simp), Nat.cast_prod]`. Use `Finset.prod_le_prod' fun v _ => ?_` and prove the remaining obligations. Use `hle v` as an intermediate fact. Conclude with `this` after adjusting the coercions. Introduce `v y hy`.

Establish `hy' : ‖y‖ ≤ (H v : ℝ)` using `by exact_mod_cast hy`. Rewrite using `[norm_mul]`. Distinguish the cases in `hv : v ∈ hfin.toFinset`. Establish `hq` using `one_lt_norm v`. Establish `hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)` using `lt_trans one_pos hq`.

Establish `h2 : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n v`. Use `norm_le_of_lt v y (n v) (by` as an intermediate fact. Use `lt_of_le_of_lt hy' (hlt v)` as an intermediate fact. Conclude with `this)` after adjusting the coercions. Simplify using `using this`.

Rewrite using `[← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]`. Establish `h3 : ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ n v ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v` using `pow_le_pow_left₀ (norm_nonneg _) (norm_absNorm_le v) _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one, ← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]`. Establish `h2 : H v = 1` using `by simpa using hv`.

Rewrite `hy'` using `[h2]`. Conclude with `mul_le_one₀ (norm_natCast_le v _) (norm_nonneg _) (by simpa using hy')`.
-/
theorem exists_denominator {F : Type} [Field F] [NumberField F]
    (H : HeightOneSpectrum (RingOfIntegers F) → NNReal) (h1 : ∀ v, (1 : NNReal) ≤ H v)
    (hfin : Set.Finite (Function.mulSupport H)) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F),
        ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ (1 : ℝ) := by
  classical
  have hn : ∀ v : HeightOneSpectrum (RingOfIntegers F), ∃ n : ℕ,
      (Ideal.absNorm v.asIdeal : ℝ) ^ n ≤ H v ∧ (H v : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (n + 1) :=
    fun v => exists_nat_pow_near (by exact_mod_cast h1 v) (one_lt_norm v)
  choose n hle hlt using hn
  refine ⟨∏ v ∈ hfin.toFinset, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_, ?_⟩
  · refine Finset.prod_pos fun v _ => pow_pos ?_ _
    exact lt_trans Nat.one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  · rw [finprod_eq_prod_of_mulSupport_subset H (s := hfin.toFinset) (by simp), Nat.cast_prod]
    refine Finset.prod_le_prod' fun v _ => ?_
    have := hle v
    exact_mod_cast this
  · intro v y hy
    have hy' : ‖y‖ ≤ (H v : ℝ) := by exact_mod_cast hy
    rw [norm_mul]
    by_cases hv : v ∈ hfin.toFinset
    · have hq := one_lt_norm v
      have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans one_pos hq
      have h2 : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n v := by
        have := norm_le_of_lt v y (n v) (by
          have := lt_of_le_of_lt hy' (hlt v)
          exact_mod_cast this)
        simpa using this
      rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
      have h3 : ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ n v
          ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_absNorm_le v) _
      calc _ ≤ (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v * 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ n v :=
            mul_le_mul (mul_le_mul h3 (norm_natCast_le v _) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [mul_one, ← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]
    · have h2 : H v = 1 := by simpa using hv
      rw [h2] at hy'
      exact mul_le_one₀ (norm_natCast_le v _) (norm_nonneg _) (by simpa using hy')

end GlobalTheory.AdicNormZpowEstimates
