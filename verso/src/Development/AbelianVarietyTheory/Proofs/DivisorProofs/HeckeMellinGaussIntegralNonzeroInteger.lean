import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeProdNormSqEqAbsNormSpanStatement

noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellinOne

/- English proof (translation)
Establish `hn : ((‖z‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hz`. Establish `hc : starRingEnd ℂ z * z = ((‖z‖ : ℝ) : ℂ) ^ 2`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `GlobalTheory.HeckeTheta.hmon`. Use `split_ifs with h`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le h`. Simplify using `only [Int.toNat_natCast, Int.natAbs_natCast, zpow_neg, zpow_natCast]`. Rewrite using `[← inv_pow, ← mul_pow]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hc`. Take `⟨m, hm⟩ : ∃ m : ℕ, -n = m` from `⟨(-n).toNat, by omega⟩`. Establish `hm' : n.natAbs = m` using `by omega`.

Rewrite using `[hm, hm', Int.toNat_natCast, zpow_natCast, ← mul_pow]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem hmon_eq_mul (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    GlobalTheory.HeckeTheta.hmon n z = ((‖z‖ : ℝ) : ℂ) ^ n.natAbs * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have hc : starRingEnd ℂ z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [Int.toNat_natCast, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
    linear_combination hc
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -n = m := ⟨(-n).toNat, by omega⟩
    have hm' : n.natAbs = m := by omega
    rw [hm, hm', Int.toNat_natCast, zpow_natCast, ← mul_pow]
    congr 1
    field_simp

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]`.
-/
theorem ofReal_prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w = ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

/- English proof (translation)
Substitute `hk` using the available equality. Establish `h2π : 0 < 2 * Real.pi` using `by positivity`. Rewrite using `[Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos h2π, Real.rpow_def_of_pos (by positivity), Real.log_mul h2π.ne' (by positivity), Real.log_pow, ← Real.exp_log (pow_pos hr k), Real.log_pow]`. Establish `key : Real.exp (k * Real.log r) * Real.exp ((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log r) * -(σ + k / 2)) = Real.exp (Real.log (2 * Real.pi) * -(σ + k / 2)) * Real.exp ((2 : ℕ) * Real.log r * -σ)`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `G * key`.
-/
theorem real_factor (r σ a G : ℝ) (k : ℕ) (hr : 0 < r) (hk : (k : ℝ) = a) :
    r ^ k * G * (2 * Real.pi * r ^ 2) ^ (-(σ + a / 2)) =
      (2 * Real.pi) ^ (-(σ + a / 2)) * G * (r ^ 2) ^ (-σ) := by
  subst hk
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos h2π, Real.rpow_def_of_pos (by positivity),
    Real.log_mul h2π.ne' (by positivity), Real.log_pow, ← Real.exp_log (pow_pos hr k), Real.log_pow]
  have key : Real.exp (k * Real.log r) * Real.exp ((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log r) * -(σ + k / 2)) =
      Real.exp (Real.log (2 * Real.pi) * -(σ + k / 2)) * Real.exp ((2 : ℕ) * Real.log r * -σ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  linear_combination G * key

/- English proof (translation)
Establish `hr : 0 < ‖z‖` using `norm_pos_iff.2 hz`. Establish `h2π : 0 < 2 * Real.pi` using `by positivity`. Establish `e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ)` using `by push_cast; ring`. Establish `hk : ((n.natAbs : ℕ) : ℂ) = ((|n| : ℤ) : ℂ)`. Rewrite using `[← Int.cast_natCast, Int.natCast_natAbs]`.

Rewrite using `[hmon_eq_mul n hz, e2, ← Complex.cpow_natCast, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi * ‖z‖ ^ 2).ne'), Complex.cpow_def_of_ne_zero (by exact_mod_cast h2π.ne'), Complex.cpow_def_of …`. Establish `key : Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) * ((|n| : ℤ) : ℂ)) * Complex.exp (((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) = Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) * Complex.exp ((((2 : ℕ) * Real. …`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(2 * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * G) * key`.
-/
theorem complex_factor (z : ℂ) (hz : z ≠ 0) (n : ℤ) (s G : ℂ) :
    2 * (GlobalTheory.HeckeTheta.hmon n z * G *
      ((2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n| : ℤ) : ℂ) / 2))) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n| : ℤ) : ℂ) / 2)) * G *
        ((z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2π : 0 < 2 * Real.pi := by positivity
  have e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hk : ((n.natAbs : ℕ) : ℂ) = ((|n| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  rw [hmon_eq_mul n hz, e2, ← Complex.cpow_natCast,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi * ‖z‖ ^ 2).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast h2π.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < ‖z‖ ^ 2).ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log h2π.le,
    ← Complex.ofReal_log (by positivity), Real.log_mul h2π.ne' (by positivity), Real.log_pow, hk]
  have key : Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) * ((|n| : ℤ) : ℂ)) *
      Complex.exp (((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) *
      Complex.exp ((((2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (2 * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * G) * key

end GlobalTheory.HeckeMellinOne

namespace GlobalTheory.HeckeMellinOne

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, Real.mul_rpow (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]`.
-/
theorem real_prod_rpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℝ) :
    (∏ j ∈ t, f j) ^ w = ∏ j ∈ t, f j ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

/- English proof (translation)
Introduce `K _ _ _ I _ φ hφ n s hs α hα`. Establish `hαK : (α : K) ≠ 0` using `by exact_mod_cast hα`. Establish `hv : ∀ i, GlobalTheory.HeckeTheta.emb φ (α : K) i ≠ 0` using `fun i => (map_ne_zero (φ i)).2 hαK`. Take `⟨hint, hI, hN⟩` from `GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma I n s hs _ hv`. Establish `hnorm` using `GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span K I φ hφ α`.

Use `⟨hint, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hI, ← Complex.ofReal_natCast, ← hnorm, ofReal_prod_cpow _ _ (fun i => by positivity), ← Finset.card_univ, Finset.pow_card_mul_prod]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor GlobalTheory.HeckeStrip.wt`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[complex_factor _ (hv i)]`. Simplify using `only [GlobalTheory.HeckeTheta.emb]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hN, ← hnorm, real_prod_rpow _ _ (fun i => by positivity), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Conclude with `real_factor _ _ _ _ _ (norm_pos_iff.2 (hv i)) (by rw [Nat.cast_natAbs, Int.cast_abs])`.
-/
theorem mellin_term : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  intro K _ _ _ I _ φ hφ n s hs α hα
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  have hv : ∀ i, GlobalTheory.HeckeTheta.emb φ (α : K) i ≠ 0 := fun i => (map_ne_zero (φ i)).2 hαK
  obtain ⟨hint, hI, hN⟩ := GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma I n s hs _ hv
  have hnorm := GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span K I φ hφ α
  refine ⟨hint, ?_, ?_⟩
  · rw [hI, ← Complex.ofReal_natCast, ← hnorm, ofReal_prod_cpow _ _ (fun i => by positivity),
      ← Finset.card_univ, Finset.pow_card_mul_prod]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor GlobalTheory.HeckeStrip.wt
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [complex_factor _ (hv i)]
    simp only [GlobalTheory.HeckeTheta.emb]
    ring
  · rw [hN, ← hnorm, real_prod_rpow _ _ (fun i => by positivity), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact real_factor _ _ _ _ _ (norm_pos_iff.2 (hv i)) (by rw [Nat.cast_natAbs, Int.cast_abs])

end GlobalTheory.HeckeMellinOne
