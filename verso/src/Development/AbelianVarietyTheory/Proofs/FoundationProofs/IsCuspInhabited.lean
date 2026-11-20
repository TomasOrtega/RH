import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletedLaurentQuotPrimeEquivLaurentFp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicElementApproximation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismOnExtensionPointwiseStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismExtensionUniformStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerBasisIndependentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesAlgebraicConstantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueAlgebraicPolynomialDivisibleStatement

noncomputable section

namespace GlobalTheory.Glue.Cusp

open GlobalTheory.K5 GlobalTheory.KZ Polynomial
open scoped NNReal

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
  {v : Valuation Ωl ℝ≥0}

/- English proof (translation)
The claim follows from `(hv _).2 isIntegral_algebraMap`.
-/
theorem v_alg_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (b : O0 p) : v (algebraMap (O0 p) Ωl b) ≤ 1 :=
  (hv _).2 isIntegral_algebraMap

/- English proof (translation)
Take `⟨_, hd, hirr⟩` from `completed_laurent_isDVR p`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Rewrite using `[← Ideal.mem_span_singleton, ← hirr.maximalIdeal_eq]`. Introduce `hu`.

Take `⟨c, hc⟩` from `hu.exists_right_inv`. Establish `h2 : v (algebraMap (O0 p) Ωl b) * v (algebraMap (O0 p) Ωl c) = 1`. Rewrite using `[← map_mul, ← map_mul, hc, map_one, map_one]`. Conclude with `absurd h2 (mul_lt_one_of_nonneg_of_lt_one_left zero_le hb (v_alg_le hv c)).ne`. Introduce and unpack `⟨c, rfl⟩`.

Rewrite using `[map_mul, map_mul, map_natCast]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (v_alg_le hv c)`.
-/
theorem v_alg_lt_iff (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1) (b : O0 p) :
    v (algebraMap (O0 p) Ωl b) < 1 ↔ (p : O0 p) ∣ b := by
  obtain ⟨_, hd, hirr⟩ := completed_laurent_isDVR p
  constructor
  · intro hb
    rw [← Ideal.mem_span_singleton, ← hirr.maximalIdeal_eq]
    intro hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have h2 : v (algebraMap (O0 p) Ωl b) * v (algebraMap (O0 p) Ωl c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_nonneg_of_lt_one_left zero_le hb (v_alg_le hv c)).ne
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_mul, map_natCast]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (v_alg_le hv c)

/- English proof (translation)
Take `⟨e, he⟩` from `exists_completedLaurent_quot_prime_equiv_laurentFp p`. Use `⟨e.toRingHom.comp (Ideal.Quotient.mk _), he, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `e.map_eq_zero_iff`.
-/
theorem exists_red : ∃ φ : O0 p →+* LaurentSeries (ZMod p),
    φ (qO p) = HahnSeries.single (1 : ℤ) (1 : ZMod p) ∧ ∀ b, φ b = 0 ↔ (p : O0 p) ∣ b := by
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk _), he, fun b => ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  exact e.map_eq_zero_iff

/- English proof (translation)
Use `IsIntegral.of_pow (pow_pos hp.out.pos n) ?_` and prove the remaining obligations. Rewrite using `[Basic.qq_pow]`. Conclude with `isIntegral_algebraMap`.
-/
theorem isInt_qq (T : K5.Tower p Ωl) (n : ℕ) : IsIntegral (O0 p) (T.qq n) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos n) ?_
  rw [Basic.qq_pow]
  exact isIntegral_algebraMap

/- English proof (translation)
The claim follows from `(hv _).2 (IsIntegral.of_mem_of_fg _ (isInt_qq T n).fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _))`.
-/
theorem v_aeval_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) :
    v (aeval (T.qq n) f) ≤ 1 :=
  (hv _).2 (IsIntegral.of_mem_of_fg _ (isInt_qq T n).fg_adjoin_singleton _
    (aeval_mem_adjoin_singleton _ _))

/- English proof (translation)
Take `⟨φ, hq, hφ⟩` from `exists_red (p := p)`. Establish `h2` using `GlobalTheory.T.frobenius_power_reduction_congruence p Ωl h v hv h1 T n f hf`. Establish `h3 : v (aeval (T.qq n) f ^ (p ^ n)) < 1`. Rewrite using `[map_pow]`. Conclude with `pow_lt_one₀ zero_le hlt (pow_pos hp.out.pos n).ne'`.

Establish `h4` using `v.map_sub_lt h3 h2`. Rewrite `h4` using `[sub_sub_cancel, v_alg_lt_iff hv h1, ← hφ]`. Simplify using `only [map_sum, map_mul, map_pow, hq] at h4`. Establish `h5` using `GlobalTheory.T.frobenius_power_basis_independent p n (fun i => φ (f.coeff i)) h4`. Rewrite using `[C_dvd_iff_dvd_coeff]`.

Introduce `i`. Distinguish the cases in `hi : i < p ^ n`. Conclude with `(hφ _).1 (h5 i hi)`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _`.
-/
theorem orth (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (hlt : v (aeval (T.qq n) f) < 1) : C (p : O0 p) ∣ f := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.T.frobenius_power_reduction_congruence p Ωl h v hv h1 T n f hf
  have h3 : v (aeval (T.qq n) f ^ (p ^ n)) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le hlt (pow_pos hp.out.pos n).ne'
  have h4 := v.map_sub_lt h3 h2
  rw [sub_sub_cancel, v_alg_lt_iff hv h1, ← hφ] at h4
  simp only [map_sum, map_mul, map_pow, hq] at h4
  have h5 := GlobalTheory.T.frobenius_power_basis_independent p n (fun i => φ (f.coeff i)) h4
  rw [C_dvd_iff_dvd_coeff]
  intro i
  by_cases hi : i < p ^ n
  · exact (hφ _).1 (h5 i hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _

/- English proof (translation)
Take `⟨φ, hq, hφ⟩` from `exists_red (p := p)`. Establish `h2` using `GlobalTheory.T.frobenius_power_reduction_congruence p Ωl h v hv h1 T n f hf`. Establish `hy` using `v_aeval_le hv T n f`. Use `set y := aeval (T.qq n) f`. Use `set b := ∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i`.

Take `⟨P, hP0, hP⟩` from `GlobalTheory.T.residue_algebraic_polynomial_divisible p Ωl h v hv h1 (y ^ p ^ n) b (halg.pow _) (by rw [map_pow]; exact pow_le_one₀ zero_le hy) h2`. Take `⟨c, hc⟩` from `GlobalTheory.T.laurent_series_algebraic_constant (ZMod p) (φ b) ⟨_, hP0, by`. Rewrite using `[← (hφ _).2 hP, eval₂_map, aeval_def, hom_eval₂]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _⟩`.

Take `⟨m, rfl⟩` from `ZMod.intCast_surjective c`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `h3 : v (algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n)) < 1`. Rewrite using `[v_alg_lt_iff hv h1, ← hφ, map_sub, hc, map_pow φ, map_intCast φ, ← map_intCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p)), ← map_pow, ZMod.pow_card_pow, sub_self]`. Establish `hm : v (m : Ωl) ≤ 1` using `(hv _).2 (Basic.isInt_intCast m)`.

Set `y' : v.integer` to `⟨y - m, v.map_sub_le hy hm⟩`. Take `⟨r, hr⟩` from `exists_add_pow_prime_pow_eq hp.out y' (m : v.integer) n`. Establish `hr'` using `congrArg (Subtype.val) hr`. Simplify using `only [y'] at hr'`. Move the coercions through the operations in `at hr'`.

Establish `h4 : v ((p : Ωl) * (y - m) * m * r) < 1`. Rewrite using `[mul_assoc, mul_assoc, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (y' * ((m : v.integer) * r)).2`. Establish `h5` using `v.map_sub_lt (v.map_add_lt h2 h3) h4`. Establish `h6 : y ^ p ^ n - algebraMap (O0 p) Ωl b + algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n) - (p : Ωl) * (y - m) * m * r = (y - m) ^ p ^ n`.

Rewrite using `[map_sub, map_pow, map_intCast]`. Rewrite `hr'` using `[sub_add_cancel]`. Take the linear combination `hr'`. Rewrite `h5` using `[h6, map_pow]`. Conclude with `lt_of_pow_lt_pow_left₀ (p ^ n) zero_le_one (by rwa [one_pow])`.
-/
theorem res (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (halg : IsAlgebraic ℤ (aeval (T.qq n) f)) : ∃ m : ℤ, v (aeval (T.qq n) f - m) < 1 := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.T.frobenius_power_reduction_congruence p Ωl h v hv h1 T n f hf
  have hy := v_aeval_le hv T n f
  set y := aeval (T.qq n) f
  set b := ∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.T.residue_algebraic_polynomial_divisible p Ωl h v hv h1 (y ^ p ^ n) b (halg.pow _)
    (by rw [map_pow]; exact pow_le_one₀ zero_le hy) h2
  obtain ⟨c, hc⟩ := GlobalTheory.T.laurent_series_algebraic_constant (ZMod p) (φ b) ⟨_, hP0, by
    rw [← (hφ _).2 hP, eval₂_map, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨m, ?_⟩
  have h3 : v (algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n)) < 1 := by
    rw [v_alg_lt_iff hv h1, ← hφ, map_sub, hc, map_pow φ, map_intCast φ,
      ← map_intCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p)), ← map_pow, ZMod.pow_card_pow, sub_self]
  have hm : v (m : Ωl) ≤ 1 := (hv _).2 (Basic.isInt_intCast m)
  let y' : v.integer := ⟨y - m, v.map_sub_le hy hm⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out y' (m : v.integer) n
  have hr' := congrArg (Subtype.val) hr
  simp only [y'] at hr'
  push_cast at hr'
  have h4 : v ((p : Ωl) * (y - m) * m * r) < 1 := by
    rw [mul_assoc, mul_assoc, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (y' * ((m : v.integer) * r)).2
  have h5 := v.map_sub_lt (v.map_add_lt h2 h3) h4
  have h6 : y ^ p ^ n - algebraMap (O0 p) Ωl b + algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n) -
      (p : Ωl) * (y - m) * m * r = (y - m) ^ p ^ n := by
    rw [map_sub, map_pow, map_intCast]
    rw [sub_add_cancel] at hr'
    linear_combination hr'
  rw [h6, map_pow] at h5
  exact lt_of_pow_lt_pow_left₀ (p ^ n) zero_le_one (by rwa [one_pow])

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

/- English proof (translation)
Use `haveI := Basic.charZero_of_isClo h`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `f a _ ha`.

Establish `h2` using `v_aeval_le hv T n f`. Rewrite `h2` using `[ha]`. Rewrite using `[map_sub, pow_zero]`. Conclude with `v.map_sub_le (hs a h2) h2`. Consider the case `succ N ih`.

Introduce `f a hf ha`. Establish `halg : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨m, hm⟩` from `res h hv h1 T n f hf (ha ▸ halg.algHom j.toIntAlgHom)`. Establish `hf' : (f - C (m : O0 p)).natDegree < p ^ n` using `by rwa [natDegree_sub_C]`. Take `⟨g, hg⟩` from `orth h hv h1 T n _ hf' (by simpa using hm)`.

Establish `hp0 : (p : Ω) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Establish `hpl : (p : Ωl) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Establish `hpO : (p : O0 p) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Establish `h3` using `ih g ((a - m) / p) (by rwa [hg, natDegree_C_mul hpO] at hf') (by`. Use `congrArg (aeval (T.qq n)) hg` as an intermediate fact.

Simplify using `only [map_sub, map_mul, aeval_C, map_intCast, map_natCast, ha] at this`. Rewrite using `[map_div₀, map_sub, map_intCast, map_natCast, this, mul_div_cancel_left₀ _ hpl])`. Establish `h4 : s a - a = p * (s ((a - m) / p) - (a - m) / p)`. Rewrite using `[map_div₀, map_sub, map_intCast, map_natCast]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, map_mul, map_mul, map_natCast, pow_succ']`. Conclude with `mul_le_mul_right h3 _`.
-/
theorem approx (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (N : ℕ) : ∀ (f : (O0 p)[X]) (a : Ω), f.natDegree < p ^ n → aeval (T.qq n) f = j a →
      v (j (s a - a)) ≤ v (p : Ωl) ^ N := by
  haveI := Basic.charZero_of_isClo h
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction N with
  | zero =>
    intro f a _ ha
    have h2 := v_aeval_le hv T n f
    rw [ha] at h2
    rw [map_sub, pow_zero]
    exact v.map_sub_le (hs a h2) h2
  | succ N ih =>
    intro f a hf ha
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨m, hm⟩ := res h hv h1 T n f hf (ha ▸ halg.algHom j.toIntAlgHom)
    have hf' : (f - C (m : O0 p)).natDegree < p ^ n := by rwa [natDegree_sub_C]
    obtain ⟨g, hg⟩ := orth h hv h1 T n _ hf' (by simpa using hm)
    have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpl : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpO : (p : O0 p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h3 := ih g ((a - m) / p) (by rwa [hg, natDegree_C_mul hpO] at hf') (by
      have := congrArg (aeval (T.qq n)) hg
      simp only [map_sub, map_mul, aeval_C, map_intCast, map_natCast, ha] at this
      rw [map_div₀, map_sub, map_intCast, map_natCast, this, mul_div_cancel_left₀ _ hpl])
    have h4 : s a - a = p * (s ((a - m) / p) - (a - m) / p) := by
      rw [map_div₀, map_sub, map_intCast, map_natCast]; field_simp; ring
    rw [h4, map_mul, map_mul, map_natCast, pow_succ']
    exact mul_le_mul_right h3 _

/- English proof (translation)
Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Take `⟨_, hdv, hirr⟩` from `completed_laurent_isDVR p`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hirr`. Establish `hpos` using `pow_pos hp.out.pos n`. Establish `hmon : (X ^ (p ^ n) - C (qO p)).Monic` using `monic_X_pow_sub_C _ hpos.ne'`.

Establish `hdeg : ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))).natDegree < p ^ n`. Use `natDegree_modByMonic_lt (C (↑u⁻¹ : O0 p) * f) hmon (fun h0 => by` as an intermediate fact. Use `congrArg natDegree h0` as an intermediate fact. Rewrite `this` using `[natDegree_X_pow_sub_C, natDegree_one]`. Use the proof step `omega)`.

Rewrite `this` using `[natDegree_X_pow_sub_C]`. Then use the resulting hypothesis. Establish `hev : aeval (T.qq n) ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))) = j ((p : Ω) ^ m * a)`. Rewrite using `[aeval_modByMonic_eq_self_of_root (by simp [Basic.qq_pow]), map_mul, aeval_C, ha, ← mul_assoc, ← map_mul, Units.inv_mul_cancel_left]`. Simplify using the standard rewrite rules. Establish `h0 : v (j (s ((p : Ω) ^ m * a) - (p : Ω) ^ m * a)) = 0`.

Assume the negation of the conclusion as `hne`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (pos_iff_ne_zero.2 hne) h1`. Conclude with `absurd (approx h hv h1 T n j s hs N _ _ hdeg hev) (not_le.2 hN)`. Rewrite `h0` using `[v.zero_iff, map_eq_zero, sub_eq_zero, map_mul, map_pow, map_natCast]`. Conclude with `mul_left_cancel₀ (pow_ne_zero m (by exact_mod_cast hp.out.ne_zero)) h0`.
-/
theorem fixed (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (f : (O0 p)[X]) (d : O0 p) (hd : d ≠ 0) (a : Ω)
    (ha : aeval (T.qq n) f = algebraMap (O0 p) Ωl d * j a) : s a = a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨_, hdv, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hirr
  have hpos := pow_pos hp.out.pos n
  have hmon : (X ^ (p ^ n) - C (qO p)).Monic := monic_X_pow_sub_C _ hpos.ne'
  have hdeg : ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))).natDegree < p ^ n := by
    have := natDegree_modByMonic_lt (C (↑u⁻¹ : O0 p) * f) hmon (fun h0 => by
      have := congrArg natDegree h0
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      omega)
    rwa [natDegree_X_pow_sub_C] at this
  have hev : aeval (T.qq n) ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))) = j ((p : Ω) ^ m * a) := by
    rw [aeval_modByMonic_eq_self_of_root (by simp [Basic.qq_pow]), map_mul, aeval_C, ha, ← mul_assoc,
      ← map_mul, Units.inv_mul_cancel_left]
    simp
  have h0 : v (j (s ((p : Ω) ^ m * a) - (p : Ω) ^ m * a)) = 0 := by
    by_contra hne
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.2 hne) h1
    exact absurd (approx h hv h1 T n j s hs N _ _ hdeg hev) (not_le.2 hN)
  rw [v.zero_iff, map_eq_zero, sub_eq_zero, map_mul, map_pow, map_natCast] at h0
  exact mul_left_cancel₀ (pow_ne_zero m (by exact_mod_cast hp.out.ne_zero)) h0

/- English proof (translation)
Use `haveI := h.clo`. Use `haveI := h.alg`. Use `haveI := Basic.charZero_of_isClo h`. Use `haveI : FaithfulSMul (O0 p) Ωl := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj`. Use `letI : Algebra (FractionRing (O0 p)) Ωl := FractionRing.liftAlgebra (O0 p) Ωl`.

Use `haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ωl := FractionRing.isScalarTower_liftAlgebra _ _`. Use `haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ωl := (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).1 h.alg`. Set `K` to `IntermediateField.adjoin (FractionRing (O0 p)) {T.qq n}`. Establish `hfix : ∀ a : Ω, j a ∈ Set.range (algebraMap K Ωl) → s a = a`. Introduce and unpack `a ⟨⟨y, hy⟩, rfl : y = j a⟩`.

Rewrite `hy` using `[← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨f, hf⟩` from `hy`. Take `⟨d, hd, hdf⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors (O0 p)) f`. Use `fixed h hv h1 T n j s hs (IsLocalization.integerNormalization (nonZeroDivisors (O0 p)) f) d (nonZeroDivisors.ne_zero hd) a ?_` and prove the remaining obligations. Rewrite using `[← aeval_map_algebraMap (FractionRing (O0 p)), hdf, ← Algebra.smul_def, ← hf, ← algebraMap_smul (FractionRing (O0 p)) d f, map_smul, algebraMap_smul]`.

Both sides reduce to the same expression. Take `⟨g, hg⟩` from `GlobalTheory.T.automorphism_extension_uniform Ω Ωl K j s (GlobalTheory.T.automorphism_on_extension_pointwise Ω Ωl K j s hfix)`. Use `⟨(g.restrictScalars (FractionRing (O0 p))).restrictScalars (O0 p), ?_, hg⟩` and prove the remaining obligations. Conclude with `g.commutes ⟨T.qq n, IntermediateField.mem_adjoin_simple_self _ _⟩`.
-/
theorem up (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  haveI := h.clo
  haveI := h.alg
  haveI := Basic.charZero_of_isClo h
  haveI : FaithfulSMul (O0 p) Ωl := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
  letI : Algebra (FractionRing (O0 p)) Ωl := FractionRing.liftAlgebra (O0 p) Ωl
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ωl := FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ωl :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).1 h.alg
  let K := IntermediateField.adjoin (FractionRing (O0 p)) {T.qq n}
  have hfix : ∀ a : Ω, j a ∈ Set.range (algebraMap K Ωl) → s a = a := by
    rintro a ⟨⟨y, hy⟩, rfl : y = j a⟩
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, hf⟩ := hy
    obtain ⟨d, hd, hdf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (O0 p)) f
    refine fixed h hv h1 T n j s hs
      (IsLocalization.integerNormalization (nonZeroDivisors (O0 p)) f) d (nonZeroDivisors.ne_zero hd) a ?_
    rw [← aeval_map_algebraMap (FractionRing (O0 p)), hdf, ← Algebra.smul_def, ← hf,
      ← algebraMap_smul (FractionRing (O0 p)) d f, map_smul, algebraMap_smul]
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.T.automorphism_extension_uniform Ω Ωl K j s (GlobalTheory.T.automorphism_on_extension_pointwise Ω Ωl K j s hfix)
  refine ⟨(g.restrictScalars (FractionRing (O0 p))).restrictScalars (O0 p), ?_, hg⟩
  exact g.commutes ⟨T.qq n, IntermediateField.mem_adjoin_simple_self _ _⟩

end Local

end GlobalTheory.Glue.Cusp
