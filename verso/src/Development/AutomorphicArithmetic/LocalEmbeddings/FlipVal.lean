import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Development.AutomorphicArithmetic.DivisorFrames.ExistsPowLocKMulInfEqOneOfLevelLeTwo
import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralCmTypeUnitaryPartMulAbsNormPow
open NumberField IsDedekindDomain
open Formalism.DivisionValues (vw)

namespace UpperTheory.FlipVal

/- English proof (translation)
Establish `hq' : (q : K) ≠ 0` using `by exact_mod_cast hq`. Establish `h0 : 0 ≤ vw w ((q : K) ^ n * y)`. Take `⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (q : K) ^ n * y` from `⟨⟨_, h⟩, rfl⟩`. Rewrite using `[← ha, vw, ← FractionalIdeal.coeIdeal_span_singleton]`. Conclude with `FractionalIdeal.count_coe_nonneg K w _`.

Rewrite `h0` using `[vw, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_mul K w (pow_ne_zero _ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hq')) (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy), FractionalIdeal.count_pow]`. Unfold `vw`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vw_ge {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) {q : ℕ} (hq : q ≠ 0)
    (n : ℕ) (h : IsIntegral ℤ ((q : K) ^ n * y)) : -((n : ℤ) * vw w (q : K)) ≤ vw w y := by
  have hq' : (q : K) ≠ 0 := by exact_mod_cast hq
  have h0 : 0 ≤ vw w ((q : K) ^ n * y) := by
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (q : K) ^ n * y := ⟨⟨_, h⟩, rfl⟩
    rw [← ha, vw, ← FractionalIdeal.coeIdeal_span_singleton]
    exact FractionalIdeal.count_coe_nonneg K w _
  rw [vw, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow,
    FractionalIdeal.count_mul K w (pow_ne_zero _ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hq'))
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy), FractionalIdeal.count_pow] at h0
  unfold vw
  linarith

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton]`. Conclude with `FractionalIdeal.count_coe_nonneg K w _`.
-/
theorem vw_nat_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (q : ℕ) : 0 ≤ vw w (q : K) := by
  rw [← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

/- English proof (translation)
Establish `hfin : Finite (𝓞 E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`. Establish `hmax` using `P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Use `letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)`. Take `⟨n, -, hn⟩` from `FiniteField.card (𝓞 E ⧸ P.asIdeal) (ringChar (𝓞 E ⧸ P.asIdeal))`.

Establish `h1 : Ideal.absNorm P.asIdeal = Formalism.EigenvalueLevelCeiling.plc P ^ (n : ℕ)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]`. Both sides reduce to the same expression. Establish `h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ∉ w.asIdeal`. Rewrite using `[h1, Nat.cast_pow]`.

Conclude with `fun h' => h (w.isPrime.mem_of_pow_mem _ h')`. Establish `h3 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ≠ 0` using `fun h' => h2 (h' ▸ zero_mem _)`. Rewrite using `[← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w (by simpa using h3)]`. Assume the negation of the conclusion as `h4`. Use `h2 ((Ideal.dvd_span_singleton).1 ?_)` and prove the remaining obligations.

Conclude with `(Associates.count_ne_zero_iff_dvd (by simpa using h3) w.irreducible).1 (by exact_mod_cast h4)`.
-/
theorem vw_absNorm {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (h : ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    vw w ((Ideal.absNorm P.asIdeal : ℕ) : K) = 0 := by
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hmax := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ P.asIdeal) (ringChar (𝓞 E ⧸ P.asIdeal))
  have h1 : Ideal.absNorm P.asIdeal = Formalism.EigenvalueLevelCeiling.plc P ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]; rfl
  have h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    rw [h1, Nat.cast_pow]; exact fun h' => h (w.isPrime.mem_of_pow_mem _ h')
  have h3 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ≠ 0 := fun h' => h2 (h' ▸ zero_mem _)
  rw [← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w (by simpa using h3)]
  by_contra h4
  refine h2 ((Ideal.dvd_span_singleton).1 ?_)
  exact (Associates.count_ne_zero_iff_dvd (by simpa using h3) w.irreducible).1 (by exact_mod_cast h4)

/- English proof (translation)
Take `⟨h, z, h0, hP, hQ, H⟩` from `UpperTheory.exists_pow_locK_mul_inf_eq_one_of_levelLe_two E χ S hS hl P (Formalism.L2.Host.unif P)`. Establish `hu : P.valuation E (Formalism.L2.Host.unif P : E) = WithZero.exp (-1 : ℤ)` using `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm.trans (Formalism.L2.Host.unif_spec P)`. Rewrite `hP` using `[hu, ← WithZero.exp_nsmul, show h • (-1 : ℤ) = -(h : ℤ) by simp]`. Establish `H' : (χ.val P : ℂ) ^ h * ∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i = 1`. Rewrite using `[← hn z]`.

Conclude with `congrArg Units.val H`. Prove the components needed by the constructor for the conclusion. Use `IsIntegral.of_pow h0 ?_` and prove the remaining obligations. Use `UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ (fun i => -n i) M (fun i => by simpa using hM i) P h z hP hQ` as an intermediate fact. Simplify using `only [zpow_neg, Finset.prod_inv_distrib] at this`.

Rewrite `this` using `[← eq_inv_of_mul_eq_one_left H', mul_comm, mul_comm h, pow_mul, ← mul_pow]`. Then use the resulting hypothesis. Use `IsIntegral.of_pow h0 ?_` and prove the remaining obligations. Use `UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ n M hM P h z hP hQ` as an intermediate fact. Rewrite `this` using `[eq_inv_of_mul_eq_one_right H', mul_comm, mul_comm h, pow_mul, ← inv_pow, ← mul_pow]`. Then use the resulting hypothesis.
-/
theorem val_int {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ v, v ∉ S → χ.UnrAt v) (hl : ∀ v, χ.LevelLe v 2) {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Injective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i))) (n : I → ℤ) (hn : χ.HasInf φ n)
    (M : ℕ) (hM : ∀ i, (n i).natAbs ≤ M) (P : HeightOneSpectrum (𝓞 E)) :
    IsIntegral ℤ (((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ M * (χ.val P : ℂ)) ∧
      IsIntegral ℤ (((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ M * (χ.val P : ℂ)⁻¹) := by
  obtain ⟨h, z, h0, hP, hQ, H⟩ := UpperTheory.exists_pow_locK_mul_inf_eq_one_of_levelLe_two E χ S hS hl P (Formalism.L2.Host.unif P)
  have hu : P.valuation E (Formalism.L2.Host.unif P : E) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm.trans (Formalism.L2.Host.unif_spec P)
  rw [hu, ← WithZero.exp_nsmul, show h • (-1 : ℤ) = -(h : ℤ) by simp] at hP
  have H' : (χ.val P : ℂ) ^ h * ∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i = 1 := by
    rw [← hn z]; exact congrArg Units.val H
  constructor
  · refine IsIntegral.of_pow h0 ?_
    have := UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ (fun i => -n i) M (fun i => by simpa using hM i) P h z hP hQ
    simp only [zpow_neg, Finset.prod_inv_distrib] at this
    rwa [← eq_inv_of_mul_eq_one_left H', mul_comm, mul_comm h, pow_mul, ← mul_pow] at this
  · refine IsIntegral.of_pow h0 ?_
    have := UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ n M hM P h z hP hQ
    rwa [eq_inv_of_mul_eq_one_right H', mul_comm, mul_comm h, pow_mul, ← inv_pow, ← mul_pow] at this

end UpperTheory.FlipVal
