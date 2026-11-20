import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PDifferentExtNorm
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PRootsOfUnityValuation
open NumberField IsDedekindDomain

noncomputable section
namespace LevelTowerAlt.LocalPrimeBound

section Dvr

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

/- English proof (translation)
Establish `hmax : IsLocalRing.maximalIdeal V ≠ ⊥` using `IsDiscreteValuationRing.not_a_field V`. Set `P : HeightOneSpectrum V` to `⟨IsLocalRing.maximalIdeal V, (IsLocalRing.maximalIdeal.isMaximal V).isPrime, hmax⟩`. Establish `hP : ∀ w : HeightOneSpectrum V, w = P` using `fun w => HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal (w.isPrime.isMaximal w.ne_bot))`. Establish `he : (1 : NNReal) < 2` using `one_lt_two`. Set `f` to `WithZeroMulInt.toNNReal he.ne_zero`.

Establish `hf : StrictMono f` using `WithZeroMulInt.toNNReal_strictMono he`. Use `⟨(P.valuation K).map f hf.monotone, ⟨IsFractionRing.injective V K, fun x => ?_, fun r hr => ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Valuation.map_apply, ← map_one f]`. Conclude with `hf.monotone (P.valuation_le_one (K := K) x)`. Rewrite `hr` using `[Valuation.map_apply, ← map_one f]`.

Establish `hr' : P.valuation K r ≤ 1` using `hf.le_iff_le.1 hr`. Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (K := K) (x := r) (h := fun w => by rw [hP w]; exact hr')`. Conclude with `⟨y, hy⟩`. Rewrite using `[Valuation.map_apply, ← map_one f]`. Conclude with `hf ((P.valuation_lt_one_iff_mem (K := K) x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx))`.
-/
theorem exists_val : ∃ v : Valuation K NNReal, v.Integers V ∧ ∀ x : V, ¬ IsUnit x → v (algebraMap V K x) < 1 := by
  have hmax : IsLocalRing.maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let P : HeightOneSpectrum V :=
    ⟨IsLocalRing.maximalIdeal V, (IsLocalRing.maximalIdeal.isMaximal V).isPrime, hmax⟩
  have hP : ∀ w : HeightOneSpectrum V, w = P := fun w =>
    HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal (w.isPrime.isMaximal w.ne_bot))
  have he : (1 : NNReal) < 2 := one_lt_two
  let f := WithZeroMulInt.toNNReal he.ne_zero
  have hf : StrictMono f := WithZeroMulInt.toNNReal_strictMono he
  refine ⟨(P.valuation K).map f hf.monotone,
    ⟨IsFractionRing.injective V K, fun x => ?_, fun r hr => ?_⟩, fun x hx => ?_⟩
  · rw [Valuation.map_apply, ← map_one f]
    exact hf.monotone (P.valuation_le_one (K := K) x)
  · rw [Valuation.map_apply, ← map_one f] at hr
    have hr' : P.valuation K r ≤ 1 := hf.le_iff_le.1 hr
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := K) (x := r)
      (h := fun w => by rw [hP w]; exact hr')
    exact ⟨y, hy⟩
  · rw [Valuation.map_apply, ← map_one f]
    exact hf ((P.valuation_lt_one_iff_mem (K := K) x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx))

end Dvr

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `hnormZ : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 L)}) = m ^ Module.finrank ℚ L`. Introduce `m`. Rewrite using `[Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)) m, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]`. Simplify using the standard rewrite rules. Establish `hd : (0 : ℝ) ≤ Module.finrank ℚ L` using `Nat.cast_nonneg _`.

Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `ht : 0 ≤ Real.log p / ((p : ℝ) - 1)` using `div_nonneg (Real.log_nonneg hp1.le) (by linarith)`. Distinguish the cases in `h2' : p = 2`. Substitute `h2'` using the available equality. Use `⟨4, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h2 rfl]`. Conclude with `map_ofNat _ 4`. Introduce `h`. Establish `h4` using `congrArg (algebraMap (𝓞 L) L) h`. Rewrite `h4` using `[map_ofNat, map_zero]`.

Evaluate the numerical expressions using `at h4`. Rewrite using `[show (4 : 𝓞 L) = ((4 : ℕ) : 𝓞 L) by norm_num, hnormZ, Nat.cast_pow, Real.log_pow]`. Establish `h4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2`. Rewrite using `[show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Evaluate the numerical expressions.

Rewrite using `[h4]`. Evaluate the numerical expressions. Establish `hζ : IsPrimitiveRoot (r + 1) p` using `hodd h2'`. Set `ζ : 𝓞 L` to `⟨r + 1, hζ.isIntegral hp.pos⟩`. Establish `hζ' : IsPrimitiveRoot ζ p` using `IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective`.

Use `⟨ζ - 1, ?_, sub_ne_zero.2 (hζ'.ne_one hp.one_lt), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_one]`. Conclude with `add_sub_cancel_right r 1`. Establish `hassoc` using `GroundTheory.Heights₂.Heights.RootsOfUnityValuation.one_sub_pow_associated hp hζ'`. Establish `hsp : Ideal.span {ζ - 1} = Ideal.span {1 - ζ}`.

Rewrite using `[← neg_sub, Ideal.span_singleton_neg]`. Establish `hN : Ideal.absNorm (Ideal.span {ζ - 1}) ^ (p - 1) = p ^ Module.finrank ℚ L`. Rewrite using `[← hnormZ, ← Ideal.span_singleton_eq_span_singleton.2 hassoc, ← Ideal.span_singleton_pow, map_pow, hsp]`. Establish `hNr : (Ideal.absNorm (Ideal.span {ζ - 1}) : ℝ) ^ (p - 1) = (p : ℝ) ^ Module.finrank ℚ L`. Conclude with `hN` after adjusting the coercions.

Establish `hlog` using `congrArg Real.log hNr`. Rewrite `hlog` using `[Real.log_pow, Real.log_pow, Nat.cast_sub hp.one_le, Nat.cast_one]`. Establish `hpos : (0 : ℝ) < (p : ℝ) - 1` using `by linarith`. Establish `hL : Real.log (Ideal.absNorm (Ideal.span {ζ - 1})) = Module.finrank ℚ L * (Real.log p / ((p : ℝ) - 1))`. Rewrite using `[← mul_div_assoc, eq_div_iff hpos.ne']`.

Take the linear combination `hlog`. Rewrite using `[hL]`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) hd`.
-/
theorem const_int {p : ℕ} (hp : p.Prime) {r : L} (h2 : p = 2 → r = 4) (hodd : p ≠ 2 → IsPrimitiveRoot (r + 1) p) :
    ∃ k : 𝓞 L, algebraMap (𝓞 L) L k = r ∧ k ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1))) := by
  have hnormZ : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 L)}) = m ^ Module.finrank ℚ L := by
    intro m
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)) m, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    simp
  have hd : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ht : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg (Real.log_nonneg hp1.le) (by linarith)
  by_cases h2' : p = 2
  · subst h2'
    refine ⟨4, ?_, ?_, ?_⟩
    · rw [h2 rfl]
      exact map_ofNat _ 4
    · intro h
      have h4 := congrArg (algebraMap (𝓞 L) L) h
      rw [map_ofNat, map_zero] at h4
      norm_num at h4
    · rw [show (4 : 𝓞 L) = ((4 : ℕ) : 𝓞 L) by norm_num, hnormZ, Nat.cast_pow, Real.log_pow]
      have h4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
        rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [h4]
      norm_num
  · have hζ : IsPrimitiveRoot (r + 1) p := hodd h2'
    let ζ : 𝓞 L := ⟨r + 1, hζ.isIntegral hp.pos⟩
    have hζ' : IsPrimitiveRoot ζ p :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
    refine ⟨ζ - 1, ?_, sub_ne_zero.2 (hζ'.ne_one hp.one_lt), ?_⟩
    · rw [map_sub, map_one]
      exact add_sub_cancel_right r 1
    · have hassoc := GroundTheory.Heights₂.Heights.RootsOfUnityValuation.one_sub_pow_associated hp hζ'
      have hsp : Ideal.span {ζ - 1} = Ideal.span {1 - ζ} := by
        rw [← neg_sub, Ideal.span_singleton_neg]
      have hN : Ideal.absNorm (Ideal.span {ζ - 1}) ^ (p - 1) = p ^ Module.finrank ℚ L := by
        rw [← hnormZ, ← Ideal.span_singleton_eq_span_singleton.2 hassoc, ← Ideal.span_singleton_pow,
          map_pow, hsp]
      have hNr : (Ideal.absNorm (Ideal.span {ζ - 1}) : ℝ) ^ (p - 1) = (p : ℝ) ^ Module.finrank ℚ L := by
        exact_mod_cast hN
      have hlog := congrArg Real.log hNr
      rw [Real.log_pow, Real.log_pow, Nat.cast_sub hp.one_le, Nat.cast_one] at hlog
      have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hL : Real.log (Ideal.absNorm (Ideal.span {ζ - 1})) =
          Module.finrank ℚ L * (Real.log p / ((p : ℝ) - 1)) := by
        rw [← mul_div_assoc, eq_div_iff hpos.ne']
        linear_combination hlog
      rw [hL]
      exact mul_le_mul_of_nonneg_left (by linarith) hd

/- English proof (translation)
Take `⟨hne, hlog⟩` from `GroundTheory.Heights₂.Heights.NineStatements.DifferentExtNorm.full E L ι`. Express the relevant statement in the definitionally equal form `(differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) ≠ ⊥ at hne`. Express the relevant statement in the definitionally equal form `Real.log (Ideal.absNorm ((differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι))) = _ at hlog`. Use `set I := (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) with hI`. Establish `hspan : Ideal.span {∏ p ∈ S, k p} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `Finset.prod_ne_zero_iff.2 fun p hp => (hk p hp).1`. Use `⟨by rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hne, hspan⟩, ?_⟩` and prove the remaining obligations. Establish `hn : (0 : ℝ) < Module.finrank ℚ L` using `Nat.cast_pos.2 Module.finrank_pos`. Establish `hN : ∀ p ∈ S, (Ideal.absNorm (Ideal.span {k p}) : ℝ) ≠ 0` using `fun p hp => by`.

Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `(hk p hp).1`. Establish `hNI : (Ideal.absNorm I : ℝ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hne`.

Rewrite using `[map_mul, ← Ideal.prod_span_singleton, map_prod, Nat.cast_mul, Nat.cast_prod, Real.log_mul hNI (Finset.prod_ne_zero_iff.2 hN), Real.log_prod hN, hlog]`. Establish `hB : ∑ p ∈ S, Real.log (Ideal.absNorm (Ideal.span {k p})) ≤ Module.finrank ℚ L * (2 * ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1))`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun p hp => (hk p hp).2`. Establish `hdE : (discr E : ℝ) ≠ 0` using `by exact_mod_cast NumberField.discr_ne_zero E`.

Establish `hR : 0 ≤ GroundTheory.Heights₂.Heights.NineStatements.logRd E`. Unfold `GroundTheory.Heights₂.Heights.NineStatements.logRd`. Use `div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)` and prove the remaining obligations. Establish `h1 : (1 : ℤ) ≤ |discr E|` using `Int.one_le_abs (NumberField.discr_ne_zero E)`. Conclude with `h1` after adjusting the coercions.

Establish `hlogd : Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) = GroundTheory.Heights₂.Heights.NineStatements.logRd E`. Unfold `GroundTheory.Heights₂.Heights.NineStatements.logRd`. Rewrite using `[Real.log_rpow (abs_pos.2 hdE)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hlogd, add_div, mul_div_cancel_left₀ _ hn.ne']`.

Establish `hB' : (∑ p ∈ S, Real.log (Ideal.absNorm (Ideal.span {k p}))) / Module.finrank ℚ L ≤ 2 * ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)`. Rewrite using `[div_le_iff₀ hn]`. Combine the linear relations using `[hB]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_bound {E : Type} [Field E] [NumberField E] (ι : E →+* L) (S : Finset ℕ) (k : ℕ → 𝓞 L)
    (hk : ∀ p ∈ S, k p ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k p})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1)))) :
    (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) * Ideal.span {∏ p ∈ S, k p} ≠ ⊥ ∧
    Real.log (Ideal.absNorm ((differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) *
        Ideal.span {∏ p ∈ S, k p})) / Module.finrank ℚ L ≤
      2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
        2 * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) := by
  obtain ⟨hne, hlog⟩ := GroundTheory.Heights₂.Heights.NineStatements.DifferentExtNorm.full E L ι
  change (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) ≠ ⊥ at hne
  change Real.log (Ideal.absNorm ((differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι))) = _ at hlog
  set I := (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) with hI
  have hspan : Ideal.span {∏ p ∈ S, k p} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun p hp => (hk p hp).1
  refine ⟨by rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hne, hspan⟩, ?_⟩
  have hn : (0 : ℝ) < Module.finrank ℚ L := Nat.cast_pos.2 Module.finrank_pos
  have hN : ∀ p ∈ S, (Ideal.absNorm (Ideal.span {k p}) : ℝ) ≠ 0 := fun p hp => by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact (hk p hp).1
  have hNI : (Ideal.absNorm I : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hne
  rw [map_mul, ← Ideal.prod_span_singleton, map_prod, Nat.cast_mul, Nat.cast_prod,
    Real.log_mul hNI (Finset.prod_ne_zero_iff.2 hN), Real.log_prod hN, hlog]
  have hB : ∑ p ∈ S, Real.log (Ideal.absNorm (Ideal.span {k p})) ≤
      Module.finrank ℚ L * (2 * ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hk p hp).2
  have hdE : (discr E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hR : 0 ≤ GroundTheory.Heights₂.Heights.NineStatements.logRd E := by
    unfold GroundTheory.Heights₂.Heights.NineStatements.logRd
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    have h1 : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (NumberField.discr_ne_zero E)
    exact_mod_cast h1
  have hlogd : Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) =
      GroundTheory.Heights₂.Heights.NineStatements.logRd E := by
    unfold GroundTheory.Heights₂.Heights.NineStatements.logRd
    rw [Real.log_rpow (abs_pos.2 hdE)]
    ring
  rw [hlogd, add_div, mul_div_cancel_left₀ _ hn.ne']
  have hB' : (∑ p ∈ S, Real.log (Ideal.absNorm (Ideal.span {k p}))) / Module.finrank ℚ L ≤
      2 * ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    rw [div_le_iff₀ hn]
    linarith [hB]
  linarith

end LevelTowerAlt.LocalPrimeBound
