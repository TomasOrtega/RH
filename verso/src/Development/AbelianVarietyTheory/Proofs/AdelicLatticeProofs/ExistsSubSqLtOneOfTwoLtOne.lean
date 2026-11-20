import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Use `haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot`. Use `haveI := v.isPrime`. Establish `h0 : (2 : 𝓞 F ⧸ v.asIdeal) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.2 h2` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `hinj : Function.Injective (fun t : 𝓞 F ⧸ v.asIdeal => t ^ 2)`. Introduce `s t hst`. Establish `hst' : s ^ 2 = t ^ 2` using `hst`. Establish `: (s - t) ^ 2 = 0`. Take the linear combination `hst' + (t ^ 2 - s * t) * h0`.

Conclude with `sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)`. Take `⟨t, ht⟩` from `Finite.surjective_of_injective hinj (Ideal.Quotient.mk v.asIdeal a)`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective t`. Use `⟨b, Ideal.Quotient.eq.1 ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `ht.symm`.
-/
theorem exists_sub_sq_mem_of_two_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (a : 𝓞 F) :
    ∃ b : 𝓞 F, a - b ^ 2 ∈ v.asIdeal := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI := v.isPrime
  have h0 : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 h2
    rwa [map_ofNat] at this
  have hinj : Function.Injective (fun t : 𝓞 F ⧸ v.asIdeal => t ^ 2) := by
    intro s t hst
    have hst' : s ^ 2 = t ^ 2 := hst
    have : (s - t) ^ 2 = 0 := by
      linear_combination hst' + (t ^ 2 - s * t) * h0
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj (Ideal.Quotient.mk v.asIdeal a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨b, Ideal.Quotient.eq.1 ?_⟩
  rw [map_pow]
  exact ht.symm

/- English proof (translation)
Introduce `F _ _ v h2 x hx`. Use `set φ := algebraMap F (v.adicCompletion F) with hφ`. Establish `hval : ∀ k : F, Valued.v (φ k) = v.valuation F k` using `fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k`. Establish `hmem : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal` using `fun r => HeightOneSpectrum.valuation_lt_one_iff_mem v r`. Establish `h2' : (2 : 𝓞 F) ∈ v.asIdeal`.

Rewrite using `[← hmem, ← hval, map_ofNat, map_ofNat]`. Conclude with `h2`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : F, Valued.v (φ k - x) < 1 := by`. Establish `hU : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x`. Rewrite using `[Valued.mem_nhds]`.

Use `⟨1, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : Valued.v.restrict (y - x) < Valued.v.restrict 1` using `by simpa using hy`. Simplify using `using Valued.v.restrict_lt_iff.mp hy'`. Conclude with `(HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds hU`. Establish `hk1 : v.valuation F k ≤ 1`.

Rewrite using `[← hval]`. Establish `e : φ k = (φ k - x) + x` using `by ring`. Rewrite using `[e]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le hk.le hx)`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by`.

Choose the witnesses or unpack the hypotheses as in `⟨s, m, hs, hsm⟩ : ∃ s m : 𝓞 F, s ∉ v.asIdeal ∧ k * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F m := by`. Take `⟨n, d, h | h⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := F) v k`. Conclude with `⟨d, n, d.2, h⟩`. Use `⟨n, d, fun hn => d.2 ?_, h⟩ show (d : 𝓞 F) ∈ v.asIdeal` and prove the remaining obligations. Rewrite using `[← hmem, ← h, map_mul]`.

Conclude with `(mul_le_of_le_one_left' hk1).trans_lt ((hmem n).2 hn)`. Take `⟨t, i, hi, hti⟩` from `(Ideal.IsPrime.isMaximal v.isPrime v.ne_bot).exists_inv hs`. Use `⟨t * m, ?_⟩` and prove the remaining obligations. Establish `hi' : i = 1 - t * s` using `by rw [← hti]; ring`. Establish `e : k - algebraMap (𝓞 F) F (t * m) = k * algebraMap (𝓞 F) F i`.

Rewrite using `[hi', map_mul, ← hsm, map_sub, map_one, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_mul]`. Conclude with `(mul_le_of_le_one_left' hk1).trans_lt ((hmem i).2 hi)`. Take `⟨b, hb⟩` from `exists_sub_sq_mem_of_two_mem F v h2' r`.

Use `⟨φ (algebraMap (𝓞 F) F b), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `HeightOneSpectrum.valuation_le_one v b`. Establish `e : x - φ (algebraMap (𝓞 F) F b) ^ 2 = -(φ k - x) + (φ (k - algebraMap (𝓞 F) F r) + φ (algebraMap (𝓞 F) F (r - b ^ 2)))`. Simplify using `only [map_sub, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Valuation.map_add_lt _ (by rwa [Valuation.map_neg]) (Valuation.map_add_lt _ ?_ ?_)` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `hr`.

Rewrite using `[hval]`. Conclude with `(hmem _).2 hb`.
-/
theorem exists_sub_sq_lt_one_of_two_lt_one :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
        ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1 := by
  intro F _ _ v h2 x hx
  set φ := algebraMap F (v.adicCompletion F) with hφ
  have hval : ∀ k : F, Valued.v (φ k) = v.valuation F k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have hmem : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal :=
    fun r => HeightOneSpectrum.valuation_lt_one_iff_mem v r

  have h2' : (2 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hmem, ← hval, map_ofNat, map_ofNat]
    exact h2

  obtain ⟨k, hk⟩ : ∃ k : F, Valued.v (φ k - x) < 1 := by
    have hU : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun y hy => ?_⟩
      have hy' : Valued.v.restrict (y - x) < Valued.v.restrict 1 := by simpa using hy
      simpa using Valued.v.restrict_lt_iff.mp hy'
    exact (HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds hU
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← hval]
    have e : φ k = (φ k - x) + x := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le hk.le hx)

  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
    obtain ⟨s, m, hs, hsm⟩ : ∃ s m : 𝓞 F, s ∉ v.asIdeal ∧
        k * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F m := by
      obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := F) v k
      · exact ⟨d, n, d.2, h⟩
      · refine ⟨n, d, fun hn => d.2 ?_, h⟩
        show (d : 𝓞 F) ∈ v.asIdeal
        rw [← hmem, ← h, map_mul]
        exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem n).2 hn)
    obtain ⟨t, i, hi, hti⟩ := (Ideal.IsPrime.isMaximal v.isPrime v.ne_bot).exists_inv hs
    refine ⟨t * m, ?_⟩
    have hi' : i = 1 - t * s := by rw [← hti]; ring
    have e : k - algebraMap (𝓞 F) F (t * m) = k * algebraMap (𝓞 F) F i := by
      rw [hi', map_mul, ← hsm, map_sub, map_one, map_mul]; ring
    rw [e, map_mul]
    exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem i).2 hi)

  obtain ⟨b, hb⟩ := exists_sub_sq_mem_of_two_mem F v h2' r
  refine ⟨φ (algebraMap (𝓞 F) F b), ?_, ?_⟩
  · rw [hval]
    exact HeightOneSpectrum.valuation_le_one v b
  · have e : x - φ (algebraMap (𝓞 F) F b) ^ 2 =
        -(φ k - x) + (φ (k - algebraMap (𝓞 F) F r) + φ (algebraMap (𝓞 F) F (r - b ^ 2))) := by
      simp only [map_sub, map_pow]; ring
    rw [e]
    refine Valuation.map_add_lt _ (by rwa [Valuation.map_neg]) (Valuation.map_add_lt _ ?_ ?_)
    · rw [hval]; exact hr
    · rw [hval]; exact (hmem _).2 hb

end GlobalTheory.QNorm
