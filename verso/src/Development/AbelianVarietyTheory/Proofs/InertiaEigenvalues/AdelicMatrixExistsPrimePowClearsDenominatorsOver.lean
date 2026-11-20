import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

/- English proof (translation)
Take `⟨b, hb, hbx⟩` from `HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x`. Rewrite `hbx` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Use `set N := Ideal.absNorm (Ideal.span {b}) with hNdef`. Establish `hN0 : N ≠ 0`.

Rewrite using `[hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`. Establish `hmem : (N : 𝓞 E) ∈ Ideal.span {b}` using `Ideal.absNorm_mem _`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Use `set e := N.factorization p with he`.

Use `set r := N / p ^ e with hr`. Establish `hcop : r.Coprime p` using `(Nat.coprime_ordCompl hp hN0).symm`. Establish `hsplit : p ^ e * r = N` using `Nat.ordProj_mul_ordCompl_eq_self N p`. Establish `hrQ : (r : 𝓞 E) ∉ Q.asIdeal`. Introduce `hrQ`.

Establish `h1 : ((Nat.gcd r p : ℕ) : ℤ) = r * Nat.gcdA r p + p * Nat.gcdB r p` using `Nat.gcd_eq_gcd_ab r p`. Rewrite `h1` using `[hcop]`. Establish `h2` using `congrArg (Int.cast : ℤ → 𝓞 E) h1`. Move the coercions through the operations in `at h2`. Establish `h3 : (1 : 𝓞 E) ∈ Q.asIdeal`.

Rewrite using `[h2]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hrQ) (Ideal.mul_mem_right _ _ hpQ)`. Conclude with `Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)`. Establish `hvr : Valued.v ((r : Q.adicCompletion E)) = 1`. Establish `h1` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (r : 𝓞 E)`.

Establish `h2 : Q.valuation E (algebraMap (𝓞 E) E (r : 𝓞 E)) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hrQ`. Simplify using `only [map_natCast] at h1 h2`. Rewrite using `[h1, h2]`. Establish `hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1`. Establish `e' : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) * (algebraMap (𝓞 E) (Q.adicCompletion E) b)`.

Rewrite using `[← map_mul, hc, map_natCast]`. Rewrite using `[e', mul_assoc, Valuation.map_mul, mul_comm _ x]`. Use `mul_le_one' ?_ hbx` and prove the remaining obligations. Establish `h` using `HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c`. Rewrite `h` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis.

Establish `hex : Valued.v (((p ^ e : ℕ) : Q.adicCompletion E) * x) ≤ 1`. Rewrite `hNx` using `[← hsplit]`. Rewrite `hNx` using `[Nat.cast_mul, mul_comm ((p ^ e : ℕ) : Q.adicCompletion E), mul_assoc, Valuation.map_mul, hvr, one_mul]`. Conclude with `hNx`. Use `⟨e, fun d hd => ?_⟩` and prove the remaining obligations.

Establish `hde : p ^ d = p ^ (d - e) * p ^ e` using `by rw [← pow_add, Nat.sub_add_cancel hd]`. Rewrite using `[hde, Nat.cast_mul, mul_assoc, Valuation.map_mul]`. Conclude with `mul_le_one' (natCast_adicCompletion_v_le_one Q _) hex`.
-/
theorem exists_pow_mul_v_le_one_of_mem {E : Type} [Field E] [NumberField E]
    (p : ℕ) (hp : p.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hpQ : (p : 𝓞 E) ∈ Q.asIdeal)
    (x : Q.adicCompletion E) :
    ∃ a : ℕ, ∀ d : ℕ, a ≤ d → Valued.v (((p ^ d : ℕ) : Q.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hbx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b}) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have hmem : (N : 𝓞 E) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  set e := N.factorization p with he
  set r := N / p ^ e with hr
  have hcop : r.Coprime p := (Nat.coprime_ordCompl hp hN0).symm
  have hsplit : p ^ e * r = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hrQ : (r : 𝓞 E) ∉ Q.asIdeal := by
    intro hrQ
    have h1 : ((Nat.gcd r p : ℕ) : ℤ) = r * Nat.gcdA r p + p * Nat.gcdB r p := Nat.gcd_eq_gcd_ab r p
    rw [hcop] at h1
    have h2 := congrArg (Int.cast : ℤ → 𝓞 E) h1
    push_cast at h2
    have h3 : (1 : 𝓞 E) ∈ Q.asIdeal := by
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hrQ) (Ideal.mul_mem_right _ _ hpQ)
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hvr : Valued.v ((r : Q.adicCompletion E)) = 1 := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (r : 𝓞 E)
    have h2 : Q.valuation E (algebraMap (𝓞 E) E (r : 𝓞 E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hrQ
    simp only [map_natCast] at h1 h2
    rw [h1, h2]
  have hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1 := by
    have e' : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) *
        (algebraMap (𝓞 E) (Q.adicCompletion E) b) := by
      rw [← map_mul, hc, map_natCast]
    rw [e', mul_assoc, Valuation.map_mul, mul_comm _ x]
    refine mul_le_one' ?_ hbx
    have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hex : Valued.v (((p ^ e : ℕ) : Q.adicCompletion E) * x) ≤ 1 := by
    rw [← hsplit] at hNx
    rw [Nat.cast_mul, mul_comm ((p ^ e : ℕ) : Q.adicCompletion E), mul_assoc, Valuation.map_mul,
      hvr, one_mul] at hNx
    exact hNx
  refine ⟨e, fun d hd => ?_⟩
  have hde : p ^ d = p ^ (d - e) * p ^ e := by rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hde, Nat.cast_mul, mul_assoc, Valuation.map_mul]
  exact mul_le_one' (natCast_adicCompletion_v_le_one Q _) hex

/- English proof (translation)
Introduce `E _ _ p hp n A`. Establish `h0 : Ideal.span {(p : 𝓞 E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Establish `hF` using `Ideal.finite_factors h0`.

Establish `hmemF : ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → Q ∈ {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {(p : 𝓞 E)}}` using `fun Q hQ => Ideal.dvd_span_singleton.mpr hQ`. Set `f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ` to `fun t => if h : (p : 𝓞 E) ∈ t.1.asIdeal then Classical.choose (exists_pow_mul_v_le_one_of_mem p hp t.1 h ((A t.2.1 t.2.2) t.1)) else 0`. Set `T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n)` to `hF.toFinset ×ˢ Finset.univ`. Use `⟨T.sup f, fun d hd Q hQ i j => ?_⟩` and prove the remaining obligations. Set `ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E` to `RestrictedProduct.evalRingHom _ Q`.

Establish `hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x` using `fun _ => rfl`. Rewrite using `[hev, map_mul, map_natCast, ← hev]`. Establish `hmem : (Q, i, j) ∈ T`. Simplify using `only [T, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_univ, and_true]`. Conclude with `hmemF Q hQ`.

Establish `hle : f (Q, i, j) ≤ d` using `le_trans (Finset.le_sup hmem) hd`. Establish `hspec` using `Classical.choose_spec (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q))`. Establish `hfQ : f (Q, i, j) = Classical.choose (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q))`. Simplify using `only [f, dif_pos hQ]`. Conclude with `hspec d (hfQ ▸ hle)`.
-/
theorem exists_pow_clears_denom_over :
    ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((((p ^ d : ℕ) : FiniteAdeleRing (𝓞 E) E) * A i j) Q) ≤ 1 := by
  intro E _ _ p hp n A
  classical
  have h0 : Ideal.span {(p : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hF := Ideal.finite_factors h0
  have hmemF : ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal →
      Q ∈ {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {(p : 𝓞 E)}} := fun Q hQ =>
    Ideal.dvd_span_singleton.mpr hQ
  let f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ := fun t =>
    if h : (p : 𝓞 E) ∈ t.1.asIdeal then
      Classical.choose (exists_pow_mul_v_le_one_of_mem p hp t.1 h ((A t.2.1 t.2.2) t.1)) else 0
  let T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n) := hF.toFinset ×ˢ Finset.univ
  refine ⟨T.sup f, fun d hd Q hQ i j => ?_⟩
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, map_natCast, ← hev]
  have hmem : (Q, i, j) ∈ T := by
    simp only [T, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_univ, and_true]
    exact hmemF Q hQ
  have hle : f (Q, i, j) ≤ d := le_trans (Finset.le_sup hmem) hd
  have hspec := Classical.choose_spec (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q))
  have hfQ : f (Q, i, j) = Classical.choose (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q)) := by
    simp only [f, dif_pos hQ]
  exact hspec d (hfQ ▸ hle)

end GlobalTheory.StdAtPrime
