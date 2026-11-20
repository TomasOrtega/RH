import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TraceIdempotentNotDivisibleStatement

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Glob

/- English proof (translation)
Introduce `hdiv`. Use `set d := Module.finrank ℚ E with hd`. Establish `hdpos : 0 < d` using `Module.finrank_pos`. Establish `hp0 : (p : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hPbot : P ≠ ⊥`.

Introduce `h`. Rewrite `hpP` using `[h, Ideal.mem_bot]`. Conclude with `hp0 hpP`. Establish `hPmax : P.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hPbot`. Establish `hpd : ((p : 𝓞 E)) ^ d ∈ P` using `Ideal.pow_mem_of_mem P hpP d hdpos`.

Establish `hspanP : Ideal.span {((p : 𝓞 E)) ^ d} ≤ P`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `hpd`. Establish `hJP : ¬ J ≤ P` using `fun h => hPJ (Ideal.dvd_iff_le.2 h)`. Establish `hk : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hspan` using `[pow_zero, Ideal.one_eq_top, Ideal.top_mul]`. Conclude with `hJP (hspan ▸ hspanP)`. Establish `hcop : IsCoprime P J`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`.

Conclude with `hPmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hJP (h ▸ le_sup_right))`. Take `⟨y, hy, x, hx, hyx⟩` from `Ideal.isCoprime_iff_exists.1 (hcop.pow_left (m := k))`. Establish `hxy : x * y ∈ Ideal.span {((p : 𝓞 E)) ^ d}`. Rewrite using `[hspan, mul_comm x y]`. Conclude with `Ideal.mul_mem_mul hy hx`.

Establish `hidem : x * x - x ∈ Ideal.span {((p : 𝓞 E)) ^ d}`. Establish `: x * x - x = -(x * y)`. Establish `: x = 1 - y` using `by rw [← hyx]; ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `neg_mem hxy`. Establish `hnot : x ∉ Ideal.span {((p : 𝓞 E)) ^ d}`. Introduce `h`. Establish `h1 : x ∈ P` using `hspanP h`.

Establish `h2 : y ∈ P` using `Ideal.pow_le_self hk hy`. Conclude with `hPmax.ne_top ((Ideal.eq_top_iff_one _).2 (hyx ▸ add_mem h2 h1))`. Establish `hlt : Module.finrank ℤ (𝓞 E) < p ^ d`. Rewrite using `[RingOfIntegers.rank]`. Conclude with `Nat.lt_pow_self hp.one_lt`.

Use `GlobalTheory.T.trace_idempotent_not_divisible (𝓞 E) x p d hp hlt hidem hnot ?_` and prove the remaining obligations. Establish `hpdE : ((p : E)) ^ d ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)`. Establish `hD0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `differentIdeal_ne_bot`.

Establish `hz : (x : E) / ((p : E)) ^ d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)`. Establish `hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) = ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹`. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]`. Rewrite using `[hdual, FractionalIdeal.mem_inv_iff hD0]`. Introduce `w hw`.

Take `⟨δ, hδ, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hw`. Establish `hδP : δ ∈ P ^ k` using `Ideal.dvd_iff_le.1 hdiv hδ`. Establish `hmem : δ * x ∈ Ideal.span {((p : 𝓞 E)) ^ d}`. Rewrite using `[hspan]`. Conclude with `Ideal.mul_mem_mul hδP hx`.

Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hmem`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap (𝓞 E) E a * ((p : E)) ^ d = algebraMap (𝓞 E) E δ * (x : E)`. Use `congrArg (algebraMap (𝓞 E) E) ha` as an intermediate fact.

Simplify using `using this`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`.

Establish `htr` using `(FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h10).1 hz 1 (FractionalIdeal.one_mem_one _)`. Take `⟨n, hn⟩` from `htr`. Rewrite `hn` using `[Algebra.traceForm_apply, mul_one]`. Establish `hzs : (x : E) / ((p : E)) ^ d = (((p : ℚ) ^ d)⁻¹) • (x : E)`. Rewrite using `[Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]`.

Rewrite `hn` using `[hzs, map_smul, smul_eq_mul, ← Algebra.coe_trace_int]`. Establish `hpq : ((p : ℚ)) ^ d ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `: ((Algebra.trace ℤ (𝓞 E) x : ℤ) : ℚ) = ((p : ℚ)) ^ d * (n : ℚ)`. Establish `h3 : (algebraMap ℤ ℚ n) = (n : ℚ)` using `rfl`.

Rewrite `hn` using `[h3]`. Rewrite using `[hn]`. Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions.
-/
theorem not_pow_dvd_different (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime]
    (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 E) ∈ P) (hPJ : ¬ P ∣ J)
    (hspan : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J) :
    ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  intro hdiv
  set d := Module.finrank ℚ E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact hp0 hpP
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPbot
  have hpd : ((p : 𝓞 E)) ^ d ∈ P := Ideal.pow_mem_of_mem P hpP d hdpos
  have hspanP : Ideal.span {((p : 𝓞 E)) ^ d} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hpd
  have hJP : ¬ J ≤ P := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top, Ideal.top_mul] at hspan
    exact hJP (hspan ▸ hspanP)
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact hPmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hJP (h ▸ le_sup_right))
  obtain ⟨y, hy, x, hx, hyx⟩ := Ideal.isCoprime_iff_exists.1 (hcop.pow_left (m := k))
  have hxy : x * y ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    rw [hspan, mul_comm x y]
    exact Ideal.mul_mem_mul hy hx
  have hidem : x * x - x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    have : x * x - x = -(x * y) := by
      have : x = 1 - y := by rw [← hyx]; ring
      rw [this]; ring
    rw [this]
    exact neg_mem hxy
  have hnot : x ∉ Ideal.span {((p : 𝓞 E)) ^ d} := by
    intro h
    have h1 : x ∈ P := hspanP h
    have h2 : y ∈ P := Ideal.pow_le_self hk hy
    exact hPmax.ne_top ((Ideal.eq_top_iff_one _).2 (hyx ▸ add_mem h2 h1))
  have hlt : Module.finrank ℤ (𝓞 E) < p ^ d := by
    rw [RingOfIntegers.rank]
    exact Nat.lt_pow_self hp.one_lt
  refine GlobalTheory.T.trace_idempotent_not_divisible (𝓞 E) x p d hp hlt hidem hnot ?_

  have hpdE : ((p : E)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hD0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hz : (x : E) / ((p : E)) ^ d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
        ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
    rw [hdual, FractionalIdeal.mem_inv_iff hD0]
    intro w hw
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hw
    have hδP : δ ∈ P ^ k := Ideal.dvd_iff_le.1 hdiv hδ
    have hmem : δ * x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
      rw [hspan]
      exact Ideal.mul_mem_mul hδP hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨a, ?_⟩
    have h2 : algebraMap (𝓞 E) E a * ((p : E)) ^ d = algebraMap (𝓞 E) E δ * (x : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      simpa using this
    field_simp
    rw [h2]
    ring
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have htr := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h10).1 hz 1 (FractionalIdeal.one_mem_one _)
  obtain ⟨n, hn⟩ := htr
  rw [Algebra.traceForm_apply, mul_one] at hn
  have hzs : (x : E) / ((p : E)) ^ d = (((p : ℚ) ^ d)⁻¹) • (x : E) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]
  rw [hzs, map_smul, smul_eq_mul, ← Algebra.coe_trace_int] at hn
  have hpq : ((p : ℚ)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨n, ?_⟩
  have : ((Algebra.trace ℤ (𝓞 E) x : ℤ) : ℚ) = ((p : ℚ)) ^ d * (n : ℚ) := by
    have h3 : (algebraMap ℤ ℚ n) = (n : ℚ) := rfl
    rw [h3] at hn
    rw [hn]
    field_simp
  exact_mod_cast this

end GlobalTheory.CompanionTheory.Glob
