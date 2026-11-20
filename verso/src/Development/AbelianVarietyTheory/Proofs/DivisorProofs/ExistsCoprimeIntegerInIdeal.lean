import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.NormCoprime

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]`. Introduce `hdvd`. Use `Ideal.finiteQuotientOfFreeOfNeBot I hI` as an intermediate fact. Set `_ : Fintype (𝓞 K ⧸ I)` to `Fintype.ofFinite _`.

Rewrite `hdvd` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card p hdvd`. Establish `h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)}` using `by rw [h]; trivial`. Take `⟨i, hi, r, hr, hir⟩` from `Submodule.mem_sup.mp h1`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`.

Establish `hpx : (p : ℕ) • x = 0` using `by rw [← hx]; exact addOrderOf_nsmul_eq_zero x`. Establish `hq : (Ideal.Quotient.mk I i) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hi`. Establish `hx0 : x = 0`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y)` using `by linear_combination (-(y)) * hir`.

Establish `e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y + Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y)`. Rewrite using `[nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← e0]`. Rewrite using `[e, hpx, mul_zero, add_zero, hq, zero_mul]`. Rewrite `hx` using `[hx0, addOrderOf_zero]`. Conclude with `hp.one_lt.ne hx`.
-/
theorem coprime_absNorm_of_sup {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by rw [h]; trivial
  obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hpx : (p : ℕ) • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hq : (Ideal.Quotient.mk I i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hx0 : x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y) := by linear_combination (-(y)) * hir
    have e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y +
        Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y) := by
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← e0]
    rw [e, hpx, mul_zero, add_zero, hq, zero_mul]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

/- English proof (translation)
Introduce `K _ _ c l hl hc hv`. Use `⟨Ideal.absNorm c, ?_, Ideal.absNorm_mem c⟩` and prove the remaining obligations. Use `coprime_absNorm_of_sup l hl hc ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Establish `hlM : ((l : ℕ) : 𝓞 K) ∈ M` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hcM : c ≤ M` using `le_trans le_sup_left hle`. Establish `hM0 : M ≠ ⊥`. Introduce `h0`. Rewrite `hlM` using `[h0, Ideal.mem_bot]`.

Conclude with `hl.ne_zero (by exact_mod_cast hlM)`. Conclude with `hv ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.mpr hcM) hlM`.
-/
theorem exists_coprime_mem : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by
  intro K _ _ c l hl hc hv
  refine ⟨Ideal.absNorm c, ?_, Ideal.absNorm_mem c⟩
  refine coprime_absNorm_of_sup l hl hc ?_
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hlM : ((l : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcM : c ≤ M := le_trans le_sup_left hle
  have hM0 : M ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hlM
    exact hl.ne_zero (by exact_mod_cast hlM)
  exact hv ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.mpr hcM) hlM

end GlobalTheory.NormCoprime
