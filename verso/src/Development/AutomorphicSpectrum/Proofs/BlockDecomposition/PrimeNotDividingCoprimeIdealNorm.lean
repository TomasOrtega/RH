import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.DeligneRibet

/- English proof (translation)
Introduce `F _ _ l hl 𝔟 h hdvd`. Establish `h1 : (1 : 𝓞 F) ∈ 𝔟 ⊔ Ideal.span {(l : 𝓞 F)}`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Take `⟨b, hb, c, hc, hbc⟩` from `Submodule.mem_sup.mp h1`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hc`. Distinguish the cases in `h𝔟 : 𝔟 = ⊥`. Substitute `h𝔟` using the available equality. Rewrite `h` using `[bot_sup_eq]`. Establish `hnorm` using `Ideal.absNorm_span_singleton (l : 𝓞 F)`.

Rewrite `hnorm` using `[h, Ideal.absNorm_top]`. Establish `hcast : (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ)` using `by simp`. Rewrite `hnorm` using `[hcast, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast]`. Establish `hpos : 0 < Module.finrank ℤ (𝓞 F)` using `Module.finrank_pos`. Break down `Nat.pow_eq_one.mp hnorm.symm with h' | h'` into its components or cases.

Conclude with `hl.one_lt.ne' h'`. Use linear arithmetic over natural numbers and integers. Use `haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔟 h𝔟 haveI := Fact.mk hl`. Rewrite `hdvd` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' l hdvd`.

Establish `hlx : (l : 𝓞 F ⧸ 𝔟) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]`. Establish `hunit : Ideal.Quotient.mk 𝔟 a * (l : 𝓞 F ⧸ 𝔟) = 1`. Establish `key` using `congrArg (Ideal.Quotient.mk 𝔟) hbc`. Rewrite `key` using `[map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, map_natCast, map_one]`.

Conclude with `key`. Establish `hx0 : x = 0`. Rewrite using `[← one_mul x, ← hunit, mul_assoc, hlx, mul_zero]`. Rewrite `hx` using `[hx0, addOrderOf_zero]`. Conclude with `hl.one_lt.ne hx`.
-/
theorem absNorm_not_dvd_of_sup_span_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F),
      𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  intro F _ _ l hl 𝔟 h hdvd
  have h1 : (1 : 𝓞 F) ∈ 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  by_cases h𝔟 : 𝔟 = ⊥
  · subst h𝔟
    rw [bot_sup_eq] at h
    have hnorm := Ideal.absNorm_span_singleton (l : 𝓞 F)
    rw [h, Ideal.absNorm_top] at hnorm
    have hcast : (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) := by simp
    rw [hcast, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hnorm
    have hpos : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp hnorm.symm with h' | h'
    · exact hl.one_lt.ne' h'
    · omega
  · haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔟 h𝔟
    haveI := Fact.mk hl
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hdvd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
    have hlx : (l : 𝓞 F ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : Ideal.Quotient.mk 𝔟 a * (l : 𝓞 F ⧸ 𝔟) = 1 := by
      have key := congrArg (Ideal.Quotient.mk 𝔟) hbc
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, map_natCast,
        map_one] at key
      exact key
    have hx0 : x = 0 := by
      rw [← one_mul x, ← hunit, mul_assoc, hlx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hl.one_lt.ne hx

end GlobalTheory.CompanionTheory.DeligneRibet
