import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlacesStatement

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (OF E) (𝓞 E))` using `FaithfulSMul.algebraMap_injective (OF E) (𝓞 E)`. Take `⟨Q, -, hQ, hQv⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) v.asIdeal ⊥ (by`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap (OF E) (𝓞 E))]`. Rewrite using `[hinj hx]`.

Conclude with `v.asIdeal.zero_mem)`. Establish `hQne : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[← hQv]`.

Conclude with `Ideal.comap_bot_of_injective _ hinj`. Use `⟨⟨Q, hQ, hQne⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[below, Ideal.under, ← hQv]`.
-/
theorem basecond_exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), below P = v := by
  have hinj : Function.Injective (algebraMap (OF E) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (OF E) (𝓞 E)
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) v.asIdeal ⊥
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap (OF E) (𝓞 E))] at hx
      rw [hinj hx]
      exact v.asIdeal.zero_mem)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨⟨Q, hQ, hQne⟩, ?_⟩
  ext x
  simp [below, Ideal.under, ← hQv]

/- English proof (translation)
Simplify using `[below, Ideal.under, Ideal.mem_comap, map_natCast]`.
-/
theorem basecond_natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  simp [below, Ideal.under, Ideal.mem_comap, map_natCast]

/- English proof (translation)
Introduce `R H q0 w0 hspl hok`. Establish `hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime` using `fun p hp => (hok.splits p hp).1`. Establish `hN0 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ≠ 0`. Establish `h : H.g 0 * H.g 1 * H.pde * H.pde' ≠ 0`. Apply the tactic sequence `refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>`.

Conclude with `(hprime _ (by simp)).ne_zero`. Conclude with `h` after adjusting the coercions. Establish `hle : cond0 H w0 ≤ (below w0).asIdeal`. Unfold `cond0`. Use `first`.

Consider the case `exact Ideal.mul_le_right`. Consider the case `exact Ideal.mul_le_left`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Break down `Ideal.mul_eq_bot.mp h with h1 | h1` into its components or cases.

Rewrite `h1` using `[← Ideal.zero_eq_bot]`. Establish `h2` using `pow_eq_zero_iff (two_ne_zero) |>.mp h1`. Rewrite `h2` using `[Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN0 h2`. Conclude with `(below w0).ne_bot h1`.

Introduce `h`. Conclude with `(below w0).isPrime.ne_top (top_le_iff.mp (h ▸ hle))`. Introduce `v hv`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp, hpv⟩ : ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ((p : ℕ) : OF H.E) ∈ v.asIdeal := by`. Establish `hvp : Prime v.asIdeal` using `Ideal.prime_of_isPrime v.ne_bot v.isPrime`.

Break down `hvp.dvd_or_dvd hv with h | h` into its components or cases. Establish `h1 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ∈ v.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd (hvp.dvd_of_dvd_pow h))`. Move the coercions through the operations in `at h1`. Break down `v.isPrime.mem_or_mem h1 with h1 | h1` into its components or cases. Break down `v.isPrime.mem_or_mem h1 with h1 | h1` into its components or cases.

Break down `v.isPrime.mem_or_mem h1 with h1 | h1` into its components or cases. Conclude with `⟨H.g 0, by simp, h1⟩`. Conclude with `⟨H.g 1, by simp, h1⟩`. Conclude with `⟨H.pde, by simp, h1⟩`. Conclude with `⟨H.pde', by simp, h1⟩`.

Establish `h1 : (below w0).asIdeal = v.asIdeal` using `((below w0).isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h)`. Use `⟨q0, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, basecond_natCast_mem_below]`. Conclude with `hok.referencePlaceOverPrime`. Take `⟨P, hPv⟩` from `basecond_exists_above v`.

Establish `hpP : ((p : ℕ) : 𝓞 H.E) ∈ P.asIdeal`. Rewrite using `[← basecond_natCast_mem_below, hPv]`. Conclude with `hpv`. Take `⟨hpr, hp2, hdisc, hnorm⟩` from `hok.splits p hp`. Use `⟨hPv ▸ hspl p hp P hpP, ?_, p, hpr, hp2, hpv, hdisc, hnorm⟩` and prove the remaining obligations.

Take `⟨e4, eb, e0⟩` from `GlobalTheory.T.conductor_exponent_at_places R H q0 w0 hok P`. Rewrite using `[← hPv]`. Distinguish the cases in `h4 : Over4 H P`. Rewrite using `[e4 h4]`. Distinguish the cases in `hb : below P = below w0`.

Rewrite using `[(eb hb).2]`. Evaluate the numerical expressions. Rewrite using `[e0 h4 hb]`. Evaluate the numerical expressions.
-/
theorem isBaseCond_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Splits (below P)) → PlacesOk H q0 w0 → IsBaseCond (cond0 H w0) := by
  intro R H q0 w0 hspl hok
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hok.splits p hp).1

  have hN0 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ≠ 0 := by
    have h : H.g 0 * H.g 1 * H.pde * H.pde' ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
        exact (hprime _ (by simp)).ne_zero
    exact_mod_cast h
  have hle : cond0 H w0 ≤ (below w0).asIdeal := by
    unfold cond0
    first
    | exact Ideal.mul_le_right
    | exact Ideal.mul_le_left
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases Ideal.mul_eq_bot.mp h with h1 | h1
    · rw [← Ideal.zero_eq_bot] at h1
      have h2 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h2
      exact hN0 h2
    · exact (below w0).ne_bot h1
  · intro h
    exact (below w0).isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  · intro v hv

    obtain ⟨p, hp, hpv⟩ : ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ((p : ℕ) : OF H.E) ∈ v.asIdeal := by
      have hvp : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
      rcases hvp.dvd_or_dvd hv with h | h
      · have h1 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ∈ v.asIdeal :=
          (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd (hvp.dvd_of_dvd_pow h))
        push_cast at h1
        rcases v.isPrime.mem_or_mem h1 with h1 | h1
        · rcases v.isPrime.mem_or_mem h1 with h1 | h1
          · rcases v.isPrime.mem_or_mem h1 with h1 | h1
            · exact ⟨H.g 0, by simp, h1⟩
            · exact ⟨H.g 1, by simp, h1⟩
          · exact ⟨H.pde, by simp, h1⟩
        · exact ⟨H.pde', by simp, h1⟩
      · have h1 : (below w0).asIdeal = v.asIdeal :=
          ((below w0).isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h)
        refine ⟨q0, by simp, ?_⟩
        rw [← h1, basecond_natCast_mem_below]
        exact hok.referencePlaceOverPrime
    obtain ⟨P, hPv⟩ := basecond_exists_above v
    have hpP : ((p : ℕ) : 𝓞 H.E) ∈ P.asIdeal := by
      rw [← basecond_natCast_mem_below, hPv]
      exact hpv
    obtain ⟨hpr, hp2, hdisc, hnorm⟩ := hok.splits p hp
    refine ⟨hPv ▸ hspl p hp P hpP, ?_, p, hpr, hp2, hpv, hdisc, hnorm⟩

    obtain ⟨e4, eb, e0⟩ := GlobalTheory.T.conductor_exponent_at_places R H q0 w0 hok P
    rw [← hPv]
    by_cases h4 : Over4 H P
    · rw [e4 h4]
    · by_cases hb : below P = below w0
      · rw [(eb hb).2]; norm_num
      · rw [e0 h4 hb]; norm_num

end GlobalTheory.LamTie
