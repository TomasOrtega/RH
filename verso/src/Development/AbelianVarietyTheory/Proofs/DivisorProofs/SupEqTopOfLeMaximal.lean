import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

open NumberField

namespace GlobalTheory.PrimesAboveExistence

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hAM : A ≤ M` using `h M hM (le_sup_right.trans hle)`. Conclude with `hM.ne_top (top_le_iff.mp (hA ▸ sup_le (le_sup_left.trans hle) hAM))`.
-/
theorem sup_eq_top_of_le_maximal {R : Type} [CommRing R] {A B I : Ideal R}
    (h : ∀ M : Ideal R, M.IsMaximal → B ≤ M → A ≤ M) (hA : I ⊔ A = ⊤) : I ⊔ B = ⊤ := by
  by_contra hne

  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hAM : A ≤ M := h M hM (le_sup_right.trans hle)
  exact hM.ne_top (top_le_iff.mp (hA ▸ sup_le (le_sup_left.trans hle) hAM))

/- English proof (translation)
Use `set L : Ideal (𝓞 F) := Ideal.span {(l : 𝓞 F)} with hL`. Establish `hL0 : L ≠ ⊥`. Rewrite using `[hL, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hl.ne_zero` after adjusting the coercions. Use `⟨(UniqueFactorizationMonoid.normalizedFactors L).toFinset, ?_, ?_⟩` and prove the remaining obligations.

Introduce `𝔭 h𝔭`. Rewrite `h𝔭` using `[Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0]`. Take `⟨hp, hle⟩` from `h𝔭`. Establish `hne : 𝔭 ≠ ⊥` using `fun h => hL0 (le_bot_iff.mp (h ▸ hle))`. Establish `hmax : 𝔭.IsMaximal` using `hp.isMaximal hne`.

Use `⟨hmax, hne, ?_⟩` and prove the remaining obligations. Establish `hdvd : Ideal.absNorm 𝔭 ∣ l ^ Module.finrank ℤ (𝓞 F)`. Establish `h` using `Ideal.absNorm_dvd_absNorm_of_le hle`. Rewrite `h` using `[hL, Ideal.absNorm_span_singleton, show (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) by simp, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast]`. Then use the resulting hypothesis. Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hl).mp hdvd`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hmax.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hk))`. Express the relevant statement in the definitionally equal form `l ∣ Ideal.absNorm 𝔭`. Rewrite using `[hk]`.

Conclude with `dvd_pow_self l hk0`. Introduce `I`. Unfold `Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo`. Use `and_congr_right fun _ => ⟨fun h => sup_eq_top_of_le_maximal ?_ h, fun h => sup_eq_top_of_le_maximal ?_ h⟩` and prove the remaining obligations. Introduce `M hM hLM`.

Establish `hmem : M ∈ (UniqueFactorizationMonoid.normalizedFactors L).toFinset`. Rewrite using `[Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0]`. Conclude with `⟨hM.isPrime, hLM⟩`. Conclude with `Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun 𝔭 => 𝔭) hmem)`. Introduce `M hM hPM`.

Take `⟨𝔭, h𝔭, hle⟩` from `(Ideal.IsPrime.prod_le hM.isPrime).mp hPM`. Rewrite `h𝔭` using `[Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0]`. Establish `hne : 𝔭 ≠ ⊥` using `fun h => hL0 (le_bot_iff.mp (h ▸ h𝔭.2))`. Establish `h𝔭M : 𝔭 = M` using `(h𝔭.1.isMaximal hne).eq_of_le hM.ne_top hle`. Conclude with `h𝔭M ▸ h𝔭.2`.
-/
theorem exists_primes_above {F : Type} [Field F] [NumberField F] (l : ℕ) (hl : Nat.Prime l) :
    ∃ P : Finset (Ideal (𝓞 F)),
      (∀ 𝔭 ∈ P, Ideal.IsMaximal 𝔭 ∧ 𝔭 ≠ ⊥ ∧ l ∣ (Ideal.absNorm : Ideal (𝓞 F) → ℕ) 𝔭) ∧
      ∀ I : Ideal (𝓞 F), Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔
        Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  classical
  set L : Ideal (𝓞 F) := Ideal.span {(l : 𝓞 F)} with hL
  have hL0 : L ≠ ⊥ := by
    rw [hL, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero

  refine ⟨(UniqueFactorizationMonoid.normalizedFactors L).toFinset, ?_, ?_⟩
  · intro 𝔭 h𝔭
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
    obtain ⟨hp, hle⟩ := h𝔭
    have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hle))
    have hmax : 𝔭.IsMaximal := hp.isMaximal hne
    refine ⟨hmax, hne, ?_⟩

    have hdvd : Ideal.absNorm 𝔭 ∣ l ^ Module.finrank ℤ (𝓞 F) := by
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rwa [hL, Ideal.absNorm_span_singleton,
        show (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hmax.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hk))
    change l ∣ Ideal.absNorm 𝔭
    rw [hk]
    exact dvd_pow_self l hk0
  · intro I
    unfold Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo
    refine and_congr_right fun _ =>
      ⟨fun h => sup_eq_top_of_le_maximal ?_ h, fun h => sup_eq_top_of_le_maximal ?_ h⟩
    ·
      intro M hM hLM
      have hmem : M ∈ (UniqueFactorizationMonoid.normalizedFactors L).toFinset := by
        rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0]
        exact ⟨hM.isPrime, hLM⟩
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun 𝔭 => 𝔭) hmem)
    ·
      intro M hM hPM
      obtain ⟨𝔭, h𝔭, hle⟩ := (Ideal.IsPrime.prod_le hM.isPrime).mp hPM
      rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
      have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ h𝔭.2))
      have h𝔭M : 𝔭 = M := (h𝔭.1.isMaximal hne).eq_of_le hM.ne_top hle
      exact h𝔭M ▸ h𝔭.2

end GlobalTheory.PrimesAboveExistence
