import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l hl D`. Establish `hn : l.Prime` using `hl.out`. Establish `hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hn.ne_zero` after adjusting the coercions.

Establish `hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal` using `inferInstance`. Use `le_trans (Finset.card_le_card_of_injOn (t := IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F)) (fun p => p.asIdeal) ?_ ?_) (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0)` and prove the remaining obligations. Introduce `p hp`. Rewrite `hp` using `[D.hS]`. Establish `hp' : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal` using `hp`.

Rewrite using `[Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]`. Use `p.isPrime` as an intermediate fact. Use `⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Conclude with `hp'`.

Introduce `p _ p' _ h`. Conclude with `HeightOneSpectrum.ext h`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.cardAbove :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l), D.S.card ≤ Module.finrank ℚ F := by
  intro F Ω _ _ _ _ _ l hl D
  classical
  have hn : l.Prime := hl.out
  have hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne_zero
  have hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal := inferInstance
  refine le_trans (Finset.card_le_card_of_injOn
    (t := IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F))
    (fun p => p.asIdeal) ?_ ?_) (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0)
  · intro p hp
    rw [D.hS] at hp
    have hp' : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal := hp
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    have := p.isPrime
    refine ⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hp'
  · intro p _ p' _ h
    exact HeightOneSpectrum.ext h
