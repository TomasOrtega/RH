import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Kum UpperTheory.V.B3

/- English proof (translation)
Establish `h : Prime ((l : ℤ))` using `Nat.prime_iff_prime_int.mp hl`. Rewrite using `[← MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃* ℤ)]`. Simplify using `using h`.
-/
private theorem prime_l {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.mp hl
  rw [← MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃* ℤ)]
  simpa using h

private noncomputable def vQ {l : ℕ} (hl : l.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l hl).ne_zero).mpr (prime_l hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l hl).ne_zero

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use `symm`. Apply `Ideal.IsMaximal.eq_of_le (vQ hl).isMaximal v.isPrime.ne_top` to reduce the goal to its premises. Use `show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `h`.
-/
private theorem eq_vQ {l : ℕ} (hl : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    v = vQ hl := by
  apply HeightOneSpectrum.ext
  symm
  apply Ideal.IsMaximal.eq_of_le (vQ hl).isMaximal v.isPrime.ne_top
  show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact h

/- English proof (translation)
Use `set J : Ideal ℤ := v.asIdeal.comap (Int.castRingHom (𝓞 ℚ)) with hJ`. Establish `hJp : J.IsPrime` using `Ideal.IsPrime.comap _`. Establish `hJb : J ≠ ⊥`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Introduce `hbot`.

Establish `hxe : ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) = x` using `by conv_rhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]`. Conclude with `(eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm`. Establish `hmem : Rat.ringOfIntegersEquiv x ∈ J`. Rewrite using `[hJ, Ideal.mem_comap]`. Simplify `hx` using `[hxe]`.

Rewrite `hmem` using `[hbot, Ideal.mem_bot]`. Apply `hx0` to reduce the goal to its premises. Rewrite using `[← hxe, hmem]`. Simplify using the standard rewrite rules. Take `⟨z, hzJ, hz⟩` from `hJp.exists_mem_prime_of_ne_bot hJb`.

Use `⟨z.natAbs, Int.prime_iff_natAbs_prime.mp hz, ?_⟩` and prove the remaining obligations. Establish `hz' : ((z.natAbs : ℤ)) ∈ J`. Break down `Int.natAbs_eq z with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `hzJ`.

Establish `: ((z.natAbs : ℤ)) = -z` using `by omega`. Rewrite using `[this]`. Conclude with `J.neg_mem hzJ`. Rewrite `hz'` using `[hJ, Ideal.mem_comap]`. Simplify using `using hz'`.
-/
private theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  set J : Ideal ℤ := v.asIdeal.comap (Int.castRingHom (𝓞 ℚ)) with hJ
  have hJp : J.IsPrime := Ideal.IsPrime.comap _
  have hJb : J ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hxe : ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) = x := by
      conv_rhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]
      exact (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
    have hmem : Rat.ringOfIntegersEquiv x ∈ J := by
      rw [hJ, Ideal.mem_comap]
      simpa [hxe] using hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    rw [← hxe, hmem]
    simp
  obtain ⟨z, hzJ, hz⟩ := hJp.exists_mem_prime_of_ne_bot hJb
  refine ⟨z.natAbs, Int.prime_iff_natAbs_prime.mp hz, ?_⟩
  have hz' : ((z.natAbs : ℤ)) ∈ J := by
    rcases Int.natAbs_eq z with h | h
    · rw [← h]; exact hzJ
    · have : ((z.natAbs : ℤ)) = -z := by omega
      rw [this]; exact J.neg_mem hzJ
  rw [hJ, Ideal.mem_comap] at hz'
  simpa using hz'

/- English proof (translation)
Introduce `Ω _ _ _`. Take `⟨hTop, hOver, hNe, hIff⟩` from `placeDict ℚ Ω`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Take `⟨A, hA⟩` from `exists_isPlaceOver (F := ℚ) Ω (vQ hp)`.

Use `⟨A, (hIff A (vQ hp) p hA).mpr ?_⟩` and prove the remaining obligations. Use `show ((p : ℕ) : 𝓞 ℚ) ∈ Ideal.span {((p : ℕ) : 𝓞 ℚ)}`. Conclude with `Ideal.subset_span rfl`. Introduce `B`. Distinguish the cases in `hB : B = ⊤`.

Use `left`. Rewrite using `[hB]`. Conclude with `hTop`. Use `right`. Take `⟨v, hv⟩` from `hOver B hB`.

Take `⟨p, hp, hpv⟩` from `exists_prime_mem v`. Conclude with `⟨p, hp, (hIff B v p hv).mpr hpv⟩`. Introduce `p A B hp hA hB`. Take `⟨vA, hvA⟩` from `hOver A (hNe A p hp.ne_zero hA)`. Take `⟨vB, hvB⟩` from `hOver B (hNe B p hp.ne_zero hB)`.

Establish `eA` using `eq_vQ hp vA ((hIff A vA p hvA).mp hA)`. Establish `eB` using `eq_vQ hp vB ((hIff B vB p hvB).mp hB)`. Substitute `eA` using the available equality. Rewrite `hvB` using `[eB]`. Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver hvA hvB`.

Use `⟨σ, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← hσ]`. Conclude with `GlobalTheory.Cut.ShaBound.conj_mem_Ine' hx`.
-/
theorem UpperTheory.V.B3.placesQ :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω],
    (∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) ∧
    (∀ B : ValuationSubring Ω, Ine (F := ℚ) B = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ B.valuation (p : Ω) < 1) ∧
    ∀ (p : ℕ) (A B : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → B.valuation (p : Ω) < 1 →
      ∃ g : G ℚ Ω, ∀ x ∈ Ine (F := ℚ) B, g⁻¹ * x * g ∈ Ine (F := ℚ) A := by
  intro Ω _ _ _
  obtain ⟨hTop, hOver, hNe, hIff⟩ := placeDict ℚ Ω
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hA⟩ := exists_isPlaceOver (F := ℚ) Ω (vQ hp)
    refine ⟨A, (hIff A (vQ hp) p hA).mpr ?_⟩
    show ((p : ℕ) : 𝓞 ℚ) ∈ Ideal.span {((p : ℕ) : 𝓞 ℚ)}
    exact Ideal.subset_span rfl
  · intro B
    by_cases hB : B = ⊤
    · left
      rw [hB]
      exact hTop
    · right
      obtain ⟨v, hv⟩ := hOver B hB
      obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
      exact ⟨p, hp, (hIff B v p hv).mpr hpv⟩
  · intro p A B hp hA hB
    obtain ⟨vA, hvA⟩ := hOver A (hNe A p hp.ne_zero hA)
    obtain ⟨vB, hvB⟩ := hOver B (hNe B p hp.ne_zero hB)
    have eA := eq_vQ hp vA ((hIff A vA p hvA).mp hA)
    have eB := eq_vQ hp vB ((hIff B vB p hvB).mp hB)
    subst eA
    rw [eB] at hvB
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hvA hvB
    refine ⟨σ, fun x hx => ?_⟩
    rw [← hσ] at hx
    exact GlobalTheory.Cut.ShaBound.conj_mem_Ine' hx
