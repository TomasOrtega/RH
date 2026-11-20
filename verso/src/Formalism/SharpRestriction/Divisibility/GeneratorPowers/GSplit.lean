import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

open NumberField IsDedekindDomain UniqueFactorizationMonoid

/- English proof (translation)
Use `set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hIdef`. Use `set p' : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hp'def`. Establish `hmax : p'.IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hp0 : p' ≠ ⊥`. Rewrite using `[hp'def, Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hp.ne_zero` after adjusting the coercions. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p' = I`. Rewrite using `[hp'def, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hI0 : I ≠ ⊥`. Rewrite using `[hIdef, Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hp.ne_zero` after adjusting the coercions. Use `set M := normalizedFactors I with hMdef`. Establish `hmem : ∀ P : Ideal (𝓞 E), P ∈ M ↔ P.IsPrime ∧ I ≤ P` using `fun P => Ideal.mem_normalizedFactors_iff hI0`. Establish `hne : ∀ P ∈ M, P ≠ ⊥` using `fun P hP h0 => hI0 (eq_bot_iff.2 (h0 ▸ ((hmem P).1 hP).2))`. Establish `hlies : ∀ P ∈ M, P.LiesOver p'`.

Introduce `P hP`. Take `⟨hPp, hIP⟩` from `(hmem P).1 hP`. Establish `hle : p' ≤ P.under ℤ`. Rewrite using `[hp'def, Ideal.span_le, Set.singleton_subset_iff]`. Use `show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P`.

Rewrite using `[map_natCast]`. Conclude with `hIP (Ideal.subset_span rfl)`. Establish `hnt : P.under ℤ ≠ ⊤`. Introduce `ht`. Apply `hPp.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : (1 : ℤ) ∈ P.under ℤ` using `by rw [ht]; trivial`. Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 E) 1 ∈ P at h1`. Rewrite `h1` using `[map_one]`. Then use the resulting hypothesis. Conclude with `⟨hmax.eq_of_le hnt hle⟩`.

Establish `hcard1 : M.toFinset.card = Module.finrank ℚ E`. Rewrite using `[← h, ← Set.ncard_coe_finset]`. Establish `himg : HeightOneSpectrum.asIdeal '' {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} = (M.toFinset : Set (Ideal (𝓞 E)))`. Use extensionality with `P`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Use `(hmem _).2 ⟨v.isPrime, ?_⟩` and prove the remaining obligations. Rewrite using `[hIdef, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hv`.

Introduce `hP`. Take `⟨hPp, hIP⟩` from `(hmem P).1 hP`. Conclude with `⟨⟨P, hPp, hne P hP⟩, hIP (Ideal.subset_span rfl), rfl⟩`. Rewrite using `[← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]`. Use `haveI := hmax`.

Establish `hsum` using `Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0`. Establish `hfs : IsDedekindDomain.primesOverFinset p' (𝓞 E) = M.toFinset`. Rewrite using `[IsDedekindDomain.primesOverFinset, hmap, hMdef, factors_eq_normalizedFactors]`. Establish `hle : ∑ P ∈ M.toFinset, M.count P ≤ Module.finrank ℚ E`. Rewrite using `[← hsum, hfs]`.

Use `Finset.sum_le_sum fun P hP => ?_` and prove the remaining obligations. Establish `hPM : P ∈ M` using `Multiset.mem_toFinset.1 hP`. Use `haveI := hlies P hPM`. Use `haveI : P.IsPrime := ((hmem P).1 hPM).1`. Rewrite using `[Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (by rw [hmap]; exact hI0) ‹P.IsPrime› (hne P hPM), hmap]`.

Conclude with `Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg'_pos p' P)`. Establish `hcard : M.card = ∑ P ∈ M.toFinset, M.count P` using `(Multiset.toFinset_sum_count_eq M).symm`. Establish `h1 : M.toFinset.card ≤ M.card` using `Multiset.toFinset_card_le M`. Establish `hMc : M.card = Module.finrank ℚ E` using `le_antisymm (hcard ▸ hle) (hcard1 ▸ h1)`. Conclude with `⟨hMc, Multiset.toFinset_card_eq_card_iff_nodup.1 (hcard1.trans hMc.symm)⟩`.
-/
theorem split_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hIdef
  set p' : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hp'def
  have hmax : p'.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : p' ≠ ⊥ := by
    rw [hp'def, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p' = I := by
    rw [hp'def, Ideal.map_span, Set.image_singleton, map_natCast]
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := normalizedFactors I with hMdef

  have hmem : ∀ P : Ideal (𝓞 E), P ∈ M ↔ P.IsPrime ∧ I ≤ P := fun P => Ideal.mem_normalizedFactors_iff hI0
  have hne : ∀ P ∈ M, P ≠ ⊥ := fun P hP h0 => hI0 (eq_bot_iff.2 (h0 ▸ ((hmem P).1 hP).2))
  have hlies : ∀ P ∈ M, P.LiesOver p' := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
    have hle : p' ≤ P.under ℤ := by
      rw [hp'def, Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P
      rw [map_natCast]
      exact hIP (Ideal.subset_span rfl)
    have hnt : P.under ℤ ≠ ⊤ := by
      intro ht
      apply hPp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [ht]; trivial
      change algebraMap ℤ (𝓞 E) 1 ∈ P at h1
      rwa [map_one] at h1
    exact ⟨hmax.eq_of_le hnt hle⟩
  have hcard1 : M.toFinset.card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset]
    have himg : HeightOneSpectrum.asIdeal '' {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} =
        (M.toFinset : Set (Ideal (𝓞 E))) := by
      ext P
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine (hmem _).2 ⟨v.isPrime, ?_⟩
        rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]
        exact hv
      · intro hP
        obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
        exact ⟨⟨P, hPp, hne P hP⟩, hIP (Ideal.subset_span rfl), rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]
  haveI := hmax
  have hsum := Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0
  have hfs : IsDedekindDomain.primesOverFinset p' (𝓞 E) = M.toFinset := by
    rw [IsDedekindDomain.primesOverFinset, hmap, hMdef, factors_eq_normalizedFactors]
  have hle : ∑ P ∈ M.toFinset, M.count P ≤ Module.finrank ℚ E := by
    rw [← hsum, hfs]
    refine Finset.sum_le_sum fun P hP => ?_
    have hPM : P ∈ M := Multiset.mem_toFinset.1 hP
    haveI := hlies P hPM
    haveI : P.IsPrime := ((hmem P).1 hPM).1
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (by rw [hmap]; exact hI0) ‹P.IsPrime› (hne P hPM), hmap]
    exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg'_pos p' P)
  have hcard : M.card = ∑ P ∈ M.toFinset, M.count P := (Multiset.toFinset_sum_count_eq M).symm
  have h1 : M.toFinset.card ≤ M.card := Multiset.toFinset_card_le M
  have hMc : M.card = Module.finrank ℚ E := le_antisymm (hcard ▸ hle) (hcard1 ▸ h1)
  exact ⟨hMc, Multiset.toFinset_card_eq_card_iff_nodup.1 (hcard1.trans hMc.symm)⟩

open Formalism.BasicNotions in

/- English proof (translation)
The claim follows from `split_of_ncard (D.host.g_prime i) (D.nd.g_split i)`.
-/
theorem g_splits (D : D7) (i : Fin 2) :
    (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧
      (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup :=
  split_of_ncard (D.host.g_prime i) (D.nd.g_split i)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit
