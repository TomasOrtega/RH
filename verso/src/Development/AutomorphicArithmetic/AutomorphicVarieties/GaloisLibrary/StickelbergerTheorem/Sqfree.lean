import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Introduce `I h`. Rewrite `h` using `[Finset.prod_empty]`. Establish `h1` using `Ideal.dvd_iff_le.1 h`. Rewrite `h1` using `[Ideal.one_eq_top, top_le_iff]`.

Use `⟨∅, Finset.empty_subset _, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_empty, h1, Ideal.one_eq_top]`. Introduce `a t ha ih I h`. Rewrite `h` using `[Finset.prod_insert ha]`. Take `⟨K, hK⟩` from `h`.

Establish `hpa` using `hP a`. Distinguish the cases in `hd : P a ∣ I`. Take `⟨J, rfl⟩` from `hd`. Establish `h' : J ∣ ∏ i ∈ t, P i` using `⟨K, mul_left_cancel₀ hpa.ne_zero (by rw [hK, mul_assoc])⟩`. Take `⟨u, hu, rfl⟩` from `ih J h'`.

Use `⟨insert a u, Finset.insert_subset_insert a hu, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert (fun h => ha (hu h))]`. Establish `hk : P a ∣ K` using `(hpa.dvd_or_dvd ⟨_, hK.symm⟩).resolve_left hd`. Take `⟨L, rfl⟩` from `hk`. Establish `h' : I ∣ ∏ i ∈ t, P i` using `⟨L, mul_left_cancel₀ hpa.ne_zero (by rw [hK]; exact mul_left_comm _ _ _)⟩`.

Take `⟨u, hu, e⟩` from `ih I h'`. Conclude with `⟨u, hu.trans (Finset.subset_insert a t), e⟩`.
-/
private theorem sub_prod {R : Type} [CommRing R] [IsDedekindDomain R] {ι : Type} (P : ι → Ideal R)
    (hP : ∀ i, Prime (P i)) (t : Finset ι) :
    ∀ I : Ideal R, I ∣ ∏ i ∈ t, P i → ∃ u : Finset ι, u ⊆ t ∧ I = ∏ i ∈ u, P i := by
  classical
  refine Finset.induction_on t ?_ ?_
  · intro I h
    rw [Finset.prod_empty] at h
    have h1 := Ideal.dvd_iff_le.1 h
    rw [Ideal.one_eq_top, top_le_iff] at h1
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [Finset.prod_empty, h1, Ideal.one_eq_top]
  · intro a t ha ih I h
    rw [Finset.prod_insert ha] at h
    obtain ⟨K, hK⟩ := h
    have hpa := hP a
    by_cases hd : P a ∣ I
    · obtain ⟨J, rfl⟩ := hd
      have h' : J ∣ ∏ i ∈ t, P i := ⟨K, mul_left_cancel₀ hpa.ne_zero (by rw [hK, mul_assoc])⟩
      obtain ⟨u, hu, rfl⟩ := ih J h'
      refine ⟨insert a u, Finset.insert_subset_insert a hu, ?_⟩
      rw [Finset.prod_insert (fun h => ha (hu h))]
    · have hk : P a ∣ K := (hpa.dvd_or_dvd ⟨_, hK.symm⟩).resolve_left hd
      obtain ⟨L, rfl⟩ := hk
      have h' : I ∣ ∏ i ∈ t, P i := ⟨L, mul_left_cancel₀ hpa.ne_zero (by rw [hK]; exact mul_left_comm _ _ _)⟩
      obtain ⟨u, hu, e⟩ := ih I h'
      exact ⟨u, hu.trans (Finset.subset_insert a t), e⟩

/- English proof (translation)
Introduce `R _ _ ι _ P hinj hP x s hdiv hs`. Take `⟨u, -, hu⟩` from `sub_prod P hP Finset.univ _ hdiv`. Rewrite using `[hu]`. Use `congr 1`. Use extensionality with `i`.

Rewrite using `[hs i, ← Ideal.dvd_span_singleton, hu, (hP i).dvd_finset_prod_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hi`. Conclude with `⟨i, hi, dvd_rfl⟩`. Introduce and unpack `⟨j, hj, hij⟩`.

Establish `e` using `((hP i).dvd_prime_iff_associated (hP j)).1 hij`. Rewrite `e` using `[associated_iff_eq]`. Rewrite using `[hinj e]` and apply the resulting hypothesis.
-/
theorem UpperTheory.V.Stick.sqfree :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (P : ι → Ideal R),
    Function.Injective P → (∀ i, Prime (P i)) → ∀ (x : R) (s : Finset ι), Ideal.span {x} ∣ ∏ i, P i →
    (∀ i, i ∈ s ↔ x ∈ P i) → Ideal.span {x} = ∏ i ∈ s, P i := by
  classical
  intro R _ _ ι _ P hinj hP x s hdiv hs
  obtain ⟨u, -, hu⟩ := sub_prod P hP Finset.univ _ hdiv
  rw [hu]
  congr 1
  ext i
  rw [hs i, ← Ideal.dvd_span_singleton, hu, (hP i).dvd_finset_prod_iff]
  constructor
  · intro hi
    exact ⟨i, hi, dvd_rfl⟩
  · rintro ⟨j, hj, hij⟩
    have e := ((hP i).dvd_prime_iff_associated (hP j)).1 hij
    rw [associated_iff_eq] at e
    rwa [hinj e]
