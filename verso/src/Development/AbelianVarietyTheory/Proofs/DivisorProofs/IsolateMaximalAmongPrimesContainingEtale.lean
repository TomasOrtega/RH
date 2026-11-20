import Mathlib

namespace GlobalTheory.EtaleIsolate

/- English proof (translation)
Establish `key : ∀ Q : Ideal A, Q.IsPrime → I ≤ Q → (Q.map (Ideal.Quotient.mk I)).IsPrime ∧ (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q`. Introduce `Q hQ hIQ`. Establish `hk : RingHom.ker (Ideal.Quotient.mk I) ≤ Q` using `by rwa [Ideal.mk_ker]`. Use `⟨Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hk, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIQ]`.

Use `⟨((IsArtinianRing.setOfPred_isPrime_finite (A ⧸ I)).image (Ideal.comap (Ideal.Quotient.mk I))).subset fun Q hQ => ?_, fun Q hQ hIQ => ?_⟩` and prove the remaining obligations. Conclude with `⟨_, (key Q hQ.1 hQ.2).1, (key Q hQ.1 hQ.2).2⟩`. Use `haveI := (key Q hQ hIQ).1`. Establish `hm` using `IsArtinianRing.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk I))`. Rewrite using `[← (key Q hQ hIQ).2]`.

Conclude with `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`.
-/
theorem primes_above_finite {A : Type*} [CommRing A] (I : Ideal A) [IsArtinianRing (A ⧸ I)] :
    {Q : Ideal A | Q.IsPrime ∧ I ≤ Q}.Finite ∧
      ∀ Q : Ideal A, Q.IsPrime → I ≤ Q → Q.IsMaximal := by
  have key : ∀ Q : Ideal A, Q.IsPrime → I ≤ Q →
      (Q.map (Ideal.Quotient.mk I)).IsPrime ∧
        (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q := by
    intro Q hQ hIQ
    have hk : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by rwa [Ideal.mk_ker]
    refine ⟨Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hk, ?_⟩
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIQ]
  refine ⟨((IsArtinianRing.setOfPred_isPrime_finite (A ⧸ I)).image
    (Ideal.comap (Ideal.Quotient.mk I))).subset fun Q hQ => ?_, fun Q hQ hIQ => ?_⟩
  · exact ⟨_, (key Q hQ.1 hQ.2).1, (key Q hQ.1 hQ.2).2⟩
  · haveI := (key Q hQ hIQ).1
    have hm := IsArtinianRing.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk I))
    rw [← (key Q hQ hIQ).2]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

/- English proof (translation)
Establish `hr0 : f ∈ nonZeroDivisors B` using `mem_nonZeroDivisors_of_ne_zero hf`. Use `haveI : IsArtinian B (B ⧸ Ideal.span {f}) := (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_quotient_span_singleton B hr0)).2`. Conclude with `isArtinian_of_tower B inferInstance`.
-/
theorem isArtinianRing_quot_span (B : Type*) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : IsArtinianRing (B ⧸ Ideal.span {f}) := by
  have hr0 : f ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hf
  haveI : IsArtinian B (B ⧸ Ideal.span {f}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton B hr0)).2
  exact isArtinian_of_tower B inferInstance

/- English proof (translation)
Use `letI : Field (B ⧸ P) := Ideal.Quotient.field P`. Use `haveI : Algebra.Etale (B ⧸ P) (D ⧸ P.map (algebraMap B D)) := Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D P).symm`. Use `haveI : Module.Finite (B ⧸ P) (D ⧸ P.map (algebraMap B D)) := Algebra.FormallyUnramified.finite_of_free _ _`. Conclude with `IsArtinianRing.of_finite (B ⧸ P) _`.
-/
theorem isArtinianRing_fibre (B D : Type*) [CommRing B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (P : Ideal B) [P.IsMaximal] :
    IsArtinianRing (D ⧸ P.map (algebraMap B D)) := by
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.Etale (B ⧸ P) (D ⧸ P.map (algebraMap B D)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D P).symm
  haveI : Module.Finite (B ⧸ P) (D ⧸ P.map (algebraMap B D)) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  exact IsArtinianRing.of_finite (B ⧸ P) _

/- English proof (translation)
Use `haveI := isArtinianRing_quot_span B f hf`. Take `⟨hBfin, hBmax⟩` from `primes_above_finite (Ideal.span {f})`. Use `set S : Set (Ideal D) := {Q' | Q'.IsPrime ∧ algebraMap B D f ∈ Q'} with hS`. Use `set T : Set (Ideal B) := {P | P.IsPrime ∧ Ideal.span {f} ≤ P} with hT`. Establish `hsub : S ⊆ ⋃ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'}`.

Introduce and unpack `Q' ⟨hQ', hfQ'⟩`. Use `Set.mem_biUnion (x := Q'.comap (algebraMap B D)) ⟨Ideal.IsPrime.comap _, ?_⟩ ⟨hQ', Ideal.map_comap_le⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hfQ'`. Establish `hfib : ∀ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'}.Finite ∧ ∀ Q' : Ideal D, Q'.IsPrime → P.map (algebraMap B D) ≤ Q' → Q'.IsMaximal`.

Introduce and unpack `P ⟨hP, hfP⟩`. Use `haveI := hBmax P hP hfP`. Use `haveI := isArtinianRing_fibre B D P`. Conclude with `primes_above_finite _`. Establish `hSfin : S.Finite` using `(hBfin.biUnion fun P hP => (hfib P hP).1).subset hsub`.

Establish `hSmax : ∀ Q' ∈ S, Q'.IsMaximal` using `fun Q' hQ' => by`. Take `⟨P, hP, hQ'P⟩` from `Set.mem_iUnion₂.mp (hsub hQ')`. Conclude with `(hfib P hP).2 Q' hQ'P.1 hQ'P.2`. Establish `hch : ∀ Q' ∈ S, Q' ≠ Q → ∃ x, x ∈ Q' ∧ x ∉ Q` using `fun Q' hQ' hne => by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne ((hSmax Q' hQ').eq_of_le hQ.ne_top h)`. Use `choose! x hxmem hxnot using hch`. Use `⟨∏ Q' ∈ hSfin.toFinset.filter (· ≠ Q), x Q', ?_, ?_⟩` and prove the remaining obligations. Introduce `h haveI := hQ.isPrime`.

Take `⟨Q', hQ', hmem⟩` from `Ideal.IsPrime.prod_mem_iff.mp h`. Rewrite `hQ'` using `[Finset.mem_filter, Set.Finite.mem_toFinset]`. Conclude with `hxnot Q' hQ'.1 hQ'.2 hmem`. Introduce `Q' hQ' hfQ' hg`. Assume the negation of the conclusion as `hne`.

Apply `hg` to reduce the goal to its premises. Establish `hmem : Q' ∈ hSfin.toFinset.filter (· ≠ Q)` using `Finset.mem_filter.2 ⟨hSfin.mem_toFinset.2 ⟨hQ', hfQ'⟩, hne⟩`. Rewrite using `[← Finset.prod_erase_mul _ _ hmem]`. Conclude with `Ideal.mul_mem_left _ _ (hxmem Q' ⟨hQ', hfQ'⟩ hne)`.
-/
theorem exists_isolating (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D]
    [Algebra B D] [Algebra.Etale B D] (f : B) (hf : f ≠ 0) (Q : Ideal D) (hQ : Q.IsMaximal) :
    ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q := by
  classical
  haveI := isArtinianRing_quot_span B f hf
  obtain ⟨hBfin, hBmax⟩ := primes_above_finite (Ideal.span {f})
  set S : Set (Ideal D) := {Q' | Q'.IsPrime ∧ algebraMap B D f ∈ Q'} with hS
  set T : Set (Ideal B) := {P | P.IsPrime ∧ Ideal.span {f} ≤ P} with hT
  have hsub : S ⊆ ⋃ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'} := by
    rintro Q' ⟨hQ', hfQ'⟩
    refine Set.mem_biUnion (x := Q'.comap (algebraMap B D)) ⟨Ideal.IsPrime.comap _, ?_⟩
      ⟨hQ', Ideal.map_comap_le⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hfQ'
  have hfib : ∀ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'}.Finite ∧
      ∀ Q' : Ideal D, Q'.IsPrime → P.map (algebraMap B D) ≤ Q' → Q'.IsMaximal := by
    rintro P ⟨hP, hfP⟩
    haveI := hBmax P hP hfP
    haveI := isArtinianRing_fibre B D P
    exact primes_above_finite _
  have hSfin : S.Finite := (hBfin.biUnion fun P hP => (hfib P hP).1).subset hsub
  have hSmax : ∀ Q' ∈ S, Q'.IsMaximal := fun Q' hQ' => by
    obtain ⟨P, hP, hQ'P⟩ := Set.mem_iUnion₂.mp (hsub hQ')
    exact (hfib P hP).2 Q' hQ'P.1 hQ'P.2
  have hch : ∀ Q' ∈ S, Q' ≠ Q → ∃ x, x ∈ Q' ∧ x ∉ Q := fun Q' hQ' hne => by
    by_contra h
    push_neg at h
    exact hne ((hSmax Q' hQ').eq_of_le hQ.ne_top h)
  choose! x hxmem hxnot using hch
  refine ⟨∏ Q' ∈ hSfin.toFinset.filter (· ≠ Q), x Q', ?_, ?_⟩
  · intro h
    haveI := hQ.isPrime
    obtain ⟨Q', hQ', hmem⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hQ'
    exact hxnot Q' hQ'.1 hQ'.2 hmem
  · intro Q' hQ' hfQ' hg
    by_contra hne
    apply hg
    have hmem : Q' ∈ hSfin.toFinset.filter (· ≠ Q) :=
      Finset.mem_filter.2 ⟨hSfin.mem_toFinset.2 ⟨hQ', hfQ'⟩, hne⟩
    rw [← Finset.prod_erase_mul _ _ hmem]
    exact Ideal.mul_mem_left _ _ (hxmem Q' ⟨hQ', hfQ'⟩ hne)

/- English proof (translation)
Introduce `B D _ _ _ _ _ f hf Q hQ` and use `exists_isolating B D f hf Q hQ`.
-/
theorem isolate_maximal_among_primes_containing : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (Q : Ideal D), Q.IsMaximal →
    ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q :=
  fun B D _ _ _ _ _ f hf Q hQ => exists_isolating B D f hf Q hQ

end GlobalTheory.EtaleIsolate
