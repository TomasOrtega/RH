import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
open NumberField IsDedekindDomain

namespace GlobalTheory

open NumberField IsDedekindDomain in

/- English proof (translation)
Rewrite using `[Ideal.liesOver_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hmem : (p : ℤ) ∈ Ideal.under ℤ P` using `h ▸ Ideal.subset_span rfl`. Simplify `hmem` using `[Ideal.under, Ideal.mem_comap]`.

Introduce `h`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Use `hmax.eq_of_le (inferInstance : (Ideal.under ℤ P).IsPrime).ne_top ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Simplify `h` using `[Ideal.under, Ideal.mem_comap]`.
-/
theorem _root_.GlobalTheory.splitPrime_liesOver_span_iff {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    P.LiesOver (Ideal.span {(p : ℤ)}) ↔ ((p : ℕ) : 𝓞 E) ∈ P := by
  rw [Ideal.liesOver_iff]
  constructor
  · intro h
    have hmem : (p : ℤ) ∈ Ideal.under ℤ P := h ▸ Ideal.subset_span rfl
    simpa [Ideal.under, Ideal.mem_comap] using hmem
  · intro h
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine hmax.eq_of_le (inferInstance : (Ideal.under ℤ P).IsPrime).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.under, Ideal.mem_comap] using h

open NumberField IsDedekindDomain in

/- English proof (translation)
Use `set q : Ideal ℤ := Ideal.span {(p : ℤ)} with hq`. Use `haveI hqmax : q.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hqbot : q ≠ ⊥`. Rewrite using `[hq, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions.

Establish `hmemv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal`. Unfold `_root_.Formalism.BasicNotions.placesOver at hv`. Conclude with `hv`. Use `haveI : v.asIdeal.LiesOver q := (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp v.asIdeal).2 hmemv`. Establish `hcard : (IsDedekindDomain.primesOverFinset q (𝓞 E)).card = Module.finrank ℚ E`.

Rewrite using `[← h, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hqbot]`. Establish `himage : (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) '' _root_.Formalism.BasicNotions.placesOver E p = q.primesOver (𝓞 E)`. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Establish `hw' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal`. Unfold `_root_.Formalism.BasicNotions.placesOver at hw`. Conclude with `hw`. Conclude with `⟨w.isPrime, (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp w.asIdeal).2 hw'⟩`. Introduce and unpack `⟨hPp, hPl⟩`.

Establish `hPmem : ((p : ℕ) : 𝓞 E) ∈ P` using `(_root_.GlobalTheory.splitPrime_liesOver_span_iff hp P).1 hPl`. Establish `hPbot : P ≠ ⊥`. Introduce `hb`. Rewrite `hPmem` using `[hb, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast hPmem)`.

Use `⟨⟨P, hPp, hPbot⟩, ?_, rfl⟩` and prove the remaining obligations. Unfold `_root_.Formalism.BasicNotions.placesOver`. Conclude with `hPmem`. Rewrite using `[← himage, Set.ncard_image_of_injective _ (fun a b hab => HeightOneSpectrum.ext hab)]`. Establish `hsum` using `Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := q) hqbot`.

Rewrite `hsum` using `[← hcard, Finset.card_eq_sum_ones]`. Establish `hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset q (𝓞 E), 1 ≤ q.ramificationIdx' P * q.inertiaDeg' P`. Introduce `P hP`. Rewrite `hP` using `[IsDedekindDomain.mem_primesOverFinset_iff hqbot]`. Take `⟨hPp, hPl⟩` from `hP`.

Use `haveI := hPp`. Use `haveI := hPl`. Establish `he : q.ramificationIdx' P ≠ 0` using `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hqbot`. Establish `hf : 0 < q.inertiaDeg' P` using `Ideal.inertiaDeg'_pos' q P`. Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he hf.ne')`.

Establish `hall` using `(Finset.sum_eq_sum_iff_of_le hpos).1 hsum.symm`. Establish `hvmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset q (𝓞 E)`. Rewrite using `[IsDedekindDomain.mem_primesOverFinset_iff hqbot]`. Conclude with `⟨v.isPrime, inferInstance⟩`. Take `⟨he, hf⟩` from `mul_eq_one.1 (hall _ hvmem).symm`.

Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hsq`. Establish `hle : Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ 2`. Rewrite using `[hq, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]`.

Simplify using `using hsq`. Unfold `Ideal.ramificationIdx' at he`. Distinguish the cases in `hb : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n}`. Establish `h2` using `le_csSup hb (show 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n} from hle)`. Use linear arithmetic over natural numbers and integers.

Rewrite `he` using `[Nat.sSup_of_not_bddAbove hb]`. Conclude with `zero_ne_one he`. Rewrite using `[← Ideal.ramificationIdx'_eq_ramificationIdx q v.asIdeal hqbot]`. Conclude with `he`. Rewrite using `[← Ideal.inertiaDeg'_eq_inertiaDeg q v.asIdeal]`.

Conclude with `hf`.
-/
theorem _root_.GlobalTheory.unramified_degree_one_of_ncard_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ)
    (hp : p.Prime) (h : (_root_.Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ _root_.Formalism.BasicNotions.placesOver E p) :
    ((p : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
      v.asIdeal.inertiaDeg ℤ = 1 := by
  set q : Ideal ℤ := Ideal.span {(p : ℤ)} with hq
  haveI hqmax : q.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hqbot : q ≠ ⊥ := by
    rw [hq, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmemv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    unfold _root_.Formalism.BasicNotions.placesOver at hv
    exact hv
  haveI : v.asIdeal.LiesOver q := (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp v.asIdeal).2 hmemv
  have hcard : (IsDedekindDomain.primesOverFinset q (𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hqbot]
    have himage : (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) '' _root_.Formalism.BasicNotions.placesOver E p =
        q.primesOver (𝓞 E) := by
      ext P
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
          unfold _root_.Formalism.BasicNotions.placesOver at hw
          exact hw
        exact ⟨w.isPrime, (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp w.asIdeal).2 hw'⟩
      · rintro ⟨hPp, hPl⟩
        have hPmem : ((p : ℕ) : 𝓞 E) ∈ P := (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp P).1 hPl
        have hPbot : P ≠ ⊥ := by
          intro hb
          rw [hb, Ideal.mem_bot] at hPmem
          exact hp.ne_zero (by exact_mod_cast hPmem)
        refine ⟨⟨P, hPp, hPbot⟩, ?_, rfl⟩
        unfold _root_.Formalism.BasicNotions.placesOver
        exact hPmem
    rw [← himage, Set.ncard_image_of_injective _ (fun a b hab => HeightOneSpectrum.ext hab)]
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := q) hqbot
  rw [← hcard, Finset.card_eq_sum_ones] at hsum
  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset q (𝓞 E),
      1 ≤ q.ramificationIdx' P * q.inertiaDeg' P := by
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff hqbot] at hP
    obtain ⟨hPp, hPl⟩ := hP
    haveI := hPp
    haveI := hPl
    have he : q.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hqbot
    have hf : 0 < q.inertiaDeg' P := Ideal.inertiaDeg'_pos' q P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he hf.ne')
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 hsum.symm
  have hvmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset q (𝓞 E) := by
    rw [IsDedekindDomain.mem_primesOverFinset_iff hqbot]
    exact ⟨v.isPrime, inferInstance⟩
  obtain ⟨he, hf⟩ := mul_eq_one.1 (hall _ hvmem).symm
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  refine ⟨?_, ?_, ?_⟩
  · intro hsq
    have hle : Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ 2 := by
      rw [hq, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
      simpa using hsq
    unfold Ideal.ramificationIdx' at he
    by_cases hb : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n}
    · have h2 := le_csSup hb (show 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n}
        from hle)
      omega
    · rw [Nat.sSup_of_not_bddAbove hb] at he
      exact zero_ne_one he
  · rw [← Ideal.ramificationIdx'_eq_ramificationIdx q v.asIdeal hqbot]
    exact he
  · rw [← Ideal.inertiaDeg'_eq_inertiaDeg q v.asIdeal]
    exact hf

end GlobalTheory
