import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory

open NumberField IsDedekindDomain in
open scoped Classical in
/- English proof (translation)
Use `set I : Ideal ℤ := P.asIdeal.under ℤ with hI`. Establish `hN : (Ideal.absNorm P.asIdeal : ℤ) ∈ I`. Rewrite using `[hI, Ideal.mem_comap]`. Simplify using `using Ideal.absNorm_mem P.asIdeal`. Establish `hN0 : (Ideal.absNorm P.asIdeal : ℤ) ≠ 0`.

Use `_root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hIbot : I ≠ ⊥` using `fun h => hN0 (by simpa [h] using hN)`. Establish `hprime` using `Submodule.IsPrincipal.prime_generator_of_isPrime I hIbot`. Use `set g := Submodule.IsPrincipal.generator I`.

Use `⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_, ?_⟩` and prove the remaining obligations. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[Int.span_natAbs, Ideal.span_singleton_generator]`. Establish `hpr : Prime ((g.natAbs : ℕ) : ℤ)`. Rewrite using `[Int.natCast_natAbs]`.

Conclude with `hprime.abs`. Use `haveI : P.asIdeal.LiesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) := ⟨by rw [Int.span_natAbs, Ideal.span_singleton_generator]⟩`. Conclude with `⟨_, (Ideal.absNorm_eq_pow_inertiaDeg P.asIdeal hpr).trans (by rw [Int.natAbs_natCast])⟩`.
-/
private lemma exists_prime_liesOver_absNorm_eq_pow (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) ∧
      ∃ f : ℕ, Ideal.absNorm P.asIdeal = q ^ f := by
  set I : Ideal ℤ := P.asIdeal.under ℤ with hI
  have hN : (Ideal.absNorm P.asIdeal : ℤ) ∈ I := by
    rw [hI, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem P.asIdeal
  have hN0 : (Ideal.absNorm P.asIdeal : ℤ) ≠ 0 := by
    have := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
    omega
  have hIbot : I ≠ ⊥ := fun h => hN0 (by simpa [h] using hN)
  have hprime := Submodule.IsPrincipal.prime_generator_of_isPrime I hIbot
  set g := Submodule.IsPrincipal.generator I
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Int.span_natAbs, Ideal.span_singleton_generator]
  · have hpr : Prime ((g.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hprime.abs
    haveI : P.asIdeal.LiesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) :=
      ⟨by rw [Int.span_natAbs, Ideal.span_singleton_generator]⟩
    exact ⟨_, (Ideal.absNorm_eq_pow_inertiaDeg P.asIdeal hpr).trans (by rw [Int.natAbs_natCast])⟩

open NumberField IsDedekindDomain in
open scoped Classical in

/- English proof (translation)
Introduce `K _ _`. Use `choose q hq hlies f hf using exists_prime_liesOver_absNorm_eq_pow K`. Use `set d := Module.finrank ℚ K`. Establish `hfib : ∀ (T : Finset {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime}) (r : ℕ), (T.filter fun P => q P.1 = r).card ≤ d`. Introduce `T r`.

Distinguish the cases in `hr : ∃ P ∈ T, q P.1 = r`. Take `⟨P₀, -, rfl⟩` from `hr`. Establish `hspan : Ideal.span {((q P₀.1 : ℕ) : ℤ)} ≠ ⊥`. Simplify using `using (hq P₀.1).ne_zero`. Use `haveI hsp : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsPrime := (Ideal.span_singleton_prime (by simpa using (hq P₀.1).ne_zero)).mpr (Nat.prime_iff_prime_int.mp (hq P₀.1))`.

Use `haveI : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsMaximal := hsp.isMaximal hspan`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.card_le_card_of_injOn (fun P => P.1.asIdeal) ?_ ?_` and prove the remaining obligations. Introduce `P hP`. Rewrite using `[Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hspan]`.

Establish `hPq` using `(Finset.mem_filter.mp hP).2`. Use `haveI := hlies P.1`. Conclude with `⟨P.1.isPrime, by rw [← hPq]; infer_instance⟩`. Introduce `P _ P' _ h`. Conclude with `Subtype.ext (HeightOneSpectrum.ext h)`.

Use `_ ≤ d := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hspan`. Use `push_neg at hr`. Rewrite using `[Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr hr)]`. Conclude with `Nat.zero_le _`. Establish `hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2` using `Real.summable_one_div_nat_pow.mpr one_lt_two`.

Use `summable_of_sum_le (c := d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) (fun P => by positivity) ?_` and prove the remaining obligations. Introduce `T`. Establish `hle : ∀ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ ≤ 1 / ((q P.1 : ℕ) : ℝ) ^ 2`. Introduce `P _`. Establish `h2` using `_root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P.1`.

Establish `hf2 : 2 ≤ f P.1`. Break down `Nat.lt_or_ge (f P.1) 2 with h | h` into its components or cases. Use `interval_cases hfP : f P.1`. Rewrite `h2` using `[hf P.1, hfP]`. Simplify using `at h2`.

Conclude with `absurd (by rw [hf P.1, hfP, pow_one]; exact hq P.1) P.2`. Conclude with `h`. Rewrite using `[one_div]`. Apply `inv_anti₀ (by have := (hq P.1).pos; positivity)` to reduce the goal to its premises. Rewrite using `[hf P.1]`.

Conclude with `Nat.pow_le_pow_right (hq P.1).pos hf2` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ ∑ r ∈ T.image (fun P => q P.1), (d : ℝ) * (1 / (r : ℝ) ^ 2) := by`.

Use `Finset.sum_le_sum fun r _ => ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `hfib T r` after adjusting the coercions. Use `_ = d * ∑ r ∈ T.image (fun P => q P.1), 1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]`. Use `_ ≤ d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by gcongr`.

Conclude with `hsum.sum_le_tsum _ (fun n _ => by positivity)`.
-/
theorem _root_.GlobalTheory.summable_inv_absNorm_of_not_prime :
    ∀ (K : Type) [Field K] [NumberField K],
      Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} =>
        ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  intro K _ _
  choose q hq hlies f hf using exists_prime_liesOver_absNorm_eq_pow K
  set d := Module.finrank ℚ K
  have hfib : ∀ (T : Finset {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime})
      (r : ℕ), (T.filter fun P => q P.1 = r).card ≤ d := by
    intro T r
    by_cases hr : ∃ P ∈ T, q P.1 = r
    · obtain ⟨P₀, -, rfl⟩ := hr
      have hspan : Ideal.span {((q P₀.1 : ℕ) : ℤ)} ≠ ⊥ := by
        simpa using (hq P₀.1).ne_zero
      haveI hsp : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by simpa using (hq P₀.1).ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp (hq P₀.1))
      haveI : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsMaximal := hsp.isMaximal hspan
      calc (T.filter fun P => q P.1 = q P₀.1).card
          ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((q P₀.1 : ℕ) : ℤ)}) (𝓞 K)).card := by
            refine Finset.card_le_card_of_injOn (fun P => P.1.asIdeal) ?_ ?_
            · intro P hP
              rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hspan]
              have hPq := (Finset.mem_filter.mp hP).2
              haveI := hlies P.1
              exact ⟨P.1.isPrime, by rw [← hPq]; infer_instance⟩
            · intro P _ P' _ h
              exact Subtype.ext (HeightOneSpectrum.ext h)
        _ ≤ d := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hspan
    · push_neg at hr
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr hr)]
      exact Nat.zero_le _
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  refine summable_of_sum_le (c := d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) (fun P => by positivity) ?_
  intro T
  have hle : ∀ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ ≤ 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := by
    intro P _
    have h2 := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P.1
    have hf2 : 2 ≤ f P.1 := by
      rcases Nat.lt_or_ge (f P.1) 2 with h | h
      · interval_cases hfP : f P.1
        · rw [hf P.1, hfP] at h2; simp at h2
        · exact absurd (by rw [hf P.1, hfP, pow_one]; exact hq P.1) P.2
      · exact h
    rw [one_div]
    apply inv_anti₀ (by have := (hq P.1).pos; positivity)
    rw [hf P.1]
    exact_mod_cast Nat.pow_le_pow_right (hq P.1).pos hf2
  calc ∑ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹
      ≤ ∑ P ∈ T, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum hle
    _ = ∑ r ∈ T.image (fun P => q P.1), ∑ P ∈ T with q P.1 = r, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ r ∈ T.image (fun P => q P.1),
          ((T.filter fun P => q P.1 = r).card : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ r ∈ T.image (fun P => q P.1), (d : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun r _ => ?_
        gcongr
        exact_mod_cast hfib T r
    _ = d * ∑ r ∈ T.image (fun P => q P.1), 1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
        gcongr
        exact hsum.sum_le_tsum _ (fun n _ => by positivity)

end GlobalTheory
