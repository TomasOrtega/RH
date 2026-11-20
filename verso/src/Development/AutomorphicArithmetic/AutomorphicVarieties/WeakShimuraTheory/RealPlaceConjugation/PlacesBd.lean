import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DecIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.NcardPlacesDividingLeOfOrbitBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SupIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbIndex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [plDvd, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion. Establish `key : ∀ M : ℕ, M ≠ 0 → ((M : 𝓞 F) ∈ v.asIdeal) → ∃ p ∈ M.primeFactors, (p : 𝓞 F) ∈ v.asIdeal`. Introduce `M`.

Proceed by induction on `M using Nat.strong_induction_on with`. Consider the case `_ M ih`. Introduce `hM hv`. Distinguish the cases in `h1 : M = 1`. Substitute `h1` using the available equality.

Rewrite `hv` using `[Nat.cast_one]`. Conclude with `(v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hv)).elim`. Take `⟨p, hp, m, rfl⟩` from `Nat.exists_prime_and_dvd h1`. Rewrite `hv` using `[Nat.cast_mul]`. Break down `v.isPrime.mem_or_mem hv with h | h` into its components or cases.

Conclude with `⟨p, Nat.mem_primeFactors.2 ⟨hp, dvd_mul_right p m, hM⟩, h⟩`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hM`. Establish `hlt : m < p * m`.

Use `hp.two_le` as an intermediate fact. Use `Nat.pos_of_ne_zero hm0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Take `⟨q, hq, hqv⟩` from `ih m hlt hm0 h`. Establish `hq'` using `Nat.mem_primeFactors.1 hq`.

Conclude with `⟨q, Nat.mem_primeFactors.2 ⟨hq'.1, hq'.2.1.mul_left p, hM⟩, hqv⟩`. Conclude with `key N hN`. Introduce and unpack `⟨p, hp, hpv⟩`. Take `⟨m, hm⟩` from `(Nat.mem_primeFactors.1 hp).2.1`. Rewrite using `[hm, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hpv`.
-/
private theorem plDvd_eq (F : Type) [Field F] (N : ℕ) (hN : N ≠ 0) :
    plDvd F N = ⋃ p ∈ N.primeFactors, plDvd F p := by
  ext v
  simp only [plDvd, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · have key : ∀ M : ℕ, M ≠ 0 → ((M : 𝓞 F) ∈ v.asIdeal) →
        ∃ p ∈ M.primeFactors, (p : 𝓞 F) ∈ v.asIdeal := by
      intro M
      induction M using Nat.strong_induction_on with
      | _ M ih =>
        intro hM hv
        by_cases h1 : M = 1
        · subst h1
          rw [Nat.cast_one] at hv
          exact (v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hv)).elim
        · obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
          rw [Nat.cast_mul] at hv
          rcases v.isPrime.mem_or_mem hv with h | h
          · exact ⟨p, Nat.mem_primeFactors.2 ⟨hp, dvd_mul_right p m, hM⟩, h⟩
          · have hm0 : m ≠ 0 := by
              rintro rfl
              simp at hM
            have hlt : m < p * m := by
              have := hp.two_le
              have := Nat.pos_of_ne_zero hm0
              nlinarith
            obtain ⟨q, hq, hqv⟩ := ih m hlt hm0 h
            have hq' := Nat.mem_primeFactors.1 hq
            exact ⟨q, Nat.mem_primeFactors.2 ⟨hq'.1, hq'.2.1.mul_left p, hM⟩, hqv⟩
    exact key N hN
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨m, hm⟩ := (Nat.mem_primeFactors.1 hp).2.1
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv

/- English proof (translation)
Introduce `Ω _ _ _ l _ U N hUn hUo hN`. Use `haveI := hUn`. Use `haveI : (cycU l U).Normal := by`. Unfold `cycU`. Use `infer_instance`.

Establish `hUi : U.index ≠ 0` using `by haveI := Subgroup.quotient_finite_of_isOpen U hUo`. Conclude with `Subgroup.index_ne_zero_of_finite`. Establish `hUle : ∀ {X : Type} (s : Finset ℕ) (f : ℕ → Set X), (⋃ p ∈ s, f p).ncard ≤ ∑ p ∈ s, (f p).ncard`. Introduce `X s f`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Introduce `a s ha ih`. Rewrite using `[Finset.set_biUnion_insert, Finset.sum_insert ha]`. Conclude with `(Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)`. Establish `hb : ∀ p : ℕ, ∃ n, p.Prime → OrbLe (cycU l U) p n`.

Introduce `p`. Distinguish the cases in `hA : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1`. Take `⟨A₀, hA₀⟩` from `hA`. Use `⟨(cycU l U ⊔ Dec A₀).index, fun hp => ?_⟩` and prove the remaining obligations. Establish `hK` using `index_cyclotomicKer_sup_decompositionGroup_ne_zero Ω l p A₀ hp hA₀`.

Establish `hs` using `supIndex (G ℚ Ω) (cycZ ℚ Ω l).ker U (Dec A₀) hUi hK`. Conclude with `orbIndex Ω p (cycU l U) A₀ hp hA₀ hs.1`. Conclude with `⟨0, fun _ => ⟨∅, by simp, by simp, fun A hA' => (hA ⟨A, hA'⟩).elim⟩⟩`. Use `choose nf hnf using hb`. Use `⟨∑ p ∈ N.primeFactors, nf p, fun F _ hF => ?_⟩` and prove the remaining obligations.

Rewrite using `[plDvd_eq F N hN]`. Use `(hUle _ _).trans (Finset.sum_le_sum fun p hp => ?_)` and prove the remaining obligations. Establish `hpp` using `(Nat.mem_primeFactors.1 hp).1`. Conclude with `ncard_placesDividing_le_of_orbitBound Ω F (cycU l U) p (nf p) hpp.ne_zero hF (hnf p hpp)`.
-/
theorem UpperTheory.V.Ws.exists_uniform_bound_ncard_placesDividing :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (N : ℕ), U.Normal → IsOpen (U : Set (G ℚ Ω)) → N ≠ 0 → ∃ g : ℕ, ∀ (F : IntermediateField ℚ Ω) [NumberField F], cycU l U ≤ F.fixingSubgroup → (plDvd F N).ncard ≤ g := by
  intro Ω _ _ _ l _ U N hUn hUo hN
  haveI := hUn
  haveI : (cycU l U).Normal := by
    unfold cycU
    infer_instance
  have hUi : U.index ≠ 0 := by
    haveI := Subgroup.quotient_finite_of_isOpen U hUo
    exact Subgroup.index_ne_zero_of_finite
  have hUle : ∀ {X : Type} (s : Finset ℕ) (f : ℕ → Set X),
      (⋃ p ∈ s, f p).ncard ≤ ∑ p ∈ s, (f p).ncard := by
    intro X s f
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
  have hb : ∀ p : ℕ, ∃ n, p.Prime → OrbLe (cycU l U) p n := by
    intro p
    by_cases hA : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
    · obtain ⟨A₀, hA₀⟩ := hA
      refine ⟨(cycU l U ⊔ Dec A₀).index, fun hp => ?_⟩
      have hK := index_cyclotomicKer_sup_decompositionGroup_ne_zero Ω l p A₀ hp hA₀
      have hs := supIndex (G ℚ Ω) (cycZ ℚ Ω l).ker U (Dec A₀) hUi hK
      exact orbIndex Ω p (cycU l U) A₀ hp hA₀ hs.1
    · exact ⟨0, fun _ => ⟨∅, by simp, by simp, fun A hA' => (hA ⟨A, hA'⟩).elim⟩⟩
  choose nf hnf using hb
  refine ⟨∑ p ∈ N.primeFactors, nf p, fun F _ hF => ?_⟩
  rw [plDvd_eq F N hN]
  refine (hUle _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hpp := (Nat.mem_primeFactors.1 hp).1
  exact ncard_placesDividing_le_of_orbitBound Ω F (cycU l U) p (nf p) hpp.ne_zero hF (hnf p hpp)
