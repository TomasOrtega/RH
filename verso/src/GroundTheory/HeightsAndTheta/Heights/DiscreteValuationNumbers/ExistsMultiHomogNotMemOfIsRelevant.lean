import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Avoid

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Use `choose i hi using hrel`. Use `⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩` and prove the remaining obligations. Establish `hprod` using `IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k) (fun k => c k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)`. Establish `hc : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c`. Use function extensionality and compare the values at `k'`.

Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Rewrite `hprod` using `[hc]`. Conclude with `hprod`. Introduce `hm`. Take `⟨k, -, hk⟩` from `hH.prod_mem_iff.mp hm`.

Conclude with `hi k (hH.mem_of_pow_mem _ hk)`.
-/
theorem exists_multiHomog_not_mem_of_isRelevant {H : Ideal (MRing ι R)} (hH : H.IsPrime)
    (hrel : IsRelevant H) (c : K → ℕ) : ∃ m : MRing ι R, IsMultiHomog m c ∧ m ∉ H := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k) (fun k => c k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
    have hc : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hc] at hprod
    exact hprod
  · intro hm
    obtain ⟨k, -, hk⟩ := hH.prod_mem_iff.mp hm
    exact hi k (hH.mem_of_pow_mem _ hk)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨0, isWeightedHomogeneous_zero _ _ _, by simp⟩`. Consider the case `@insert Q₀ S _ ih`. Take `⟨x, hx, hxS⟩` from `ih fun Q h => hS Q (Finset.mem_insert_of_mem h)`. Take `⟨hQ₀, hrel₀, hC₀⟩` from `hS Q₀ (Finset.mem_insert_self _ _)`.

Take `⟨y, hy, hyQ₀⟩` from `exists_multiHomog_not_mem_of_isRelevant hQ₀ hrel₀ c`. Establish `hsub : ∀ Q ∈ S, {t : R | x + C t * y ∈ Q}.Subsingleton`. Introduce `Q hQS t ht t' ht'`. Take `⟨hQ, -, hCQ⟩` from `hS Q (Finset.mem_insert_of_mem hQS)`. Establish `hd : C (t - t') * y ∈ Q`.

Establish `h` using `Q.sub_mem ht ht'`. Rewrite using `[map_sub]`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Break down `hQ.mem_or_mem hd with h | h` into its components or cases.

Conclude with `sub_eq_zero.mp (hCQ _ h)`. Conclude with `absurd (by simpa using Q.sub_mem ht (Q.mul_mem_left (C t) h)) (hxS Q hQS)`. Establish `hfin : (insert 0 (⋃ Q ∈ S, {t : R | x + C t * y ∈ Q})).Finite` using `(S.finite_toSet.biUnion fun Q hQ => (hsub Q hQ).finite).insert 0`. Take `⟨t, ht⟩` from `Infinite.exists_notMem_finset hfin.toFinset`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at ht`.

Take `⟨ht0, htS⟩` from `ht`. Distinguish the cases in `hxQ₀ : x ∈ Q₀`. Use `⟨x + C t * y, hx.add (by simpa using (isWeightedHomogeneous_C _ t).mul hy), ?_⟩` and prove the remaining obligations. Introduce `Q hQ`. Break down `Finset.mem_insert.mp hQ with rfl | hQS` into its components or cases.

Introduce `h`. Establish `h' : C t * y ∈ Q` using `by simpa using Q.sub_mem h hxQ₀`. Break down `hQ₀.mem_or_mem h' with h'' | h''` into its components or cases. Conclude with `ht0 (hC₀ _ h'')`. Conclude with `hyQ₀ h''`.

Conclude with `htS Q hQS`. Use `⟨x, hx, fun Q hQ => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hQ with rfl | hQS` into its components or cases. Conclude with `hxQ₀`. Conclude with `hxS Q hQS`.
-/
theorem exists_multiHomog_not_mem_finset [Infinite R] (c : K → ℕ) (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ Q ∈ S, Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : R, C a ∈ Q → a = 0) :
    ∃ m : MRing ι R, IsMultiHomog m c ∧ ∀ Q ∈ S, m ∉ Q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, isWeightedHomogeneous_zero _ _ _, by simp⟩
  | @insert Q₀ S _ ih =>
    obtain ⟨x, hx, hxS⟩ := ih fun Q h => hS Q (Finset.mem_insert_of_mem h)
    obtain ⟨hQ₀, hrel₀, hC₀⟩ := hS Q₀ (Finset.mem_insert_self _ _)
    obtain ⟨y, hy, hyQ₀⟩ := exists_multiHomog_not_mem_of_isRelevant hQ₀ hrel₀ c

    have hsub : ∀ Q ∈ S, {t : R | x + C t * y ∈ Q}.Subsingleton := by
      intro Q hQS t ht t' ht'
      obtain ⟨hQ, -, hCQ⟩ := hS Q (Finset.mem_insert_of_mem hQS)
      have hd : C (t - t') * y ∈ Q := by
        have h := Q.sub_mem ht ht'
        rw [map_sub]
        convert h using 1
        ring
      rcases hQ.mem_or_mem hd with h | h
      · exact sub_eq_zero.mp (hCQ _ h)
      · exact absurd (by simpa using Q.sub_mem ht (Q.mul_mem_left (C t) h)) (hxS Q hQS)
    have hfin : (insert 0 (⋃ Q ∈ S, {t : R | x + C t * y ∈ Q})).Finite :=
      (S.finite_toSet.biUnion fun Q hQ => (hsub Q hQ).finite).insert 0
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset hfin.toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      not_or, not_exists] at ht
    obtain ⟨ht0, htS⟩ := ht
    by_cases hxQ₀ : x ∈ Q₀
    · refine ⟨x + C t * y, hx.add (by simpa using (isWeightedHomogeneous_C _ t).mul hy), ?_⟩
      intro Q hQ
      rcases Finset.mem_insert.mp hQ with rfl | hQS
      · intro h
        have h' : C t * y ∈ Q := by simpa using Q.sub_mem h hxQ₀
        rcases hQ₀.mem_or_mem h' with h'' | h''
        · exact ht0 (hC₀ _ h'')
        · exact hyQ₀ h''
      · exact htS Q hQS
    · refine ⟨x, hx, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQS
      · exact hxQ₀
      · exact hxS Q hQS

end Avoid

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP s hs e`. Establish `: Infinite O` using `Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)`. Establish `hfin : (Function.support (divCycle P s)).Finite`. Apply `Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s}))` to reduce the goal to its premises. Introduce `W hW`.

Assume the negation of the conclusion as `hmin`. Apply `hW` to reduce the goal to its premises. Unfold `divCycle`. Rewrite using `[dif_neg]`. Conclude with `fun h => hmin h.1`.

Establish `hT : ∀ Q ∈ insert P (hfin.toFinset.filter fun H => (C ϖ : MRing ι O) ∉ H), Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : O, C a ∈ Q → a = 0`. Introduce `Q hQ`. Break down `Finset.mem_insert.mp hQ with rfl | hQ` into its components or cases. Use `⟨hP.multiProj.isPrime, hP.multiProj.relevant, fun a ha => ?_⟩` and prove the remaining obligations. Establish `h : a ∈ Q.comap (C : O →+* MRing ι O)` using `ha`.

Rewrite `h` using `[hP.noTorsion]`. Conclude with `(Submodule.mem_bot O).mp h`. Take `⟨hQs, hϖQ⟩` from `Finset.mem_filter.mp hQ`. Take `⟨hQp, -, hrel⟩` from `le_and_isRelevant_of_divCycle_ne_zero (Function.mem_support.mp (hfin.mem_toFinset.mp hQs))`. Use `⟨hQp, hrel, fun a ha => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `ha0`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ`. Rewrite `ha` using `[map_mul, map_pow]`. Break down `hQp.mem_or_mem ha with h | h` into its components or cases. Conclude with `hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))`.

Conclude with `hϖQ (hQp.mem_of_pow_mem _ h)`. Take `⟨m, hm, hmT⟩` from `exists_multiHomog_not_mem_finset e _ hT`. Use `⟨m, hm, hmT P (Finset.mem_insert_self _ _), fun H hH hϖH => hmT H ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr (Function.mem_support.mpr hH), hϖH⟩)`.
-/
theorem HorizontalAvoidingForm.proof : HorizontalAvoidingForm.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP s hs e
  classical
  have : Infinite O :=
    Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)

  have hfin : (Function.support (divCycle P s)).Finite := by
    apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s}))
    intro W hW
    by_contra hmin
    apply hW
    unfold divCycle
    rw [dif_neg]
    exact fun h => hmin h.1

  have hT : ∀ Q ∈ insert P (hfin.toFinset.filter fun H => (C ϖ : MRing ι O) ∉ H),
      Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : O, C a ∈ Q → a = 0 := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · refine ⟨hP.multiProj.isPrime, hP.multiProj.relevant, fun a ha => ?_⟩
      have h : a ∈ Q.comap (C : O →+* MRing ι O) := ha
      rw [hP.noTorsion] at h
      exact (Submodule.mem_bot O).mp h
    · obtain ⟨hQs, hϖQ⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hQp, -, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero
        (Function.mem_support.mp (hfin.mem_toFinset.mp hQs))
      refine ⟨hQp, hrel, fun a ha => ?_⟩
      by_contra ha0
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
      rw [map_mul, map_pow] at ha
      rcases hQp.mem_or_mem ha with h | h
      · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))
      · exact hϖQ (hQp.mem_of_pow_mem _ h)
  obtain ⟨m, hm, hmT⟩ := exists_multiHomog_not_mem_finset e _ hT
  refine ⟨m, hm, hmT P (Finset.mem_insert_self _ _), fun H hH hϖH => hmT H ?_⟩
  exact Finset.mem_insert_of_mem
    (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr (Function.mem_support.mpr hH), hϖH⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
