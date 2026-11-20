import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCountPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

/- English proof (translation)
Establish `hJ : J ≤ RingHom.ker (eval x)` using `fun q hq => (RingHom.mem_ker).2 (hx q hq)`. Establish `: (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨P, hP, hPle⟩` from `Ideal.exists_minimalPrimes_le hJ`. Conclude with `⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩`.
-/
theorem exists_minimalPrime_mem_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by
  have hJ : J ≤ RingHom.ker (eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJ
  exact ⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩

/- English proof (translation)
Take `⟨-, hQ, V, hV, hiso⟩` from `hx`. Conclude with `⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩`.
-/
theorem mem_isolatedFibrePts_of_le {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by
  obtain ⟨-, hQ, V, hV, hiso⟩ := hx
  exact ⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.set_biUnion_insert]`. Conclude with `(Set.encard_union_le _ _).trans (add_le_add_right ih _)`.
-/
theorem encard_biUnion_finset_le {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add_right ih _)

/- English proof (translation)
Introduce `n m J Q`. Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J`. Establish `hN : ∀ P ∈ J.minimalPrimes, ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N` using `fun P hP => hPrime n m P hP.1.1 Q`. Use `choose! N hN using hN`. Use `⟨∑ P ∈ hfin.toFinset, N P, fun z => ?_⟩` and prove the remaining obligations.

Establish `hsub : isolatedFibrePts J Q z ⊆ ⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z`. Introduce `x hx`. Take `⟨P, hP, hxP⟩` from `exists_minimalPrime_mem_zeroSet J hx.1`. Conclude with `Set.mem_biUnion (hfin.mem_toFinset.2 hP) (mem_isolatedFibrePts_of_le hP.1.2 Q z hx hxP)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsolatedPointsCount.proof (hPrime : IsolatedPointsCountPrime.Statement) :
    IsolatedPointsCount.Statement := by
  classical
  intro n m J Q
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hN : ∀ P ∈ J.minimalPrimes, ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N :=
    fun P hP => hPrime n m P hP.1.1 Q
  choose! N hN using hN
  refine ⟨∑ P ∈ hfin.toFinset, N P, fun z => ?_⟩
  have hsub : isolatedFibrePts J Q z ⊆ ⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_minimalPrime_mem_zeroSet J hx.1
    exact Set.mem_biUnion (hfin.mem_toFinset.2 hP) (mem_isolatedFibrePts_of_le hP.1.2 Q z hx hxP)
  calc (isolatedFibrePts J Q z).encard
      ≤ (⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z).encard := Set.encard_le_encard hsub
    _ ≤ ∑ P ∈ hfin.toFinset, (isolatedFibrePts P Q z).encard := encard_biUnion_finset_le _ _
    _ ≤ ∑ P ∈ hfin.toFinset, ((N P : ℕ) : ℕ∞) :=
        Finset.sum_le_sum fun P hP => hN P (hfin.mem_toFinset.1 hP) z
    _ = ((∑ P ∈ hfin.toFinset, N P : ℕ) : ℕ∞) := by push_cast; rfl

end

end GroundTheory.Heights₂.Heights
