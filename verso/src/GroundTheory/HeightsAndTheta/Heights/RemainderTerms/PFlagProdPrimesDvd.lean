import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

/- English proof (translation)
Introduce `R _ _ ι s p x`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _ _ _`. Simplify using the standard rewrite rules. Consider the case `@insert t s ht ih`.

Introduce `hp hne hdvd`. Establish `hs : (∏ i ∈ s, p i) ∣ x` using `ih (fun i hi => hp i (mem_insert_of_mem hi)) (fun i hi j hj hij => hne i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij) (fun i hi => hdvd i (mem_insert_of_mem hi))`. Take `⟨y, hy⟩` from `hs`. Establish `hpt : Prime (p t)` using `hp t (mem_insert_self t s)`. Establish `hnd : ¬ p t ∣ ∏ i ∈ s, p i`.

Rewrite using `[Prime.dvd_finsetProd_iff hpt]`. Introduce and unpack `⟨j, hj, hdj⟩`. Use `hne t (mem_insert_self t s) j (mem_insert_of_mem hj) ?_ hdj` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `ht hj`.

Establish `hty : p t ∣ y`. Establish `h` using `hdvd t (mem_insert_self t s)`. Rewrite `h` using `[hy]`. Conclude with `(hpt.dvd_or_dvd h).resolve_left hnd`. Rewrite using `[prod_insert ht, hy, mul_comm (p t)]`.

Conclude with `mul_dvd_mul_left _ hty`.
-/
theorem FlagProdPrimesDvd.proof : FlagProdPrimesDvd.Statement := by
  intro R _ _ ι s p x
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert t s ht ih =>
    intro hp hne hdvd
    have hs : (∏ i ∈ s, p i) ∣ x :=
      ih (fun i hi => hp i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hne i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (mem_insert_of_mem hi))
    obtain ⟨y, hy⟩ := hs
    have hpt : Prime (p t) := hp t (mem_insert_self t s)
    have hnd : ¬ p t ∣ ∏ i ∈ s, p i := by
      rw [Prime.dvd_finsetProd_iff hpt]
      rintro ⟨j, hj, hdj⟩
      refine hne t (mem_insert_self t s) j (mem_insert_of_mem hj) ?_ hdj
      rintro rfl
      exact ht hj
    have hty : p t ∣ y := by
      have h := hdvd t (mem_insert_self t s)
      rw [hy] at h
      exact (hpt.dvd_or_dvd h).resolve_left hnd
    rw [prod_insert ht, hy, mul_comm (p t)]
    exact mul_dvd_mul_left _ hty

end RestTerms

end GroundTheory.Heights₂.Heights
