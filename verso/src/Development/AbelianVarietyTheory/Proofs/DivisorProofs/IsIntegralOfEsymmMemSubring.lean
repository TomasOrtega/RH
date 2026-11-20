import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open Polynomial

namespace GlobalTheory.QFam

/- English proof (translation)
Use `set Q : ℂ[X] := ∏ j, (X + C (x j)) with hQ`. Establish `hmon : Q.Monic` using `monic_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))`. Establish `hdeg : Q.natDegree = (Finset.univ : Finset ι).card`. Rewrite using `[hQ, natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))]`. Simplify using the standard rewrite rules.

Establish `hl : Q ∈ Polynomial.lifts (algebraMap R ℂ)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Distinguish the cases in `hn : n ≤ (Finset.univ : Finset ι).card`. Rewrite using `[hQ, Finset.prod_X_add_C_coeff _ _ hn]`.

Conclude with `⟨⟨_, h _⟩, rfl⟩`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega)]`. Conclude with `⟨0, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hmon`. Establish `hneg : IsIntegral R (-x i)`.

Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map, hq, hQ, eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Simplify using `using hneg.neg`.
-/
theorem isIntegral_of_esymm_mem (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ)
    (h : ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) (i : ι) :
    IsIntegral R (x i) := by
  classical
  set Q : ℂ[X] := ∏ j, (X + C (x j)) with hQ
  have hmon : Q.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))
  have hdeg : Q.natDegree = (Finset.univ : Finset ι).card := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))]
    simp
  have hl : Q ∈ Polynomial.lifts (algebraMap R ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ (Finset.univ : Finset ι).card
    · rw [hQ, Finset.prod_X_add_C_coeff _ _ hn]
      exact ⟨⟨_, h _⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
  have hneg : IsIntegral R (-x i) := by
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  simpa using hneg.neg

end GlobalTheory.QFam
