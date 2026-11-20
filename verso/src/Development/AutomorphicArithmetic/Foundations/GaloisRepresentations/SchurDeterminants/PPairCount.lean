import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `hP n i`. Establish `hS : ∑ a : Fin n, (n - 1 - (a : ℕ)) = n.choose 2`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun a => n - 1 - a), Finset.sum_range_reflect (fun a => a) n, Finset.sum_range_id, Nat.choose_two_right]`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by have := i.pos; omega⟩`. Establish `hC : (m + 1).choose 2 = m.choose 2 + m`.

Rewrite using `[Nat.choose_succ_succ, Nat.choose_one_right]`. Expand and normalize the polynomial expressions, which then agree. Establish `hi : (i : ℕ) ≤ m` using `by have := i.isLt; omega`. Simplify using `only [Nat.add_sub_cancel] at hS ⊢`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun k => m - (k : ℕ)) (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers. Establish `h` using `hP (Multiplicative ℕ) (m + 1) (fun _ _ => Multiplicative.ofAdd 1) i apply_fun Multiplicative.toAdd at h`. Simplify using `[toAdd_prod] at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.Schur.pairCount_of :
    PairSplit → PairCount := by
  intro hP n i
  have hS : ∑ a : Fin n, (n - 1 - (a : ℕ)) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun a => n - 1 - a), Finset.sum_range_reflect (fun a => a) n,
      Finset.sum_range_id, Nat.choose_two_right]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hC : (m + 1).choose 2 = m.choose 2 + m := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hi : (i : ℕ) ≤ m := by have := i.isLt; omega
  simp only [Nat.add_sub_cancel] at hS ⊢
  refine ⟨?_, ?_⟩
  · have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun k => m - (k : ℕ))
      (Finset.mem_univ i)
    omega
  · have h := hP (Multiplicative ℕ) (m + 1) (fun _ _ => Multiplicative.ofAdd 1) i
    apply_fun Multiplicative.toAdd at h
    simp [toAdd_prod] at h
    omega
