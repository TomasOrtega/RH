import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

/- English proof (translation)
The claim follows from `| [], _, hx => absurd hx (List.not_mem_nil) | a :: l, hc, hx => by rcases List.mem_cons.1 hx with h | h · subst h refine ⟨l.prod, ?_⟩ rw [List.prod_cons] exact (Commute.list_prod_left _ _ fun y hy => hc y (List.mem_cons_of_mem _ hy)).eq.symm · obtain ⟨r, hr⟩ := list_prod_eq_mul_o …`.
-/
theorem list_prod_eq_mul_of_mem {M : Type} [Monoid M] (x : M) :
    ∀ l : List M, (∀ y ∈ l, Commute y x) → x ∈ l → ∃ r : M, l.prod = r * x
  | [], _, hx => absurd hx (List.not_mem_nil)
  | a :: l, hc, hx => by
    rcases List.mem_cons.1 hx with h | h
    · subst h
      refine ⟨l.prod, ?_⟩
      rw [List.prod_cons]
      exact (Commute.list_prod_left _ _ fun y hy => hc y (List.mem_cons_of_mem _ hy)).eq.symm
    · obtain ⟨r, hr⟩ := list_prod_eq_mul_of_mem x l (fun y hy => hc y (List.mem_cons_of_mem _ hy)) h
      exact ⟨a * r, by rw [List.prod_cons, hr, mul_assoc]⟩

/- English proof (translation)
Introduce `H _ _ N0 N1 nu I m κ2 n t ht`. Establish `hzero : lapAll N0 N1 n (Gxz N0 N1 nu I) = 0`. Take `⟨r, hr⟩` from `list_prod_eq_mul_of_mem (lapT (H := H) N0 N1 t ^ n t) ((Finset.univ : Finset H).toList.map fun t => lapT N0 N1 t ^ n t) (fun y hy => by`. Take `⟨t', _, rfl⟩` from `List.mem_map.1 hy`. Conclude with `(hC H N0 N1 t' t).pow_pow _ _)`.

Use the proof step `(List.mem_map.2 ⟨t, Finset.mem_toList.2 (Finset.mem_univ t), rfl⟩)`. Unfold `lapAll`. Rewrite using `[hr, Module.End.mul_apply, hZ H N0 N1 nu I t (n t) ht, map_zero]`. Establish `h` using `hB H N0 N1 (Gxz N0 N1 nu I) m κ2 n`. Rewrite `h` using `[hzero, MvPolynomial.coeff_zero]`.

Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd h (Finset.prod_ne_zero_iff.2 fun t' _ => by exact_mod_cast (Nat.factorial_ne_zero (n t')))`. Conclude with `h`.
-/
theorem vanish_of (hB : PBridge) (hC : PLapComm) (hZ : PLapZero) : PVanish := by
  intro H _ _ N0 N1 nu I m κ2 n t ht
  have hzero : lapAll N0 N1 n (Gxz N0 N1 nu I) = 0 := by
    obtain ⟨r, hr⟩ := list_prod_eq_mul_of_mem (lapT (H := H) N0 N1 t ^ n t)
      ((Finset.univ : Finset H).toList.map fun t => lapT N0 N1 t ^ n t)
      (fun y hy => by
        obtain ⟨t', _, rfl⟩ := List.mem_map.1 hy
        exact (hC H N0 N1 t' t).pow_pow _ _)
      (List.mem_map.2 ⟨t, Finset.mem_toList.2 (Finset.mem_univ t), rfl⟩)
    unfold lapAll
    rw [hr, Module.End.mul_apply, hZ H N0 N1 nu I t (n t) ht, map_zero]
  have h := hB H N0 N1 (Gxz N0 N1 nu I) m κ2 n
  rw [hzero, MvPolynomial.coeff_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (Finset.prod_ne_zero_iff.2 fun t' _ => by exact_mod_cast (Nat.factorial_ne_zero (n t')))
  · exact h

end PI.EntAtD.W
