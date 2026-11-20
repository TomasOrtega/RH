import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SubSlice

open Function

namespace PositivityTheory.KB.StokesSlices

section Alt

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

A detailed English derivation is pending.
-/
lemma alternatingMap_sub_on_finset_eq_sub_sum_update {q : ℕ} (f : V [⋀^Fin q]→ₗ[ℝ] ℝ) (x : V) (S : Finset (Fin q)) :
    ∀ u : Fin q → V, f (fun j => if j ∈ S then u j - x else u j) =
      f u - ∑ j ∈ S, f (update u j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro u; simp
  | insert a S ha ih =>
    intro u
    have hfun : (fun j => if j ∈ insert a S then u j - x else u j) =
        (fun j => if j ∈ S then update u a (u a - x) j - x else update u a (u a - x) j) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj, Function.update_of_ne hj]
    rw [hfun, ih]
    have h1 : f (update u a (u a - x)) = f u - f (update u a x) := by
      rw [f.map_update_sub, update_eq_self]
    have h2 : ∀ j ∈ S, f (update (update u a (u a - x)) j x) = f (update u j x) := by
      intro j hj
      have haj : a ≠ j := fun h => ha (h ▸ hj)
      rw [Function.update_comm haj, f.map_update_sub]
      have e1 : update (update u j x) a (u a) = update u j x := by
        conv_lhs => rw [show u a = update u j x a from (Function.update_of_ne haj _ _).symm]
        exact update_eq_self _ _
      have e2 : f (update (update u j x) a x) = 0 := by
        apply f.map_eq_zero_of_eq _ (i := a) (j := j) _ haj
        simp [Function.update_of_ne haj.symm, haj]
      rw [e1, e2, sub_zero]
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_insert ha]
    abel

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
lemma cons_removeNth_tail {q : ℕ} (v : Fin (q + 2) → V) (j : Fin (q + 1)) :
    Matrix.vecCons (v 0) (j.removeNth (Fin.tail v)) = j.succ.removeNth v := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.tail, Fin.succ_succAbove_succ]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
lemma alternatingMap_sub_base_eq_alternating_sum_removeNth (q : ℕ) (f : V [⋀^Fin q]→ₗ[ℝ] ℝ) (v : Fin (q + 1) → V) :
    f (fun j => v j.succ - v 0) = ∑ i : Fin (q + 1), (-1 : ℝ) ^ (i : ℕ) * f (i.removeNth v) := by
  classical
  have h := alternatingMap_sub_on_finset_eq_sub_sum_update f (v 0) Finset.univ (fun j => v j.succ)
  simp only [Finset.mem_univ, if_true] at h
  have hj : ∀ j : Fin q, f (update (fun j => v j.succ) j (v 0)) =
      (-1 : ℝ) ^ (j : ℕ) * f (j.succ.removeNth v) := by
    cases q with
    | zero => intro j; exact j.elim0
    | succ m =>
      intro j
      have hc := cons_removeNth_tail v j
      rw [← Fin.insertNth_removeNth, f.map_insertNth]
      erw [hc]
      simp [Units.smul_def, zsmul_eq_mul]
  have e0 : Fin.removeNth 0 v = fun j => v j.succ := by
    funext j
    simp [Fin.removeNth]
  rw [h, Fin.sum_univ_succ, Finset.sum_congr rfl (fun j _ => hj j), e0, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Alt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem subAlt : StokesSimplexSubdivision := by
  intro V _ _ q f v
  exact alternatingMap_sub_base_eq_alternating_sum_removeNth q f.toAlternatingMap v

end PositivityTheory.KB.StokesSlices
