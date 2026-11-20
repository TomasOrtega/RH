import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SubSlice

open Function

namespace PositivityTheory.KB.StokesSlices

section Alt

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => intro u`. Simplify using the standard rewrite rules. Consider the case `insert a S ha ih`. Introduce `u`.

Establish `hfun : (fun j => if j ∈ insert a S then u j - x else u j) = (fun j => if j ∈ S then update u a (u a - x) j - x else update u a (u a - x) j)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality. Simplify using `[ha]`.

Simplify using `[hj, Function.update_of_ne hj]`. Rewrite using `[hfun, ih]`. Establish `h1 : f (update u a (u a - x)) = f u - f (update u a x)`. Rewrite using `[f.map_update_sub, update_eq_self]`. Establish `h2 : ∀ j ∈ S, f (update (update u a (u a - x)) j x) = f (update u j x)`.

Introduce `j hj`. Establish `haj : a ≠ j` using `fun h => ha (h ▸ hj)`. Rewrite using `[Function.update_comm haj, f.map_update_sub]`. Establish `e1 : update (update u j x) a (u a) = update u j x` using `by conv_lhs => rw [show u a = update u j x a from (Function.update_of_ne haj _ _).symm]`. Conclude with `update_eq_self _ _`.

Establish `e2 : f (update (update u j x) a x) = 0`. Apply `f.map_eq_zero_of_eq _ (i := a) (j := j) _ haj` to reduce the goal to its premises. Simplify using `[Function.update_of_ne haj.symm, haj]`. Rewrite using `[e1, e2, sub_zero]`. Rewrite using `[h1, Finset.sum_congr rfl h2, Finset.sum_insert ha]`.

Normalize the expressions using the abelian group laws.
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
Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations. Simplify using `[Fin.removeNth]`. Simplify using `[Fin.removeNth, Fin.tail, Fin.succ_succAbove_succ]`.
-/
lemma cons_removeNth_tail {q : ℕ} (v : Fin (q + 2) → V) (j : Fin (q + 1)) :
    Matrix.vecCons (v 0) (j.removeNth (Fin.tail v)) = j.succ.removeNth v := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.tail, Fin.succ_succAbove_succ]

/- English proof (translation)
Establish `h` using `alternatingMap_sub_on_finset_eq_sub_sum_update f (v 0) Finset.univ (fun j => v j.succ)`. Simplify using `only [Finset.mem_univ, if_true] at h`. Establish `hj : ∀ j : Fin q, f (update (fun j => v j.succ) j (v 0)) = (-1 : ℝ) ^ (j : ℕ) * f (j.succ.removeNth v)`. Consider the cases of `q with`. Consider the case `zero => intro j`.

Conclude with `j.elim0`. Consider the case `succ m`. Introduce `j`. Establish `hc` using `cons_removeNth_tail v j`. Rewrite using `[← Fin.insertNth_removeNth, f.map_insertNth]`.

Use `erw [hc]`. Simplify using `[Units.smul_def, zsmul_eq_mul]`. Establish `e0 : Fin.removeNth 0 v = fun j => v j.succ`. Use function extensionality and compare the values at `j`. Simplify using `[Fin.removeNth]`.

Rewrite using `[h, Fin.sum_univ_succ, Finset.sum_congr rfl (fun j _ => hj j), e0, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Simplify using `only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `V _ _ q f v`. Conclude with `alternatingMap_sub_base_eq_alternating_sum_removeNth q f.toAlternatingMap v`.
-/
theorem subAlt : StokesSimplexSubdivision := by
  intro V _ _ q f v
  exact alternatingMap_sub_base_eq_alternating_sum_removeNth q f.toAlternatingMap v

end PositivityTheory.KB.StokesSlices
