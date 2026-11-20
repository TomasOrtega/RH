import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliDefs

noncomputable section

namespace PI.HookSteps.Cap

open Finset

variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

/- English proof (translation)
Unfold `xw`. Rewrite using `[List.ofFn_succ, List.prod_cons]`.
-/
theorem xw_succ (x : I → S → 𝒰) {k : ℕ} (r : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    xw x r s = x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ) := by
  unfold xw
  rw [List.ofFn_succ, List.prod_cons]

/- English proof (translation)
Unfold `dw`. Rewrite using `[List.ofFn_succ, List.prod_cons]`.
-/
theorem dw_succ (d : I → S → 𝒰) {k : ℕ} (g : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    dw d g s = d (g 0) (s 0) * dw d (fun i => g i.succ) (fun i => s i.succ) := by
  unfold dw
  rw [List.ofFn_succ, List.prod_cons]

/- English proof (translation)
Unfold `xw`. Simplify using the standard rewrite rules.
-/
theorem xw_zero (x : I → S → 𝒰) (r : Fin 0 → I) (s : Fin 0 → S) : xw x r s = 1 := by
  unfold xw
  simp

/- English proof (translation)
Unfold `dw`. Simplify using the standard rewrite rules.
-/
theorem dw_zero (d : I → S → 𝒰) (g : Fin 0 → I) (s : Fin 0 → S) : dw d g s = 1 := by
  unfold dw
  simp

/- English proof (translation)
Rewrite using `[← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
theorem sum_fun_succ {M : Type} [AddCommMonoid M] {k : ℕ} (f : (Fin (k + 1) → S) → M) :
    ∑ s, f s = ∑ t : S, ∑ s : Fin k → S, f (Fin.cons t s) := by
  rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
  rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [xw_zero, mul_one, one_mul]`. Consider the case `succ k ih`. Rewrite using `[xw_succ, ← mul_assoc, hxx a t (r 0) (s 0), mul_assoc (x (r 0) (s 0)) (x a t), ih, ← mul_assoc]`.
-/
theorem x_comm_xw (x : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    {k : ℕ} (a : I) (t : S) (r : Fin k → I) (s : Fin k → S) :
    x a t * xw x r s = xw x r s * x a t := by
  induction k with
  | zero => rw [xw_zero, mul_one, one_mul]
  | succ k ih =>
    rw [xw_succ, ← mul_assoc, hxx a t (r 0) (s 0), mul_assoc (x (r 0) (s 0)) (x a t), ih,
      ← mul_assoc]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `r s a b t`. Simplify using `[xw_zero]`.

Consider the case `succ k ih`. Introduce `r s a b t`. Establish `h1 : xw x (Function.update r 0 a) s = x a (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ)`. Establish `hf : (fun i : Fin k => Function.update r 0 a i.succ) = fun i => r i.succ`. Use function extensionality and compare the values at `fun i => by rw [Function.update_apply, if_neg (Fin.succ_ne_zero i)]`.

Rewrite using `[xw_succ, hf, Function.update_apply, if_pos rfl]`. Establish `h2 : ∀ j : Fin k, xw x (Function.update r j.succ a) s = x (r 0) (s 0) * xw x (Function.update (fun i => r i.succ) j a) (fun i => s i.succ)`. Introduce `j`. Establish `hf : (fun i : Fin k => Function.update r j.succ a i.succ) = Function.update (fun i => r i.succ) j a` using `Function.update_comp_eq_of_injective r (Fin.succ_injective k) j a`. Rewrite using `[xw_succ, hf, Function.update_apply, if_neg (Fin.succ_ne_zero j).symm]`.

Establish `key : x a t * (x (r 0) (s 0) * (d b t * xw x (fun i => r i.succ) (fun i => s i.succ))) = x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) + ∑ j : Fin k, if r j.succ = b ∧ s j.succ = t then xw x (Function.update r j.succ a) s else 0`. Rewrite using `[← mul_assoc, hxx a t (r 0) (s 0), mul_assoc (x (r 0) (s 0)) (x a t), ih, mul_add, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h2 j, mul_ite, mul_zero]`.

Establish `c0 : x a t * ((if r 0 = b ∧ s 0 = t then (1 : 𝒰) else 0) * xw x (fun i => r i.succ) (fun i => s i.succ)) = if r 0 = b ∧ s 0 = t then xw x (Function.update r 0 a) s else 0` using `by split_ifs with h`. Rewrite using `[h1, h.2, one_mul]`. Rewrite using `[zero_mul, mul_zero]`. Establish `m : x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) = x a t * (x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ)) * d b t`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc, hxx (r 0) (s 0) a t, mul_assoc]`. Rewrite using `[xw_succ x r s, Fin.sum_univ_succ, ← c0, ← mul_assoc (d b t), hdx (r 0) (s 0) b t, add_mul, mul_add, mul_assoc (x (r 0) (s 0)) (d b t), key, m]`. Normalize the expressions using the abelian group laws.
-/
theorem dx_key (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) :
    ∀ (k : ℕ) (r : Fin k → I) (s : Fin k → S) (a b : I) (t : S),
      x a t * (d b t * xw x r s) = x a t * xw x r s * d b t +
        ∑ j, if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0 := by
  intro k
  induction k with
  | zero =>
    intro r s a b t
    simp [xw_zero]
  | succ k ih =>
    intro r s a b t
    have h1 : xw x (Function.update r 0 a) s =
        x a (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ) := by
      have hf : (fun i : Fin k => Function.update r 0 a i.succ) = fun i => r i.succ :=
        funext fun i => by rw [Function.update_apply, if_neg (Fin.succ_ne_zero i)]
      rw [xw_succ, hf, Function.update_apply, if_pos rfl]
    have h2 : ∀ j : Fin k, xw x (Function.update r j.succ a) s =
        x (r 0) (s 0) * xw x (Function.update (fun i => r i.succ) j a) (fun i => s i.succ) := by
      intro j
      have hf : (fun i : Fin k => Function.update r j.succ a i.succ) =
          Function.update (fun i => r i.succ) j a :=
        Function.update_comp_eq_of_injective r (Fin.succ_injective k) j a
      rw [xw_succ, hf, Function.update_apply, if_neg (Fin.succ_ne_zero j).symm]
    have key : x a t * (x (r 0) (s 0) * (d b t * xw x (fun i => r i.succ) (fun i => s i.succ))) =
        x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) +
        ∑ j : Fin k, if r j.succ = b ∧ s j.succ = t then
          xw x (Function.update r j.succ a) s else 0 := by
      rw [← mul_assoc, hxx a t (r 0) (s 0), mul_assoc (x (r 0) (s 0)) (x a t), ih, mul_add,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2 j, mul_ite, mul_zero]
    have c0 : x a t * ((if r 0 = b ∧ s 0 = t then (1 : 𝒰) else 0) *
        xw x (fun i => r i.succ) (fun i => s i.succ)) =
        if r 0 = b ∧ s 0 = t then xw x (Function.update r 0 a) s else 0 := by
      split_ifs with h
      · rw [h1, h.2, one_mul]
      · rw [zero_mul, mul_zero]
    have m : x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) =
        x a t * (x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ)) * d b t := by
      simp only [mul_assoc]
      rw [← mul_assoc, hxx (r 0) (s 0) a t, mul_assoc]
    rw [xw_succ x r s, Fin.sum_univ_succ, ← c0, ← mul_assoc (d b t), hdx (r 0) (s 0) b t,
      add_mul, mul_add, mul_assoc (x (r 0) (s 0)) (d b t), key, m]
    abel

/- English proof (translation)
Establish `first : Pn x d (Fin.cons a r) (Fin.cons b g) = ∑ t, ∑ s : Fin k → S, x a t * xw x r s * (d b t * dw d g s)`. Unfold `Pn`. Rewrite using `[sum_fun_succ]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[xw_succ, dw_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ, mul_assoc]`. Establish `second : ∀ j : Fin k, (if r j = b then Pn x d (Function.update r j a) g else 0) = ∑ t, ∑ s : Fin k → S, (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s`. Introduce `j`. Rewrite using `[Finset.sum_comm]`. Unfold `Pn`.

Use `split_ifs with h`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `[h]`. Simplify using `[h]`. Establish `term : ∀ (t : S) (s : Fin k → S), x a t * d b t * (xw x r s * dw d g s) = x a t * xw x r s * (d b t * dw d g s) + ∑ j, (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s`.

Introduce `t s`. Rewrite using `[mul_assoc (x a t), ← mul_assoc (d b t), ← mul_assoc (x a t), dx_key x d hxx hdx k r s a b t, add_mul, Finset.sum_mul, mul_assoc (x a t * xw x r s)]`. Rewrite using `[first]`. Repeatedly rewrite using `[second]`. Unfold `Eop Pn`.

Rewrite using `[Finset.sum_mul]`. Repeatedly rewrite using `[Finset.mul_sum, term, Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `(Finset.sum_congr rfl fun t _ => Finset.sum_comm).trans Finset.sum_comm`.
-/
theorem E_Pn (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (r g : Fin k → I) (a b : I) :
    Eop x d a b * Pn x d r g = Pn x d (Fin.cons a r) (Fin.cons b g) +
      ∑ j, if r j = b then Pn x d (Function.update r j a) g else 0 := by
  have first : Pn x d (Fin.cons a r) (Fin.cons b g) =
      ∑ t, ∑ s : Fin k → S, x a t * xw x r s * (d b t * dw d g s) := by
    unfold Pn
    rw [sum_fun_succ]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    rw [xw_succ, dw_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_assoc]
  have second : ∀ j : Fin k, (if r j = b then Pn x d (Function.update r j a) g else 0) =
      ∑ t, ∑ s : Fin k → S,
        (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s := by
    intro j
    rw [Finset.sum_comm]
    unfold Pn
    split_ifs with h
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp [h]
    · simp [h]
  have term : ∀ (t : S) (s : Fin k → S), x a t * d b t * (xw x r s * dw d g s) =
      x a t * xw x r s * (d b t * dw d g s) +
      ∑ j, (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s := by
    intro t s
    rw [mul_assoc (x a t), ← mul_assoc (d b t), ← mul_assoc (x a t), dx_key x d hxx hdx k r s a b t,
      add_mul, Finset.sum_mul, mul_assoc (x a t * xw x r s)]
  rw [first]
  simp_rw [second]
  unfold Eop Pn
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, term, Finset.sum_add_distrib]
  congr 1
  exact (Finset.sum_congr rfl fun t _ => Finset.sum_comm).trans Finset.sum_comm

end PI.HookSteps.Cap
