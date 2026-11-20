import Formalism.RealPlaceAnalysis.StatementE

open Finset

noncomputable section

namespace Formalism.REAL

/- English proof (translation)
Unfold `Tm`. Apply the tactic sequence `split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]`.
-/
theorem shiftedGenerator_eq_smul_add {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (r : ℂ)
    (p q : Fin n) : Tm E r p q = (if p = q then r else 0) • (1 : A) + E p q := by
  unfold Tm
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Introduce `A _ _ n E hE x y a b c d`. Establish `h' : E a b * E c d = E c d * E a b + ((if c = b then E a d else 0) - (if a = d then E c b else 0))`. Establish `h0` using `hE a b c d`. Simplify using `only [@eq_comm _ b c, @eq_comm _ d a] at h0`. Rewrite using `[← h0]`.

Normalize the expressions using the abelian group laws. Simplify using `only [shiftedGenerator_eq_smul_add, Algebra.algebraMap_eq_smul_one]`. Simplify using `only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, smul_add, smul_sub]`. Rewrite using `[h']`. Apply the tactic sequence `split_ifs <;> module`.
-/
theorem rttRelation : RTT := by
  intro A _ _ n E hE x y a b c d
  have h' : E a b * E c d = E c d * E a b + ((if c = b then E a d else 0) - (if a = d then E c b else 0)) := by
    have h0 := hE a b c d
    simp only [@eq_comm _ b c, @eq_comm _ d a] at h0
    rw [← h0]
    abel
  simp only [shiftedGenerator_eq_smul_add, Algebra.algebraMap_eq_smul_one]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
    smul_add, smul_sub]
  rw [h']
  split_ifs <;> module

/- English proof (translation)
Introduce `A _ _ n t E a b τ u`. Unfold `qminor`. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft]`.

Establish `hs : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign (τ * σ) : ℤ) : A) = ((Equiv.Perm.sign σ : ℤ) : A)`. Rewrite using `[← Int.cast_mul, Equiv.Perm.sign_mul, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]`. Rewrite using `[← mul_assoc, hs]`. Both sides reduce to the same expression.
-/
theorem quantumMinorRowSkew_holds : QSkewRow := by
  intro A _ _ n t E a b τ u
  unfold qminor
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulLeft]
  have hs : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign (τ * σ) : ℤ) : A) =
      ((Equiv.Perm.sign σ : ℤ) : A) := by
    rw [← Int.cast_mul, Equiv.Perm.sign_mul, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [← mul_assoc, hs]
  rfl

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro F c v _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Introduce `F c v h`. Rewrite using `[List.ofFn_succ, List.prod_cons, Module.End.mul_apply, ih (fun i => F i.succ) (fun i => c i.succ) v (fun i => h i.succ), map_smul, h 0, smul_smul, Fin.prod_univ_succ, mul_comm (c 0)]`.
-/
theorem prod_ofFn_apply_of_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V),
      (∀ k, F k v = c k • v) → (List.ofFn F).prod v = (∏ k, c k) • v := by
  intro m
  induction m with
  | zero => intro F c v _; simp
  | succ m ih =>
    intro F c v h
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ih (fun i => F i.succ) (fun i => c i.succ) v (fun i => h i.succ), map_smul, h 0, smul_smul,
      Fin.prod_univ_succ, mul_comm (c 0)]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro F c v j`. Conclude with `j.elim0`. Consider the case `succ m ih`.

Introduce `F c v j hj hk`. Rewrite using `[List.ofFn_succ, List.prod_cons, Module.End.mul_apply]`. Consider the cases of `j using Fin.cases with`. Consider the case `zero`. Rewrite using `[prod_ofFn_apply_of_eigen m (fun i => F i.succ) (fun i => c i.succ) v (fun i => hk i.succ (Fin.succ_pos i)), map_smul, hj, smul_zero]`.

Consider the case `succ j'`. Rewrite using `[ih (fun i => F i.succ) (fun i => c i.succ) v j' hj (fun i hi => hk i.succ (Fin.succ_lt_succ_iff.mpr hi)), map_zero]`.
-/
theorem prod_ofFn_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V) (j : Fin m),
      F j v = 0 → (∀ k, j < k → F k v = c k • v) → (List.ofFn F).prod v = 0 := by
  intro m
  induction m with
  | zero => intro F c v j; exact j.elim0
  | succ m ih =>
    intro F c v j hj hk
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    cases j using Fin.cases with
    | zero =>
      rw [prod_ofFn_apply_of_eigen m (fun i => F i.succ) (fun i => c i.succ) v (fun i => hk i.succ (Fin.succ_pos i)),
        map_smul, hj, smul_zero]
    | succ j' =>
      rw [ih (fun i => F i.succ) (fun i => c i.succ) v j' hj
        (fun i hi => hk i.succ (Fin.succ_lt_succ_iff.mpr hi)), map_zero]

/- English proof (translation)
Introduce `V _ _ n E ν v hE hv u`. Take `⟨hdiag, hup⟩` from `hv`. Establish `hdiag' : ∀ k : Fin n, Tm E (u - (k : ℂ)) k k v = (u - (k : ℂ) + ν k) • v`. Introduce `k`. Rewrite using `[Tm, if_pos rfl, LinearMap.add_apply, Module.algebraMap_end_apply, hdiag k, add_smul]`.

Establish `hoff : ∀ j k : Fin n, j < k → Tm E (u - (k : ℂ)) j k v = 0`. Introduce `j k hjk`. Simplify using `[Tm, ne_of_lt hjk, hup j k hjk]`. Unfold `qdet qminor`. Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`.

Simplify using `only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, id_eq, Equiv.Perm.one_apply]`. Conclude with `prod_ofFn_apply_of_eigen n _ _ v hdiag'`. Introduce `σ _ hσ`. Establish `hne : (Finset.univ.filter fun k => σ k ≠ k).Nonempty`. Assume the negation of the conclusion as `hc`.

Apply `hσ` to reduce the goal to its premises. Use `Equiv.ext fun k => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hk`. Conclude with `hc ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩`. Use `set j := (Finset.univ.filter fun k => σ k ≠ k).max' hne with hj`.

Establish `hjmove : σ j ≠ j` using `(Finset.mem_filter.mp (Finset.max'_mem _ hne)).2`. Establish `hfix : ∀ k, j < k → σ k = k`. Introduce `k hk`. Assume the negation of the conclusion as `h`. Use `Finset.le_max' (Finset.univ.filter fun k => σ k ≠ k) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)` as an intermediate fact.

Conclude with `(not_lt.mpr this) hk`. Establish `hlt : σ j < j`. Break down `lt_or_gt_of_ne hjmove with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (σ.injective (hfix (σ j) h)) hjmove`.

Establish `hP : (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod v = 0`. Apply `prod_ofFn_apply_eq_zero n _ (fun k => u - (k : ℂ) + ν k) v j` to reduce the goal to its premises. Conclude with `hoff _ _ hlt`. Introduce `k hk`. Simplify using `only [id_eq, hfix k hk]`.

Conclude with `hdiag' k`. Rewrite using `[Module.End.mul_apply, hP, map_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem quantumDetHighestWeight_holds : QDetHW := by
  intro V _ _ n E ν v hE hv u
  obtain ⟨hdiag, hup⟩ := hv
  have hdiag' : ∀ k : Fin n, Tm E (u - (k : ℂ)) k k v = (u - (k : ℂ) + ν k) • v := by
    intro k
    rw [Tm, if_pos rfl, LinearMap.add_apply, Module.algebraMap_end_apply, hdiag k, add_smul]
  have hoff : ∀ j k : Fin n, j < k → Tm E (u - (k : ℂ)) j k v = 0 := by
    intro j k hjk
    simp [Tm, ne_of_lt hjk, hup j k hjk]
  unfold qdet qminor
  rw [LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, id_eq, Equiv.Perm.one_apply]
    exact prod_ofFn_apply_of_eigen n _ _ v hdiag'
  · intro σ _ hσ
    have hne : (Finset.univ.filter fun k => σ k ≠ k).Nonempty := by
      by_contra hc
      apply hσ
      refine Equiv.ext fun k => ?_
      by_contra hk
      exact hc ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    set j := (Finset.univ.filter fun k => σ k ≠ k).max' hne with hj
    have hjmove : σ j ≠ j := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hfix : ∀ k, j < k → σ k = k := by
      intro k hk
      by_contra h
      have := Finset.le_max' (Finset.univ.filter fun k => σ k ≠ k) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact (not_lt.mpr this) hk
    have hlt : σ j < j := by
      rcases lt_or_gt_of_ne hjmove with h | h
      · exact h
      · exact absurd (σ.injective (hfix (σ j) h)) hjmove
    have hP : (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod v = 0 := by
      apply prod_ofFn_apply_eq_zero n _ (fun k => u - (k : ℂ) + ν k) v j
      · exact hoff _ _ hlt
      · intro k hk
        simp only [id_eq, hfix k hk]
        exact hdiag' k
    rw [Module.End.mul_apply, hP, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Formalism.REAL
