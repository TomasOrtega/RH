import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TensorGLSums

/- English proof (translation)
Introduce `a b c d`. Establish `key : ∀ x y u v : R, (x + u) * (y + v) - (y + v) * (x + u) = (x * y - y * x) + (x * v - v * x) + (u * y - y * u) + (u * v - v * u)` using `by intros; noncomm_ring`. Simplify using `only`. Rewrite using `[key, hL]`. Establish `h1 : L a b * ∑ p ∈ S, e p c d - (∑ p ∈ S, e p c d) * L a b = 0`.

Rewrite using `[sub_eq_zero]`. Conclude with `(Commute.sum_right _ _ _ fun p _ => hLe p a b c d).eq`. Establish `h2 : (∑ p ∈ S, e p a b) * L c d - L c d * ∑ p ∈ S, e p a b = 0`. Rewrite using `[sub_eq_zero]`. Conclude with `(Commute.sum_left _ _ _ fun p _ => (hLe p c d a b).symm).eq`.

Establish `h3 : (∑ p ∈ S, e p a b) * (∑ q ∈ S, e q c d) - (∑ q ∈ S, e q c d) * (∑ p ∈ S, e p a b) = ∑ p ∈ S, ((if b = c then e p a d else 0) - (if d = a then e p c b else 0))`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := S) (t := S) (f := fun q p => e q c d * e p a b), ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Repeatedly rewrite using `[he p]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using `[hp]`. Rewrite using `[h1, h2, h3]`. Apply the tactic sequence `split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel`.
-/
theorem glSum {R : Type*} [Ring R] {n : ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι) (L : Fin n → Fin n → R)
    (e : ι → Fin n → Fin n → R) (hL : GlRel L) (hLe : ∀ p a b c d, Commute (L a b) (e p c d))
    (he : ∀ p q a b c d, e p a b * e q c d - e q c d * e p a b =
      if p = q then (if b = c then e p a d else 0) - (if d = a then e p c b else 0) else 0) :
    GlRel (fun a b => L a b + ∑ p ∈ S, e p a b) := by
  intro a b c d
  have key : ∀ x y u v : R, (x + u) * (y + v) - (y + v) * (x + u) =
      (x * y - y * x) + (x * v - v * x) + (u * y - y * u) + (u * v - v * u) := by
    intros; noncomm_ring
  simp only
  rw [key, hL]
  have h1 : L a b * ∑ p ∈ S, e p c d - (∑ p ∈ S, e p c d) * L a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_right _ _ _ fun p _ => hLe p a b c d).eq
  have h2 : (∑ p ∈ S, e p a b) * L c d - L c d * ∑ p ∈ S, e p a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_left _ _ _ fun p _ => (hLe p c d a b).symm).eq
  have h3 : (∑ p ∈ S, e p a b) * (∑ q ∈ S, e q c d) - (∑ q ∈ S, e q c d) * (∑ p ∈ S, e p a b) =
      ∑ p ∈ S, ((if b = c then e p a d else 0) - (if d = a then e p c b else 0)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := S) (t := S)
      (f := fun q p => e q c d * e p a b), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_sub_distrib]
    simp_rw [he p]
    rw [Finset.sum_ite_eq]
    simp [hp]
  rw [h1, h2, h3]
  split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel

/- English proof (translation)
Rewrite using `[Commute, SemiconjBy, ← sub_eq_zero]`. Establish `hterm : ∀ a b, L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a) = ((if b = c then L a d * e b a else 0) - (if d = a then L c b * e b a else 0)) + ((if a = c then L a b * e b d else 0) - (if d = b then L a b * e c a else 0))`. Introduce `a b`. Establish `h1 : e b a * L c d = L c d * e b a` using `((hLe c d b a).eq).symm`. Establish `h2 : e c d * L a b = L a b * e c d` using `((hLe a b c d).eq).symm`.

Establish `h3` using `hL a b c d`. Establish `e1` using `he b a c d`. Establish `e2` using `he c d b a`. Combine the equalities or inequalities in the displayed calculation. Establish `k1 : L a b * e b a * L c d = L a b * L c d * e b a` using `by rw [mul_assoc, h1, ← mul_assoc]`.

Establish `k2 : e c d * (L a b * e b a) = L a b * e c d * e b a` using `by rw [← mul_assoc, h2]`. Rewrite using `[mul_add, add_mul, k1, k2]`. Use `noncomm_ring`. Use `_ = _ := by`. Rewrite using `[h3, e1, e2]`.

Apply the tactic sequence `split_ifs <;> simp [sub_mul, mul_sub]`. Establish `hx : (∑ a, ∑ b, L a b * e b a) * (L c d + e c d) - (L c d + e c d) * (∑ a, ∑ b, L a b * e b a) = ∑ a, ∑ b, (L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a))`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Rewrite using `[hx]`. Repeatedly rewrite using `[hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]`.

Simplify using `only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_comm (f := fun a b => if d = a then L c b * e b a else 0)]`. Rewrite using `[Finset.sum_comm (f := fun a b => if a = c then L a b * e b d else 0)]`. Simplify using `only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Normalize the expressions using the abelian group laws.
-/
theorem omComm {R : Type*} [Ring R] {n : ℕ} (L e : Fin n → Fin n → R) (hL : GlRel L)
    (hLe : ∀ a b c d, Commute (L a b) (e c d)) (he : ∀ a b c d, e a b * e c d = if b = c then e a d else 0)
    (c d : Fin n) : Commute (∑ a, ∑ b, L a b * e b a) (L c d + e c d) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  have hterm : ∀ a b, L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a) =
      ((if b = c then L a d * e b a else 0) - (if d = a then L c b * e b a else 0)) +
      ((if a = c then L a b * e b d else 0) - (if d = b then L a b * e c a else 0)) := by
    intro a b
    have h1 : e b a * L c d = L c d * e b a := ((hLe c d b a).eq).symm
    have h2 : e c d * L a b = L a b * e c d := ((hLe a b c d).eq).symm
    have h3 := hL a b c d
    have e1 := he b a c d
    have e2 := he c d b a
    calc L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)
        = (L a b * L c d - L c d * L a b) * e b a + L a b * (e b a * e c d - e c d * e b a) := by
          have k1 : L a b * e b a * L c d = L a b * L c d * e b a := by rw [mul_assoc, h1, ← mul_assoc]
          have k2 : e c d * (L a b * e b a) = L a b * e c d * e b a := by rw [← mul_assoc, h2]
          rw [mul_add, add_mul, k1, k2]
          noncomm_ring
      _ = _ := by
          rw [h3, e1, e2]
          split_ifs <;> simp [sub_mul, mul_sub]
  have hx : (∑ a, ∑ b, L a b * e b a) * (L c d + e c d) - (L c d + e c d) * (∑ a, ∑ b, L a b * e b a) =
      ∑ a, ∑ b, (L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hx]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if d = a then L c b * e b a else 0)]
  rw [Finset.sum_comm (f := fun a b => if a = c then L a b * e b d else 0)]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [DecidableEq P]

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun I => ?_` and prove the remaining obligations. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality. Simplify using `[Module.End.mul_apply, eAt_apply, Function.update_idem]`. Simplify using `[Module.End.mul_apply, eAt_apply, hbc]`.
-/
theorem eAt_mul (p : P) (a b c d : Fin n) :
    (eAt p a b * eAt p c d : Module.End ℂ (TV n M P)) = if b = c then eAt p a d else 0 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  by_cases hbc : b = c
  · subst hbc
    simp [Module.End.mul_apply, eAt_apply, Function.update_idem]
  · simp [Module.End.mul_apply, eAt_apply, hbc]

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun I => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, eAt_apply, Function.update_of_ne h, Function.update_of_ne (Ne.symm h), Function.update_comm h]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem eAt_comm {p q : P} (h : p ≠ q) (a b c d : Fin n) :
    (eAt p a b * eAt q c d : Module.End ℂ (TV n M P)) = eAt q c d * eAt p a b := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, Function.update_of_ne h, Function.update_of_ne (Ne.symm h),
    Function.update_comm h]
  split_ifs <;> rfl

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun I => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, eAt_apply, pm_apply, Function.comp_apply]`. Rewrite using `[Function.update_comp_equiv]`. Simplify using the standard rewrite rules.
-/
theorem pm_eAt (σ : Equiv.Perm P) (p : P) (a b : Fin n) :
    (pm σ * eAt p a b : Module.End ℂ (TV n M P)) = eAt (σ p) a b * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, pm_apply, Function.comp_apply]
  rw [Function.update_comp_equiv]
  simp

omit [DecidableEq P] in
/- English proof (translation)
Introduce `a b c d`. Use `congrArg (liftA n M P) (hE a b c d)` as an intermediate fact. Simplify using `only [map_sub, map_mul, apply_ite (liftA n M P), map_zero] at this`. Conclude with `this`.
-/
theorem glLift (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) :
    GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M P))) := by
  intro a b c d
  have := congrArg (liftA n M P) (hE a b c d)
  simp only [map_sub, map_mul, apply_ite (liftA n M P), map_zero] at this
  exact this

end TensorGLSums

open TensorGLSums in
/- English proof (translation)
Introduce `n M _ _ P _ _ E hE S`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `glSum S _ _ (glLift E hE) (fun p a b c d => lift_comm_eAt _ _ _ _) fun p q a b c d => by`. Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality.

Rewrite using `[if_pos rfl, eAt_mul, eAt_mul]`. Rewrite using `[if_neg hpq, eAt_comm hpq, sub_self]`. Introduce `p hp a b`. Establish `hsplit : tE S E a b = (lift (E a b) + eAt p a b) + ∑ q ∈ S.erase p, eAt q a b`. Rewrite using `[tE, add_assoc]`.

Use `congr 1`. Conclude with `(Finset.add_sum_erase S (fun q => eAt q a b) hp).symm`. Rewrite using `[hsplit]`. Use `Commute.add_right ?_ (Commute.sum_right _ _ _ fun q hq => ?_)` and prove the remaining obligations. Conclude with `omComm (fun a b => lift (E a b)) (fun a b => eAt p a b) (glLift E hE) (fun a b c d => lift_comm_eAt _ _ _ _) (fun a b c d => eAt_mul p a b c d) a b`.

Establish `hqp : q ≠ p` using `Finset.ne_of_mem_erase hq`. Use `Commute.sum_left _ _ _ fun a' _ => Commute.sum_left _ _ _ fun b' _ => ?_` and prove the remaining obligations. Conclude with `Commute.mul_left (lift_comm_eAt _ _ _ _) (eAt_comm (Ne.symm hqp) _ _ _ _)`. Introduce `σ hσ a b`. Rewrite using `[tE, Commute, SemiconjBy, mul_add, add_mul, (lift_comm_pm _ σ).eq, Finset.mul_sum, Finset.sum_mul]`.

Use `congr 1`. Repeatedly rewrite using `[pm_eAt]`. Conclude with `Finset.sum_equiv σ (fun p => (hσ p).symm) fun p _ => rfl`. Introduce `σ p`. Simplify using `only [Om, Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← (lift_comm_pm _ σ).eq, mul_assoc, pm_eAt, mul_assoc]`.
-/
theorem tensorGl_holds : TensorGl := by
  intro n M _ _ P _ _ E hE S
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact glSum S _ _ (glLift E hE) (fun p a b c d => lift_comm_eAt _ _ _ _) fun p q a b c d => by
      by_cases hpq : p = q
      · subst hpq; rw [if_pos rfl, eAt_mul, eAt_mul]
      · rw [if_neg hpq, eAt_comm hpq, sub_self]
  · intro p hp a b
    have hsplit : tE S E a b = (lift (E a b) + eAt p a b) + ∑ q ∈ S.erase p, eAt q a b := by
      rw [tE, add_assoc]; congr 1; exact (Finset.add_sum_erase S (fun q => eAt q a b) hp).symm
    rw [hsplit]
    refine Commute.add_right ?_ (Commute.sum_right _ _ _ fun q hq => ?_)
    · exact omComm (fun a b => lift (E a b)) (fun a b => eAt p a b) (glLift E hE)
        (fun a b c d => lift_comm_eAt _ _ _ _) (fun a b c d => eAt_mul p a b c d) a b
    · have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      refine Commute.sum_left _ _ _ fun a' _ => Commute.sum_left _ _ _ fun b' _ => ?_
      exact Commute.mul_left (lift_comm_eAt _ _ _ _) (eAt_comm (Ne.symm hqp) _ _ _ _)
  · intro σ hσ a b
    rw [tE, Commute, SemiconjBy, mul_add, add_mul, (lift_comm_pm _ σ).eq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    simp_rw [pm_eAt]
    exact Finset.sum_equiv σ (fun p => (hσ p).symm) fun p _ => rfl
  · intro σ p
    simp only [Om, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← (lift_comm_pm _ σ).eq, mul_assoc, pm_eAt, mul_assoc]

end PositivityTheory.Rg.Cz

end
