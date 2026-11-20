import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrRootMem

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cr_pow_mod (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (a : K) (x : V)
    (hx : T x - a • x ∈ Z) (k : ℕ) : (T ^ k) x - a ^ k • x ∈ Z := by
  induction k with
  | zero => simp [Z.zero_mem]
  | succ k ih =>
    have e1 : (T ^ (k + 1)) x = T ((T ^ k) x) := by rw [pow_succ', Module.End.mul_apply]
    have e2 : a ^ (k + 1) • x = a ^ k • (a • x) := by rw [pow_succ, mul_smul]
    have e3 : (T ^ (k + 1)) x - a ^ (k + 1) • x =
        T ((T ^ k) x - a ^ k • x) + a ^ k • (T x - a • x) := by
      rw [e1, e2, map_sub, map_smul, smul_sub]; abel
    rw [e3]
    exact Z.add_mem (hZ _ ih) (Z.smul_mem _ hx)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cr_aeval_mod (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (a : K) (x : V)
    (hx : T x - a • x ∈ Z) (q : K[X]) : aeval T q x - q.eval a • x ∈ Z := by
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · have e : aeval T (p + r) x - (p + r).eval a • x =
        (aeval T p x - p.eval a • x) + (aeval T r x - r.eval a • x) := by
      rw [map_add, LinearMap.add_apply, eval_add, add_smul]; abel
    rw [e]; exact Z.add_mem hp hr
  · rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, eval_monomial, mul_smul,
      ← smul_sub]
    exact Z.smul_mem c (cr_pow_mod T Z hZ a x hx n)

/- English proof (translation)
Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cr_aeval_eig (T : Module.End K V) (a : K) (x : V) (hx : T x = a • x) (q : K[X]) :
    aeval T q x = q.eval a • x := by
  have h := cr_aeval_mod T ⊥ (fun y hy => by
      rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero]) a x
    (by rw [hx, sub_self]; exact Submodule.zero_mem _) q
  rw [Submodule.mem_bot, sub_eq_zero] at h
  exact h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem cr_aeval_stable (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (x : V) (hx : x ∈ Z)
    (q : K[X]) : aeval T q x ∈ Z := by
  have h := cr_aeval_mod T Z hZ 0 x (by rw [zero_smul, sub_zero]; exact hZ x hx) q
  have h' := Z.add_mem h (Z.smul_mem (q.eval 0) hx)
  rwa [sub_add_cancel] at h'

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
-/
theorem cr_aeval_comm (T X' : Module.End K V) (h : T * X' = X' * T) (q : K[X]) (x : V) :
    aeval T q (X' x) = X' (aeval T q x) := by
  have hc : Commute T X' := h
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hr, map_add]
  · rw [aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
    congr 1
    exact LinearMap.congr_fun (hc.pow_left n).eq x

end Formalism.MainNotions.G.GLWeightTheory
