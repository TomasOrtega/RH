import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrRootMem

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [Z.zero_mem]`. Consider the case `succ k ih`. Establish `e1 : (T ^ (k + 1)) x = T ((T ^ k) x)` using `by rw [pow_succ', Module.End.mul_apply]`. Establish `e2 : a ^ (k + 1) • x = a ^ k • (a • x)` using `by rw [pow_succ, mul_smul]`.

Establish `e3 : (T ^ (k + 1)) x - a ^ (k + 1) • x = T ((T ^ k) x - a ^ k • x) + a ^ k • (T x - a • x)`. Rewrite using `[e1, e2, map_sub, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e3]`. Conclude with `Z.add_mem (hZ _ ih) (Z.smul_mem _ hx)`.
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
Use `Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)` and prove the remaining obligations. Establish `e : aeval T (p + r) x - (p + r).eval a • x = (aeval T p x - p.eval a • x) + (aeval T r x - r.eval a • x)`. Rewrite using `[map_add, LinearMap.add_apply, eval_add, add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `Z.add_mem hp hr`. Rewrite using `[aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, eval_monomial, mul_smul, ← smul_sub]`. Conclude with `Z.smul_mem c (cr_pow_mod T Z hZ a x hx n)`.
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
Establish `h` using `cr_aeval_mod T ⊥ (fun y hy => by`. Rewrite `hy`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hy, map_zero]) a x`. Use the proof step `(by rw [hx, sub_self]; exact Submodule.zero_mem _) q`. Rewrite `h` using `[Submodule.mem_bot, sub_eq_zero]`.

Conclude with `h`.
-/
theorem cr_aeval_eig (T : Module.End K V) (a : K) (x : V) (hx : T x = a • x) (q : K[X]) :
    aeval T q x = q.eval a • x := by
  have h := cr_aeval_mod T ⊥ (fun y hy => by
      rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero]) a x
    (by rw [hx, sub_self]; exact Submodule.zero_mem _) q
  rw [Submodule.mem_bot, sub_eq_zero] at h
  exact h

/- English proof (translation)
Establish `h` using `cr_aeval_mod T Z hZ 0 x (by rw [zero_smul, sub_zero]; exact hZ x hx) q`. Establish `h'` using `Z.add_mem h (Z.smul_mem (q.eval 0) hx)`. Rewrite `h'` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem cr_aeval_stable (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (x : V) (hx : x ∈ Z)
    (q : K[X]) : aeval T q x ∈ Z := by
  have h := cr_aeval_mod T Z hZ 0 x (by rw [zero_smul, sub_zero]; exact hZ x hx) q
  have h' := Z.add_mem h (Z.smul_mem (q.eval 0) hx)
  rwa [sub_add_cancel] at h'

/- English proof (translation)
Establish `hc : Commute T X'` using `h`. Use `Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)` and prove the remaining obligations. Rewrite using `[map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hr, map_add]`. Rewrite using `[aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]`. Use `congr 1`.

Conclude with `LinearMap.congr_fun (hc.pow_left n).eq x`.
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
