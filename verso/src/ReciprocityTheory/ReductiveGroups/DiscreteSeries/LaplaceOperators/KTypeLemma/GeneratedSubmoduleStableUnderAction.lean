import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMemInvariantSubmodule

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

/- English proof (translation)
Apply the tactic sequence `by_cases h : c = b <;> simp [tensVd, prj, h]`.
-/
theorem tensor_dual_action_apply_component (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (g : Fin n → M) (c : Fin n) :
    tensVd E a b g c = E a b (g c) - (if c = b then g a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

/- English proof (translation)
Simplify using `[eeVd, prj, LinearMap.sum_apply]`.
-/
theorem euler_tensor_dual_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun d => ?_` and prove the remaining obligations. Establish `hc : ∀ c, E d c (E a b (f c)) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) - (if b = d then E a c (f c) else 0)`. Introduce `c`. Use `congrArg (fun T : Module.End ℂ M => T (f c)) (hE d c a b)` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at this`.

Rewrite `this` using `[sub_eq_iff_eq_add]`. Rewrite using `[this]`. Apply the tactic sequence `by_cases h1 : c = a <;> by_cases h2 : b = d <;> simp [h1, h2] <;> abel`. Simplify using `only [Module.End.mul_apply, euler_tensor_dual_apply, tensor_dual_action_apply_component, map_sub, map_neg, map_sum, sum_sub_distrib, hc, sum_add_distrib]`. Distinguish the cases in `hbd : b = d`.

Substitute `hbd` using the available equality. Simplify using `[apply_ite, Finset.sum_ite_eq']`. Normalize the expressions using the abelian group laws. Establish `hdb : d ≠ b` using `Ne.symm hbd`. Simplify using `[hbd, hdb, apply_ite, Finset.sum_ite_eq']`.
-/
theorem euler_tensor_dual_commute_gl_action (hE : IsGlRep E) (a b : Fin n) :
    eeVd E * tensVd E a b = tensVd E a b * eeVd E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  have hc : ∀ c, E d c (E a b (f c)) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) -
      (if b = d then E a c (f c) else 0) := by
    intro c
    have := congrArg (fun T : Module.End ℂ M => T (f c)) (hE d c a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    by_cases h1 : c = a <;> by_cases h2 : b = d <;> simp [h1, h2] <;> abel
  simp only [Module.End.mul_apply, euler_tensor_dual_apply, tensor_dual_action_apply_component, map_sub, map_neg, map_sum,
    sum_sub_distrib, hc, sum_add_distrib]
  by_cases hbd : b = d
  · subst hbd
    simp [apply_ite, Finset.sum_ite_eq']
    abel
  · have hdb : d ≠ b := Ne.symm hbd
    simp [hbd, hdb, apply_ite, Finset.sum_ite_eq']

/- English proof (translation)
Simplify using `[Submodule.mem_pi]`.
-/
theorem mem_pi_submodule_iff {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ Submodule.pi Set.univ (fun _ : Fin n => S) ↔ ∀ c, f c ∈ S := by
  simp [Submodule.mem_pi]

/- English proof (translation)
Rewrite using `[tensor_dual_action_apply_component]`. Use `sub_mem (hS a b _ (hf c)) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hf a`. Conclude with `zero_mem _`.
-/
theorem dualTensorAction_mem {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S) (a b : Fin n)
    {f : Fin n → M} (hf : ∀ c, f c ∈ S) (c : Fin n) : tensVd E a b f c ∈ S := by
  rw [tensor_dual_action_apply_component]
  refine sub_mem (hS a b _ (hf c)) ?_
  split_ifs
  · exact hf a
  · exact zero_mem _

/- English proof (translation)
Rewrite using `[euler_tensor_dual_apply]`. Conclude with `neg_mem (sum_mem fun c _ => hS d c _ (hf c))`.
-/
theorem euler_tensor_dual_mem_of_stable {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S)
    {f : Fin n → M} (hf : ∀ c, f c ∈ S) (d : Fin n) : eeVd E f d ∈ S := by
  rw [euler_tensor_dual_apply]
  exact neg_mem (sum_mem fun c _ => hS d c _ (hf c))

/- English proof (translation)
Unfold `genSub at *`. Rewrite `*` using `[Submodule.mem_sInf]`. Introduce `T hT`. Conclude with `hT.2 a b v (hv T hT)`.
-/
theorem generated_submodule_stable_under_action (V : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E V) :
    E a b v ∈ genSub E V := by
  unfold genSub at *
  rw [Submodule.mem_sInf] at *
  intro T hT
  exact hT.2 a b v (hv T hT)

/- English proof (translation)
The claim follows from `le_sInf fun _ hT => hT.1`.
-/
theorem le_generatedSubmodule_dual (V : Submodule ℂ M) : V ≤ genSub E V := le_sInf fun _ hT => hT.1

/- English proof (translation)
Simplify using `[Xs, Submodule.mem_pi, sub_eq_zero]`.
-/
theorem mem_euler_eigenspace_iff {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs (eeVd E) S θ ↔ (∀ c, f c ∈ S) ∧ eeVd E f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_pi, sub_eq_zero]

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_euler_eigenspace_iff]`. Use `⟨dualTensorAction_mem hS a b hf.1, ?_⟩` and prove the remaining obligations. Use `congrArg (fun T : Module.End ℂ (Fin n → M) => T f) (euler_tensor_dual_commute_gl_action hE a b)` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hf.2, map_smul]`.
-/
theorem euler_eigenspace_stable_under_action (hE : IsGlRep E) {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S)
    {θ : ℝ} (a b : Fin n) {f : Fin n → M} (hf : f ∈ Xs (eeVd E) S θ) :
    tensVd E a b f ∈ Xs (eeVd E) S θ := by
  rw [mem_euler_eigenspace_iff] at hf ⊢
  refine ⟨dualTensorAction_mem hS a b hf.1, ?_⟩
  have := congrArg (fun T : Module.End ℂ (Fin n → M) => T f) (euler_tensor_dual_commute_gl_action hE a b)
  simp only [Module.End.mul_apply] at this
  rw [this, hf.2, map_smul]

end Alg

section Poly

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/- English proof (translation)
Unfold `prodShift`. Rewrite using `[← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Simplify using `[Function.comp, Algebra.algebraMap_eq_smul_one]`.
-/
theorem shifted_product_eq_aeval (A : Module.End ℂ Y) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C (((θ t : ℝ) : ℂ)))) := by
  unfold prodShift
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext t
  simp [Function.comp, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule .. | (apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (apply @UpperTheo …`.
-/
theorem aeval_mem_invariant_submodule (A : Module.End ℂ Y) (p : Submodule ℂ Y) (hA : ∀ y ∈ p, A y ∈ p)
    (q : ℂ[X]) : ∀ y ∈ p, aeval A q y ∈ p := by
  first | exact UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule .. | (apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> first | assumption | infer_instance)

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_left hq`. Consider the case `monomial k c`. Rewrite using `[aeval_monomial]`.

Conclude with `(Algebra.commute_algebraMap_left c T).mul_left (h.pow_left k)`.
-/
theorem aeval_commute_of_commute (A T : Module.End ℂ Y) (h : Commute A T) (q : ℂ[X]) :
    Commute (aeval A q) T := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial k c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left c T).mul_left (h.pow_left k)

end Poly

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
