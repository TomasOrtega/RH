import Formalism.JumpKernelCokernel.Statement

noncomputable section

namespace Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial

variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module O V]

/- English proof (translation)
Use `conv_lhs => rw [← Polynomial.divX_mul_X_add P]`. Rewrite using `[map_add, map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, ← Polynomial.coeff_zero_eq_eval_zero, add_comm]`.
-/
theorem decomp (d : Module.End O V) (P : O[X]) (v : V) :
    aeval d P v = P.eval 0 • v + aeval d P.divX (d v) := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add P]
  rw [map_add, map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, ← Polynomial.coeff_zero_eq_eval_zero, add_comm]

/- English proof (translation)
Establish `hd : ∀ v ∈ M, d v ∈ M` using `fun v hv => hM (Submodule.mem_map_of_mem hv)`. Establish `hpow : ∀ (n : ℕ) (v : V), v ∈ M → (d ^ n) v ∈ M`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v hv`.

Simplify using `using hv`. Consider the case `succ n ih`. Introduce `v hv`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (hd v hv)`.

Introduce `Q`. Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Introduce `v hv`. Rewrite using `[map_add, LinearMap.add_apply]`.

Conclude with `M.add_mem (hp v hv) (hq v hv)`. Consider the case `monomial n a`. Introduce `v hv`. Rewrite using `[aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]`. Conclude with `M.smul_mem a (hpow n v hv)`.
-/
theorem aeval_mem (d : Module.End O V) (M : Submodule O V) (hM : M.map d ≤ M) :
    ∀ (Q : O[X]) (v : V), v ∈ M → aeval d Q v ∈ M := by
  have hd : ∀ v ∈ M, d v ∈ M := fun v hv => hM (Submodule.mem_map_of_mem hv)
  have hpow : ∀ (n : ℕ) (v : V), v ∈ M → (d ^ n) v ∈ M := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hd v hv)
  intro Q
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial n a =>
    intro v hv
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact M.smul_mem a (hpow n v hv)

end Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial Formalism.KernelCokernelLengths.PolynomialDegreeLemmas in
/- English proof (translation)
Introduce `O _ V _ _ d P M hM`. Use `⟨fun h0 => ?_, fun h0 u hu => ?_⟩` and prove the remaining obligations. Establish `ha : ∀ v : V, d (aeval d P v) = 0`. Introduce `v`. Establish `h1` using `congrArg (fun f : Module.End O V => f v) h0`.

Simplify `h1` using `[map_mul, aeval_X]`. Use `⟨ha, fun v hv => ?_, fun w hw u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[decomp d P v, hv, map_zero, add_zero]`. Establish `h1` using `decomp d P u`. Establish `h2 : P.eval 0 • w = d (-(aeval d P.divX w))`.

Establish `h3 : P.eval 0 • u = aeval d P u - aeval d P.divX (d u)` using `eq_sub_of_add_eq h1.symm`. Rewrite using `[← hu, ← map_smul, h3, map_sub, ha, zero_sub, map_neg]`. Rewrite using `[h2]`. Conclude with `Submodule.mem_map_of_mem (M.neg_mem (aeval_mem d M hM _ w hw))`. Establish `h1` using `decomp d P u`.

Rewrite `h1` using `[h0, LinearMap.zero_apply]`. Establish `h3 : P.eval 0 • u = -(aeval d P.divX (d u))` using `eq_neg_of_add_eq_zero_left h1.symm`. Rewrite using `[h3]`. Conclude with `M.neg_mem (aeval_mem d M hM _ _ hu)`.
-/
theorem Formalism.KernelCokernelLengths.polynomial_degree_facts : Formalism.KernelCokernelLengths.PdFacts := by
  intro O _ V _ _ d P M hM
  refine ⟨fun h0 => ?_, fun h0 u hu => ?_⟩
  · have ha : ∀ v : V, d (aeval d P v) = 0 := by
      intro v
      have h1 := congrArg (fun f : Module.End O V => f v) h0
      simpa [map_mul, aeval_X] using h1
    refine ⟨ha, fun v hv => ?_, fun w hw u hu => ?_⟩
    · rw [decomp d P v, hv, map_zero, add_zero]
    · have h1 := decomp d P u
      have h2 : P.eval 0 • w = d (-(aeval d P.divX w)) := by
        have h3 : P.eval 0 • u = aeval d P u - aeval d P.divX (d u) := eq_sub_of_add_eq h1.symm
        rw [← hu, ← map_smul, h3, map_sub, ha, zero_sub, map_neg]
      rw [h2]
      exact Submodule.mem_map_of_mem (M.neg_mem (aeval_mem d M hM _ w hw))
  · have h1 := decomp d P u
    rw [h0, LinearMap.zero_apply] at h1
    have h3 : P.eval 0 • u = -(aeval d P.divX (d u)) := eq_neg_of_add_eq_zero_left h1.symm
    rw [h3]
    exact M.neg_mem (aeval_mem d M hM _ _ hu)
