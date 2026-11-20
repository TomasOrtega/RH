import Mathlib

universe u_3 u_4

namespace Bl.general_b_fact_upper_form

/- English proof (translation)
Introduce `LL M _ _ _ T W hW p`. Use `Polynomial.induction_on p ?_ ?_ ?_` and prove the remaining obligations. Introduce `a x hx`. Rewrite using `[Polynomial.aeval_C, Module.algebraMap_end_apply]`. Conclude with `W.smul_mem a hx`.

Introduce `p q hp hq x hx`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `W.add_mem (hp x hx) (hq x hx)`. Introduce `n a h x hx`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]`.

Conclude with `h (T x) (hW x hx)`.
-/
theorem goal1 :
  ∀ {LL : Type u_3} {M : Type u_4} [inst : Field.{u_3} LL] [inst_1 : AddCommGroup.{u_4} M]
  [inst_2 : Module.{u_3, u_4} LL M] (T : Module.End.{u_3, u_4} LL M) (W : Submodule.{u_3, u_4} LL M),
  (∀ (x : M),
      Membership.mem.{u_4, u_4} W x → Membership.mem.{u_4, u_4} W (DFunLike.coe.{u_4 + 1, u_4 + 1, u_4 + 1} T x)) →
    ∀ (p : Polynomial.{u_3} LL) (x : M),
      Membership.mem.{u_4, u_4} W x →
        Membership.mem.{u_4, u_4} W
          (DFunLike.coe.{u_4 + 1, u_4 + 1, u_4 + 1}
            (DFunLike.coe.{max (u_4 + 1) (u_3 + 1), u_3 + 1, u_4 + 1} (Polynomial.aeval.{u_3, u_4} T) p) x) := by
  intro LL M _ _ _ T W hW p
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a x hx
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact W.smul_mem a hx
  · intro p q hp hq x hx
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  · intro n a h x hx
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact h (T x) (hW x hx)

end Bl.general_b_fact_upper_form
