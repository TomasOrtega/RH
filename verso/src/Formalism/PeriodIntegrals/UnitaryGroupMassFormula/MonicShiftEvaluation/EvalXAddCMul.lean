import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalWR

open Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation

open Formalism.QuantumDeterminants

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev R (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] := Module.End ℂ (WSm r E)

def PQ (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : ℕ → (R r E)[X] × (R r E)[X]
  | 0 => (1, 0)
  | i + 1 =>
    if h : i < r then
      ((X + C (pEnd ⟨i, h⟩)) * (PQ r E i).1 - C (cEnd ⟨i, h⟩) * (PQ r E i).2,
        C (ciEnd ⟨i, h⟩) * (PQ r E i).1)
    else PQ r E i

/- English proof (translation)
Rewrite using `[add_mul, eval_add, eval_C_mul, (commute_X P).eq, eval_mul_X, Algebra.commutes]`.
-/
theorem eval_X_add_C_mul (r : ℕ) (P : (R r E)[X]) (q : R r E) (Y : ℂ) :
    ((X + C q) * P).eval (algebraMap ℂ (R r E) Y) =
      algebraMap ℂ (R r E) Y * P.eval (algebraMap ℂ (R r E) Y) + q * P.eval (algebraMap ℂ (R r E) Y) := by
  rw [add_mul, eval_add, eval_C_mul, (commute_X P).eq, eval_mul_X, Algebra.commutes]

/- English proof (translation)
Proceed by induction on `i generalizing f with`. Consider the case `zero => simp [vAB, PQ]`. Consider the case `succ i ih`. Distinguish the cases in `h : i < r`. Simplify using `only [vAB, PQ, dif_pos h]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(ih f).1, (ih f).2, eval_sub, eval_X_add_C_mul, eval_C_mul]`. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul]`. Both sides reduce to the same expression. Rewrite using `[(ih f).1, eval_C_mul]`.

Both sides reduce to the same expression. Simplify using `only [vAB, PQ, dif_neg h]`. Conclude with `ih f`.
-/
theorem vAB_eval (r : ℕ) (Y : ℂ) (i : ℕ) (f : WSm r E) :
    (vAB r Y i).1 (f : (Fin r → ℂ) → E) = (((PQ r E i).1.eval (algebraMap ℂ (R r E) Y)) f : WSm r E) ∧
    (vAB r Y i).2 (f : (Fin r → ℂ) → E) = (((PQ r E i).2.eval (algebraMap ℂ (R r E) Y)) f : WSm r E) := by
  induction i generalizing f with
  | zero => simp [vAB, PQ]
  | succ i ih =>
    by_cases h : i < r
    · simp only [vAB, PQ, dif_pos h]
      refine ⟨?_, ?_⟩
      · rw [(ih f).1, (ih f).2, eval_sub, eval_X_add_C_mul, eval_C_mul]
        simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
          Module.algebraMap_end_apply, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul]
        rfl
      · rw [(ih f).1, eval_C_mul]
        rfl
    · simp only [vAB, PQ, dif_neg h]
      exact ih f

end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
