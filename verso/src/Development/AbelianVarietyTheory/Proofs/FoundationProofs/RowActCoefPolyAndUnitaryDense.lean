import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on generalizing l with`. Consider the case `C a => exact ⟨C (l (C a)), fun g => by simp [rowAct]⟩`. Consider the case `add p q hp hq`. Take `⟨P, hP⟩` from `hp l`. Take `⟨Q, hQ⟩` from `hq l`.

Conclude with `⟨P + Q, fun g => by simp only [map_add, hP, hQ]⟩`. Consider the case `mul_X p v hp => choose P hP using fun b : Fin n => hp (l ∘ₗ LinearMap.mulRight ℂ (X (b, v.2)))`. Use `⟨∑ b, X (v.1, b) * P b, fun g => ?_⟩` and prove the remaining obligations. Establish `e : rowAct ℂ g (X v) = ∑ b, g v.1 b • X (b, v.2)`. Simplify using `[rowAct, smul_eq_C_mul]`.

Rewrite using `[map_mul, e, Finset.mul_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]`. Both sides reduce to the same expression.
-/
theorem exists_poly_rowAct_coef (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P := by
  induction f using MvPolynomial.induction_on generalizing l with
  | C a => exact ⟨C (l (C a)), fun g => by simp [rowAct]⟩
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp l
    obtain ⟨Q, hQ⟩ := hq l
    exact ⟨P + Q, fun g => by simp only [map_add, hP, hQ]⟩
  | mul_X p v hp =>
    choose P hP using fun b : Fin n => hp (l ∘ₗ LinearMap.mulRight ℂ (X (b, v.2)))
    refine ⟨∑ b, X (v.1, b) * P b, fun g => ?_⟩
    have e : rowAct ℂ g (X v) = ∑ b, g v.1 b • X (b, v.2) := by
      simp [rowAct, smul_eq_C_mul]
    rw [map_mul, e, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
    rfl

/- English proof (translation)
Establish `hinj : Function.Injective (fun x : Fin n × Fin n => ((), x) : Fin n × Fin n → Unit × Fin n × Fin n)` using `fun x y e => congrArg Prod.snd e`. Apply `rename_injective _ hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `Formalism.L2.Col.eq_zero_of_forall_unitary (ι := Unit) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_` and prove the remaining obligations. Rewrite using `[eval_rename]`.

Use `h (u ()) (Matrix.mem_unitaryGroup_iff'.2 (hu ()))` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.
-/
theorem eq_zero_of_vanish_unitaryGroup (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) : P = 0 := by
  have hinj : Function.Injective (fun x : Fin n × Fin n => ((), x) : Fin n × Fin n → Unit × Fin n × Fin n) :=
    fun x y e => congrArg Prod.snd e
  apply rename_injective _ hinj
  rw [map_zero]
  refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := Unit) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
  rw [eval_rename]
  have := h (u ()) (Matrix.mem_unitaryGroup_iff'.2 (hu ()))
  simpa [Function.comp_def] using this

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_poly_rowAct_coef, eq_zero_of_vanish_unitaryGroup⟩`.
-/
theorem rowAct_coef_poly_and_unitary_dense :
    (∀ (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ) (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)),
      ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
        l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P) ∧
    ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
      (∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) → P = 0 :=
  ⟨exists_poly_rowAct_coef, eq_zero_of_vanish_unitaryGroup⟩

end GlobalTheory.Branching
