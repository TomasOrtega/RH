import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ g hg j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `m x`. Simplify using `[iteratedFDeriv_zero_apply]`.

Consider the case `succ n ih`. Introduce `m x`. Rewrite using `[iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]`. Establish `hfun : (List.ofFn (fun i : Fin n => m i.succ)).foldr (fun v g' => fun z => fderiv ℝ g' z v) g = fun z => iteratedFDeriv ℝ n g z (Fin.tail m)`. Use function extensionality and compare the values at `z`.

Conclude with `(ih (Fin.tail m) z).symm`. Simplify using `only [hfun]`. Apply the tactic sequence `have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x := (hg.differentiable_iteratedFDeriv (by first | exact_mod_cast ENat.coe_lt_top n | simp | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top n))) x`. Rewrite using `[fderiv_continuousMultilinear_apply_const_apply hd]`.
-/
theorem iteratedFDeriv_apply_eq_foldr_fderiv :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  intro E _ _ g hg j
  induction j with
  | zero =>
    intro m x
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m x
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]
    have hfun : (List.ofFn (fun i : Fin n => m i.succ)).foldr (fun v g' => fun z => fderiv ℝ g' z v) g
        = fun z => iteratedFDeriv ℝ n g z (Fin.tail m) := by
      funext z
      exact (ih (Fin.tail m) z).symm
    simp only [hfun]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.differentiable_iteratedFDeriv (by first | exact_mod_cast ENat.coe_lt_top n | simp | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top n))) x
    rw [fderiv_continuousMultilinear_apply_const_apply hd]

end GlobalTheory
