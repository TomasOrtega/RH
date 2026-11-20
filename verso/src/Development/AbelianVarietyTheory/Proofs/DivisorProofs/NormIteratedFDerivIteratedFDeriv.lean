import Mathlib

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `n generalizing j with`. Consider the case `zero`. Rewrite using `[iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.zero_add]`. Consider the case `succ n ih`. Rewrite using `[iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv, ih (j + 1)]`.

Rewrite using `[show n + (j + 1) = n + 1 + j by omega]`.
-/
theorem norm_iteratedFDeriv_iteratedFDeriv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  induction n generalizing j with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.zero_add]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_fderiv, ih (j + 1)]
    rw [show n + (j + 1) = n + 1 + j by omega]

end GlobalTheory
