import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SumNonneg
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KFiniteDerivativesFiniteSpanStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselCoefBound

/- English proof (translation)
Take `⟨C, Ws, -, hb⟩` from `GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok x hx`. Establish `hys : y ∈ R.sm` using `(GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hR).2.2.2.2.1 y hy`. Use `⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W y‖).sum, fun g hg => ?_⟩` and prove the remaining obligations. Establish `pg` using `GlobalTheory.BesselDecay.gN_pos' hg`. Establish `h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1`.

Rewrite using `[← Real.rpow_add pg]`. Simplify using the standard rewrite rules. Establish `pg' : 0 < B.gN g ^ (aOf r h - 1)` using `Real.rpow_pos_of_pos pg _`. Use `(mul_le_mul_of_nonneg_left (hb y hys g hg) pg'.le).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_left_comm, h3, mul_one]`.
-/
theorem pair_bound (H : HypsG) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) (hR : R.IsDG ε mu) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε mu h) (hok : GapOK k r h)
    (x y : R.H) (hx : x ∈ R.TK) (hy : y ∈ R.TK) :
    ∃ c : ℝ, ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪x, R.σ g y⟫_ℂ‖ ≤ c := by
  obtain ⟨C, Ws, -, hb⟩ := GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok x hx
  have hys : y ∈ R.sm := (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hR).2.2.2.2.1 y hy
  refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W y‖).sum, fun g hg => ?_⟩
  have pg := GlobalTheory.BesselDecay.gN_pos' hg
  have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
    rw [← Real.rpow_add pg]; simp
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
  refine (mul_le_mul_of_nonneg_left (hb y hys g hg) pg'.le).trans (le_of_eq ?_)
  rw [mul_left_comm, h3, mul_one]

/- English proof (translation)
Introduce `H k r ε mu h R hR hgap hok x hx y hy m`. Take `⟨M, xs, hxs, hxa⟩` from `GlobalTheory.T.k_finite_derivatives_finite_span H.1.2.2.1 k r ε mu R hR x hx m`. Take `⟨N, ys, hys, hyb⟩` from `GlobalTheory.T.k_finite_derivatives_finite_span H.1.2.2.1 k r ε mu R hR y hy m`. Use `choose c hc using fun (i : Fin M) (j : Fin N) => pair_bound H R hR hgap hok (xs i) (ys j) (hxs i) (hys j)`. Use `⟨∑ i, ∑ j, c i j, fun a b ha hb hl g hg => ?_⟩` and prove the remaining obligations.

Take `⟨co, hco, ea⟩` from `hxa a ha (by omega)`. Take `⟨co', hco', eb⟩` from `hyb b hb (by omega)`. Establish `pg' : 0 < B.gN g ^ (aOf r h - 1)` using `Real.rpow_pos_of_pos (GlobalTheory.BesselDecay.gN_pos' hg) _`. Rewrite using `[ea, eb, map_sum, sum_inner]`. Use `(mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum]`. Use `(mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_le_sum fun j _ => le_trans (mul_le_mul_of_nonneg_left ?_ pg'.le) (hc i j g hg)` and prove the remaining obligations. Rewrite using `[map_smul, inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]`. Establish `n0` using `norm_nonneg ⟪xs i, R.σ g (ys j)⟫_ℂ`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hco i`.

Conclude with `hco' j`. Use `_ = _ := by ring`.
-/
theorem coef_bound : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ m : ℕ, ∃ c : ℝ, ∀ a b : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → (∀ Y ∈ b, B.unitLie k r Y) → a.length + b.length ≤ m → ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ‖ ≤ c := by
  intro H k r ε mu h R hR hgap hok x hx y hy m
  obtain ⟨M, xs, hxs, hxa⟩ := GlobalTheory.T.k_finite_derivatives_finite_span H.1.2.2.1 k r ε mu R hR x hx m
  obtain ⟨N, ys, hys, hyb⟩ := GlobalTheory.T.k_finite_derivatives_finite_span H.1.2.2.1 k r ε mu R hR y hy m
  choose c hc using fun (i : Fin M) (j : Fin N) => pair_bound H R hR hgap hok (xs i) (ys j) (hxs i) (hys j)
  refine ⟨∑ i, ∑ j, c i j, fun a b ha hb hl g hg => ?_⟩
  obtain ⟨co, hco, ea⟩ := hxa a ha (by omega)
  obtain ⟨co', hco', eb⟩ := hyb b hb (by omega)
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos (GlobalTheory.BesselDecay.gN_pos' hg) _
  rw [ea, eb, map_sum, sum_inner]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_sum]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => le_trans (mul_le_mul_of_nonneg_left ?_ pg'.le) (hc i j g hg)
  rw [map_smul, inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have n0 := norm_nonneg ⟪xs i, R.σ g (ys j)⟫_ℂ
  calc _ ≤ 1 * (1 * ‖⟪xs i, R.σ g (ys j)⟫_ℂ‖) := by
        gcongr
        · exact hco i
        · exact hco' j
    _ = _ := by ring

end GlobalTheory.BesselCoefBound
