import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBaseB

noncomputable section

open MeasureTheory Complex Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

namespace GB

def sgnR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

/- English proof (translation)
Apply the tactic sequence `unfold sgn sgnR; split_ifs <;> simp`.
-/
theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sgnR ε a : ℝ) : ℂ) := by
  unfold sgn sgnR; split_ifs <;> simp

/- English proof (translation)
Simplify using `[evX, Qb]`.
-/
theorem evX_Qb (ε : Fin m → Bool) (bb : Bool) (i j : Fin n) (x : Fin m → Fin n → ℂ) :
    evX (Qb ε bb i j) x = ∑ a ∈ Finset.univ.filter (fun a => ε a = bb), star (x a i) * x a j := by
  simp [evX, Qb]

/- English proof (translation)
Unfold `gramX`. Rewrite using `[Qp, evX, map_sub, ← evX, ← evX, evX_Qb, evX_Qb, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Unfold `sgnR`. Apply the tactic sequence `cases h : ε a <;> simp`.
-/
theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, ((sgnR ε a : ℝ) : ℂ) * (star (x a i) * x a j) := by
  unfold gramX
  rw [Qp, evX, map_sub, ← evX, ← evX, evX_Qb, evX_Qb, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgnR
  cases h : ε a <;> simp

/- English proof (translation)
Establish `L : (b * gramX ε x).trace = ∑ a, ∑ i, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i))`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[L]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_gram (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, ((sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j := by
  have L : (b * gramX ε x).trace =
      ∑ a, ∑ i, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    calc (∑ i, ∑ j, ∑ a, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)))
        = ∑ i, ∑ a, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [L]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (congrFun hb j) i` as an intermediate fact. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢`. Rewrite using `[← this]`.
-/
theorem herm_transpose (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : bᵀ.IsHermitian := by
  ext i j
  have := congrFun (congrFun hb j) i
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
  rw [← this]

end GB

open GB in
/- English proof (translation)
Introduce `m n ε c t hc b hb`. Unfold `secN`. Establish `hpt : ∀ x : Fin m → Fin n → ℂ, evX 1 x * gs c x * cexp (Complex.I * t * (b * gramX ε x).trace) = ∏ a, cexp (-(((c * ∑ k, ‖x a k‖ ^ 2 : ℝ)) : ℂ) + Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j)`. Introduce `x`. Establish `h1 : evX (1 : PX m n) x = 1` using `by simp [evX]`.

Rewrite using `[h1, one_mul, gs, ← Complex.exp_add, ← Complex.exp_sum, trace_gram]`. Use `congr 1`. Rewrite using `[Finset.sum_add_distrib]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[Finset.mul_sum, Finset.sum_neg_distrib]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_fintype_prod_volume_eq_prod (fun a (r : Fin n → ℂ) => cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) + Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (r i) * bᵀ i j * r j))]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[GB.gauss_row c (t * sgnR ε a) hc bᵀ (herm_transpose b hb)]`. Establish `e : Complex.I * ((t * sgnR ε a : ℝ) : ℂ) = Complex.I * t * sgn ε a`.

Rewrite using `[sgn_eq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem base : Base := by
  intro m n ε c t hc b hb
  unfold secN
  have hpt : ∀ x : Fin m → Fin n → ℂ, evX 1 x * gs c x * cexp (Complex.I * t * (b * gramX ε x).trace) =
      ∏ a, cexp (-(((c * ∑ k, ‖x a k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j) := by
    intro x
    have h1 : evX (1 : PX m n) x = 1 := by simp [evX]
    rw [h1, one_mul, gs, ← Complex.exp_add, ← Complex.exp_sum, trace_gram]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    · push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast
      ring
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a (r : Fin n → ℂ) => cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (r i) * bᵀ i j * r j))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [GB.gauss_row c (t * sgnR ε a) hc bᵀ (herm_transpose b hb)]
  have e : Complex.I * ((t * sgnR ε a : ℝ) : ℂ) = Complex.I * t * sgn ε a := by
    rw [sgn_eq]; push_cast; ring
  rw [e]
  rfl

end PositivityTheory.Rg.Sw.WR.G
