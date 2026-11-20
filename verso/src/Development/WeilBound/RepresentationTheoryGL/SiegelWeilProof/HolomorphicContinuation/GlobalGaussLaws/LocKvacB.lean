import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacA

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

/- English proof (translation)
Establish `hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0`. Introduce `u W`. Establish `e` using `congrFun (h (fr * W)) (xL θ τ (fr * u))`. Rewrite `e` using `[annS_tens hθ hfr hM l]`. Establish `hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v` using `fun v => by`.

Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]`. Establish `hc : compAt θ τ (xL θ τ (fr * u)) = fr * u`. Use `congrFun (compAt_xL hθ τ (fr * u)) τ` as an intermediate fact. Simplify `this` using `[dirAt_self]`. Establish `hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1`.

Unfold `psi0`. Rewrite using `[compAt_xL hθ, gAway_dirAt, finPart_xL hθ]`. Simplify using `only [one_mul]`. Conclude with `gaussian_at_zero_eq_one D V.rank n`. Rewrite `e` using `[hc, hinv, hinv, hp, mul_one]`.

Conclude with `(mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)`. Establish `hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0`. Introduce `u`. Set `F : ℝ → ℂ` to `fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q`. Establish `hF : ∀ t, HasDerivAt F 0 t`.

Introduce `t`. Establish `hd` using `GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t`. Use `hd.congr_deriv ?_` and prove the remaining obligations. Establish `e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u)` using `(ptX_add_smul _ _ t).symm`. Rewrite using `[e2]`.

Conclude with `hk _ u`. Establish `hdiff : Differentiable ℝ F` using `fun t => (hF t).differentiableAt`. Establish `hc` using `is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0`. Establish `e1 : F 1 = evX Q u` using `by show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q`. Rewrite using `[Complex.ofReal_one, one_smul]`.

Establish `e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u`. Use function extensionality and compare the values at `k`. Take `⟨a, i, b⟩` from `k`. Apply the tactic sequence `cases b <;> simp [ptX]`. Rewrite using `[e3]`.

Establish `e0 : F 0 = evX Q 0` using `by show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q`. Rewrite using `[Complex.ofReal_zero, zero_smul, add_zero]`. Rewrite using `[← e1, ← e0, hc]`. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `evX_eq_zero` to reduce the goal to its premises.

Introduce `u`. Use `show eval _ (Q - C (evX Q 0)) = 0`. Rewrite using `[map_sub, eval_C]`. Conclude with `sub_eq_zero.2 (hconst u)`.
-/
theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
