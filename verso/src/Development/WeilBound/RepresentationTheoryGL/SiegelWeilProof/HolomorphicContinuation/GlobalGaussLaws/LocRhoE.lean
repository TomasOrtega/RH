import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoD

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

open Classical in

def substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    PX m n :=
  aeval (fun v : D.what₂.Tau × Fin m × Fin n × Bool => if v.1 = τ then
      (if v.2.2.2 then ∑ c, C (star (fr v.2.1 c)) * X (c, v.2.2.1, true) else ∑ c, C (fr v.2.1 c) * X (c, v.2.2.1, false))
    else 0) p

/- English proof (translation)
Unfold `evX substP evalPoly`. Rewrite using `[eval_aeval_subst]`. Use `congrArg (fun x => MvPolynomial.eval x p) (funext fun v => ?_)` and prove the remaining obligations. Take `⟨τ', a, j, b⟩` from `v`. Distinguish the cases in `hτ : τ' = τ`.

Substitute `hτ` using the available equality. Rewrite using `[if_pos rfl, dirAt_self]`. Consider the cases of `b`. Simplify using `only [Bool.false_eq_true, ↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply]`. Simplify using `only [↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, map_sum, Complex.star_def]`.

Rewrite using `[if_neg hτ, dirAt_ne hτ]`. Apply the tactic sequence `cases b <;> simp`.
-/
theorem evX_substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (u : Matrix (Fin m) (Fin n) ℂ) :
    evX (substP τ fr p) u = evalPoly p (GlobalTheory.FockAnnKill.dirAt τ (fr * u)) := by
  classical
  unfold evX substP evalPoly
  rw [eval_aeval_subst]
  refine congrArg (fun x => MvPolynomial.eval x p) (funext fun v => ?_)
  obtain ⟨τ', a, j, b⟩ := v
  by_cases hτ : τ' = τ
  · subst hτ
    rw [if_pos rfl, dirAt_self]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply]
    · simp only [↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, map_sum, Complex.star_def]
  · rw [if_neg hτ, dirAt_ne hτ]
    cases b <;> simp

/- English proof (translation)
Introduce `F hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Take `⟨p, g, -, rfl⟩` from `hF`. Use `⟨C (g 0) * substP τ fr p, fun u => ?_⟩` and prove the remaining obligations.

Use `show evalPoly p (fun τ' => compAt θ τ' (xL θ τ (fr * u))) * gauss V l s (fun τ' => compAt θ τ' (xL θ τ (fr * u))) * g (fun i j => finPart D ((xL θ τ (fr * u)) i j)) = _`. Rewrite using `[compAt_xL hθ, finPart_xL hθ, gauss_dirAt hfr, ← evX_substP]`. Simplify using `only [evX, map_mul, eval_C]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, fun u => by simp [evX]⟩`.

Consider the case `add F G _ _ hF hG`. Take `⟨Q₁, h₁⟩` from `hF`. Take `⟨Q₂, h₂⟩` from `hG`. Use `⟨Q₁ + Q₂, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, h₁, h₂, evX, map_add]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a F _ hF`. Take `⟨Q, h⟩` from `hF`. Use `⟨C a * Q, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, h, evX, map_mul, eval_C]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) :
    ∀ F ∈ fockA θ V n l s, ∃ Q : PX V.rank n, ∀ u : Matrix (Fin V.rank) (Fin n) ℂ,
      F (xL θ τ (fr * u)) = evX Q u * gs (cLoc l τ) u := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, g, -, rfl⟩ := hF
    refine ⟨C (g 0) * substP τ fr p, fun u => ?_⟩
    show evalPoly p (fun τ' => compAt θ τ' (xL θ τ (fr * u))) * gauss V l s (fun τ' => compAt θ τ' (xL θ τ (fr * u))) *
        g (fun i j => finPart D ((xL θ τ (fr * u)) i j)) = _
    rw [compAt_xL hθ, finPart_xL hθ, gauss_dirAt hfr, ← evX_substP]
    simp only [evX, map_mul, eval_C]
    ring
  | zero => exact ⟨0, fun u => by simp [evX]⟩
  | add F G _ _ hF hG =>
    obtain ⟨Q₁, h₁⟩ := hF
    obtain ⟨Q₂, h₂⟩ := hG
    refine ⟨Q₁ + Q₂, fun u => ?_⟩
    simp only [Pi.add_apply, h₁, h₂, evX, map_add]
    ring
  | smul a F _ hF =>
    obtain ⟨Q, h⟩ := hF
    refine ⟨C a * Q, fun u => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, h, evX, map_mul, eval_C]
    ring

/- English proof (translation)
Take `⟨Q, hQ⟩` from `slice hθ hfr l _ hf`. Use `⟨Q, funext fun (u : Matrix (Fin V.rank) (Fin n) ℂ) => ?_⟩` and prove the remaining obligations. Establish `h` using `hQ u`. Establish `hinv : fr⁻¹ * (fr * u) = u`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]`.

Establish `hc : compAt θ τ (xL θ τ (fr * u)) = fr * u`. Use `congrFun (compAt_xL hθ τ (fr * u)) τ` as an intermediate fact. Simplify `this` using `[dirAt_self]`. Establish `hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1`. Unfold `psi0`.

Rewrite using `[compAt_xL hθ, gAway_dirAt, finPart_xL hθ]`. Simplify using `only [one_mul]`. Conclude with `gaussian_at_zero_eq_one D V.rank n`. Simplify using `only [tens] at h`. Rewrite `h` using `[hc, hinv, hp, mul_one]`.

Conclude with `h`.
-/
theorem tens_slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) (f : (Fin V.rank → Fin n → ℂ) → ℂ)
    (hf : tens θ τ fr f (psi0 θ V n l s τ) ∈ fockA θ V n l s) : ∃ Q : PX V.rank n, f = fP (cLoc l τ) Q := by
  obtain ⟨Q, hQ⟩ := slice hθ hfr l _ hf
  refine ⟨Q, funext fun (u : Matrix (Fin V.rank) (Fin n) ℂ) => ?_⟩
  have h := hQ u
  have hinv : fr⁻¹ * (fr * u) = u := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
  have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
    have := congrFun (compAt_xL hθ τ (fr * u)) τ
    simpa [dirAt_self] using this
  have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
    unfold psi0
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
    simp only [one_mul]
    exact gaussian_at_zero_eq_one D V.rank n
  simp only [tens] at h
  rw [hc, hinv, hp, mul_one] at h
  exact h

end PositivityTheory.Rg.Sw.Glob.RhoH
