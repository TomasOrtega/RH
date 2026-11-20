import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2

open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S]
  [DecidableEq S]

/- English proof (translation)
Unfold `pairAt`. Establish `e : ∀ g : Mt k r, B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = m c * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))`. Introduce `g`. Establish `h1` using `hW Φ c (Matrix.of g)`. Simplify using `only at h1`.

Rewrite using `[h1, hsInner_smul_left']`. Repeatedly rewrite using `[e]`. Conclude with `integral_const_mul _ _`.
-/
theorem waveOut_pairAt_left (μ : Measure (Mt k r)) {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → ℂ}
    (hW : multiplicationOperator W (fun c _ => m c)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (W Φ) Ψ c = m c * pairAt μ Φ Ψ c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      m c * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    have h1 := hW Φ c (Matrix.of g)
    simp only at h1
    rw [h1, hsInner_smul_left']
  simp_rw [e]
  exact integral_const_mul _ _

/- English proof (translation)
Unfold `pairAt`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `h1` using `hW Φ c (Matrix.of g)`. Simplify using `only at h1`. Use `show B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _`.

Rewrite using `[h1, hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]`. Simplify using the standard rewrite rules.
-/
theorem waveOut_pairAt_self (μ : Measure (Mt k r)) {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → ℂ}
    (hW : multiplicationOperator W (fun c _ => m c)) (hm : ∀ c, ‖m c‖ = 1) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (W Φ) (W Φ) c = pairAt μ Φ Φ c := by
  unfold pairAt
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have h1 := hW Φ c (Matrix.of g)
  simp only at h1
  show B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
  rw [h1, hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]
  simp

/- English proof (translation)
Unfold `glue`. Rewrite using `[dif_neg (by simp)]`. Use `first`. Consider the case `exact Function.update_self l t c`. Consider the case `simp`.
-/
theorem waveOut_glue (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  unfold glue
  rw [dif_neg (by simp)]
  first
  | exact Function.update_self l t c
  | simp

/- English proof (translation)
Establish `e : (fun c' : Cf r l.succ => ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c')) = fun c' => fsv s t * (((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c'))`. Use function extensionality and compare the values at `c'`. Establish `hp : ∀ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c') = fsv s t * pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c')`. Introduce `a`. Rewrite using `[waveOut_pairAt_left (m := fun c' => fsv s (c' l)) μ hW, waveOut_glue]`.

Simplify using `only [hp, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Dens, form]`. Rewrite using `[e, integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem waveOut_dens (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) {W : Module.End ℂ (RadSp k r z z' π π')}
    (hW : multiplicationOperator W (fun c' _ => fsv s (c' l))) (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    Dens μ l (fun b => W (u b)) v c t = fsv s t * Dens μ l u v c t := by
  have e : (fun c' : Cf r l.succ => ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c')) =
      fun c' => fsv s t * (((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c')) := by
    funext c'
    have hp : ∀ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c') =
        fsv s t * pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c') := by
      intro a
      rw [waveOut_pairAt_left (m := fun c' => fsv s (c' l)) μ hW, waveOut_glue]
    simp only [hp, ← Finset.mul_sum]
    ring
  simp only [Dens, form]
  rw [e, integral_const_mul]
  ring

end Wave

end Formalism.FourierDecayAlt.P.CutSE
