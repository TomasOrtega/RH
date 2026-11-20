import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocalOfFibres

namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt NumberField

noncomputable section

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def betaL (S : C.HidaSetting E Wp Wq) : ℂ := ((4 * Real.pi / (S.g : ℝ) : ℝ) : ℂ)

/- English proof (translation)
Unfold `G.psi KB.psiL betaL`. Use `congr 1`. Rewrite using `[Complex.re_ofReal_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (betaL S) (σ * z) = KB.psiL S σ z := by
  unfold G.psi KB.psiL betaL
  congr 1
  rw [Complex.re_ofReal_mul]
  push_cast
  ring

/- English proof (translation)
Establish `h : G.psi (-betaL S) (σ * z) = G.psi (betaL S) (-σ * z)`. Unfold `G.psi`. Rewrite using `[show -betaL S * (σ * z) = betaL S * (-σ * z) by ring]`. Rewrite using `[h, psi_betaL]`.
-/
theorem psi_neg_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (-betaL S) (σ * z) = KB.psiL S (-σ) z := by
  have h : G.psi (-betaL S) (σ * z) = G.psi (betaL S) (-σ * z) := by
    unfold G.psi
    rw [show -betaL S * (σ * z) = betaL S * (-σ * z) by ring]
  rw [h, psi_betaL]

/- English proof (translation)
Establish `hg0 : 0 < S.g` using `Nat.mul_pos hg1 hg2`. Establish `hg : (0 : ℝ) < (S.g : ℝ)` using `by exact_mod_cast hg0`. Unfold `betaL`. Conclude with `Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hg.ne')`.
-/
theorem betaL_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : betaL S ≠ 0 := by
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold betaL
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hg.ne')

end loc

end

end Formalism.FourierDecayAlt.P.GermRealisation
