import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

open NumberField in

/- English proof (translation)
The claim follows from `(_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_herm τ G u v).symm`.
-/
theorem _root_.GlobalTheory.hermC_emb_eq_map_herm {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) = τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm G u v) :=
  (_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_herm τ G u v).symm

open NumberField in

/- English proof (translation)
Establish `h` using `congrArg τ X.ξ0_im`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h`. Rewrite `h` using `[NumberField.IsCMField.complexEmbedding_complexConj, map_neg]`. Establish `h2` using `congrArg Complex.re h`. Simplify using `only [Complex.conj_re, Complex.neg_re] at h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.re_map_xi_eq_zero {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : E →+* ℂ) : (τ X.ξ0).re = 0 := by
  have h := congrArg τ X.ξ0_im
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at h2
  linarith

open NumberField in

/- English proof (translation)
Establish `hre` using `_root_.GlobalTheory.re_map_xi_eq_zero X τ.1`. Establish `hz : τ.1 X.ξ0 = ((τ.1 X.ξ0).im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c`. Use `conv_lhs => rw [hz]`.

Simplify using `[Complex.norm_real]`.
-/
theorem _root_.GlobalTheory.c_eq_two_mul_abs_im {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : X.c τ = 2 * |(τ.1 X.ξ0).im| := by
  have hre := _root_.GlobalTheory.re_map_xi_eq_zero X τ.1
  have hz : τ.1 X.ξ0 = ((τ.1 X.ξ0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c
  conv_lhs => rw [hz]
  simp [Complex.norm_real]

end GlobalTheory
