import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT in
open scoped ComplexOrder in

/- English proof (translation)
Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h1 : M.fr τ * (M.fr τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `h2 : (M.fr τ)⁻¹ * M.fr τ = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1`. Unfold `Formalism.REAL.Jm`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext a; split_ifs <;> simp`. Establish `hJ' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ)`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`.

Apply the tactic sequence `congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp`. Establish `hG : gramAt D V τ * cart M τ = (M.fr τ)ᴴ * M.fr τ`. Rewrite using `[← M.fr_gram τ]`. Unfold `cart`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]`. Establish `hs : cart M τ * cart M τ = 1`. Unfold `cart`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]`. Use `⟨hs, ?_, ?_⟩` and prove the remaining obligations. Establish `hGh : (gramAt D V τ)ᴴ = gramAt D V τ`. Rewrite using `[← M.fr_gram τ]`.

Simplify using `[Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]`. Establish `h3 : (cart M τ)ᴴ * gramAt D V τ = gramAt D V τ * cart M τ`. Use `congrArg Matrix.conjTranspose hG` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Rewrite using `[this, hG]`.

Rewrite using `[h3, Matrix.mul_assoc, hs, Matrix.mul_one]`. Rewrite using `[hG]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (M.fr_unit τ))`.
-/
theorem isCartanInv_cart_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hu
  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have hJ' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  have hG : gramAt D V τ * cart M τ = (M.fr τ)ᴴ * M.fr τ := by
    rw [← M.fr_gram τ]; unfold cart
    calc _ = (M.fr τ)ᴴ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : cart M τ * cart M τ = 1 := by
    unfold cart
    calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← M.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (cart M τ)ᴴ * gramAt D V τ = gramAt D V τ * cart M τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (M.fr_unit τ))

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT in

/- English proof (translation)
Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h1 : M.fr τ * (M.fr τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Rewrite using `[← M.fr_gram τ]`. Unfold `onb`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [h1]; simp`.
-/
theorem onb_gram_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm (M.ε τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  rw [← M.fr_gram τ]; unfold onb
  calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.transpose_apply, map_neg, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_neg_transpose_diag {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ (-Gᵀ) x c c = -(xᴴ * G.map τ * x) c c := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.neg_apply,
    Matrix.transpose_apply, map_neg, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [RCLike.star_def]
  ring

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT in

/- English proof (translation)
Introduce `D W S M x₀ hx ρ`. Use `⟨isCartanInv_cart_model M ρ, fun X hW hO hρ => ?_⟩` and prove the remaining obligations. Establish `e : x₀ (tauE D ρ) = x0Mat M ρ` using `hx ρ`. Establish `hG : X.Gm = -(W.gram)ᵀ` using `hW.1`. Establish `hs : ∀ c : Fin W.rank, ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (c : ℕ) : ℝ) : ℂ) = -(if M.ε ρ (arr (nNeg (M.ε ρ)) c) then 1 else -1)`.

Introduce `c`. Establish `h1` using `congrFun (congrFun (hO _ hρ) c) c`. Rewrite `h1` using `[hG, gram_neg_transpose_diag, Matrix.diagonal_apply_eq, e]`. Establish `h2` using `congrFun (congrFun (onb_gram_model M ρ) (arr (nNeg (M.ε ρ)) c)) (arr (nNeg (M.ε ρ)) c)`. Rewrite `h2` using `[Formalism.REAL.Jm, Matrix.diagonal_apply_eq]`.

Rewrite using `[← h1, ← h2]`. Both sides reduce to the same expression. Rewrite using `[e, cart, Formalism.REAL.Jm, torus_x0Mat]`. Use extensionality with `a c`. Simplify using `only [sgnM, Matrix.neg_apply, mul_diagonal, hs]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cart_mul_baseFrame : ∀ (D : D7) (W : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel W S) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ), Formalism.IndefR.FWT.IsModelBaseFrameFamily M rfl x₀ → ∀ ρ, IsCartanInv (gramAt D W ρ) (Formalism.IndefR.Links.cart M ρ) ∧ ∀ X : Data D.host.E W.rank, ModelW W rfl X → IsOrthogonalFrame X x₀ → tauE D ρ ∈ X.Ψ → Formalism.IndefR.Links.cart M ρ * x₀ (tauE D ρ) = -(x₀ (tauE D ρ) * sgnM X) := by
  intro D W S M x₀ hx ρ
  refine ⟨isCartanInv_cart_model M ρ, fun X hW hO hρ => ?_⟩
  have e : x₀ (tauE D ρ) = x0Mat M ρ := hx ρ
  have hG : X.Gm = -(W.gram)ᵀ := hW.1
  have hs : ∀ c : Fin W.rank, ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (c : ℕ) : ℝ) : ℂ) =
      -(if M.ε ρ (arr (nNeg (M.ε ρ)) c) then 1 else -1) := by
    intro c
    have h1 := congrFun (congrFun (hO _ hρ) c) c
    rw [hG, gram_neg_transpose_diag, Matrix.diagonal_apply_eq, e] at h1
    have h2 := congrFun (congrFun (onb_gram_model M ρ) (arr (nNeg (M.ε ρ)) c)) (arr (nNeg (M.ε ρ)) c)
    rw [Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at h2
    rw [← h1, ← h2]
    rfl
  rw [e, cart, Formalism.REAL.Jm, torus_x0Mat]
  ext a c
  simp only [sgnM, Matrix.neg_apply, mul_diagonal, hs]
  ring

end GlobalTheory.FrameEquiv
