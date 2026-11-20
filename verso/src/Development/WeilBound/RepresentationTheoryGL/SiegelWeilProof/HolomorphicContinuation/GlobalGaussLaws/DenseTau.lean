import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseC

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open Formalism.IndefR.Eqv (psiT thetaC)

/- English proof (translation)
Introduce `D n θ τ ι hθ hι y O hO hy`. Take `rfl` from `Formalism.IndefR.Eqv.eq_thetaC D hθ`. Establish `hcl` using `DenseP.gam_dense (D := D) DenseP.genSt τ y`. Take `⟨y', hy'O, γ, hγ, hγe⟩` from `mem_closure_iff.1 hcl O hO hy`. Establish `hc : ∀ τ' (w : Formalism.IndefR.Datum.Mx D (n + n) (n + n)), compAt (thetaC D) τ' w = w.map (psiT D τ')` using `fun _ _ => rfl`.

Establish `hy' : (mat (ι y')).map (psiT D τ) = Glob.reidx (mR y')` using `(hc τ _).symm.trans (hι.2 y').1`. Use `⟨γ, hγ, y', hy'O, γ * (ι y')⁻¹, by group, fun y'' => ?_⟩` and prove the remaining obligations. Establish `hR : (mat (γ * (ι y')⁻¹)).map (psiT D τ) = 1`. Establish `h1 : (mat γ).map (psiT D τ) = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (mat (ι y')).map (psiT D τ)`. Rewrite using `[← Matrix.map_mul, ← DenseP.mat_mul, inv_mul_cancel_right]`.

Rewrite `h1` using `[hγe, hy']`. Establish `h2 : Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹) = 1`. Rewrite using `[← DenseP.reidx_mul]`. Use `show Glob.reidx (mR (y' * y'⁻¹)) = 1`. Rewrite using `[mul_inv_cancel]`.

Conclude with `DenseP.reidx_one`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, Matrix.mul_one]`. Use `_ = 1 := by rw [← Matrix.mul_assoc, ← h1, h2]`. Generalize the expression as in `γ * (ι y')⁻¹ = x at hR ⊢`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show mat (x * ι y'') = mat (ι y'' * x)`. Rewrite using `[DenseP.mat_mul, DenseP.mat_mul]`. Apply `Formalism.IndefR.Eqv.mat_ext D` to reduce the goal to its premises.

Introduce `τ'`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Rewrite using `[hR]`.

Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Establish `h1 : (mat (ι y'')).map (psiT D τ') = 1` using `by rw [← hc]; exact (hι.2 y'').2.1 τ' h`. Rewrite using `[h1]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, (hι.2 y'').2.2]`.

Simplify using `only [Matrix.one_mul, Matrix.mul_one]`.
-/
theorem denseTau : DenseTau := by
  intro D n θ τ ι hθ hι y O hO hy
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hcl := DenseP.gam_dense (D := D) DenseP.genSt τ y
  obtain ⟨y', hy'O, γ, hγ, hγe⟩ := mem_closure_iff.1 hcl O hO hy
  have hc : ∀ τ' (w : Formalism.IndefR.Datum.Mx D (n + n) (n + n)), compAt (thetaC D) τ' w = w.map (psiT D τ') :=
    fun _ _ => rfl
  have hy' : (mat (ι y')).map (psiT D τ) = Glob.reidx (mR y') := (hc τ _).symm.trans (hι.2 y').1
  refine ⟨γ, hγ, y', hy'O, γ * (ι y')⁻¹, by group, fun y'' => ?_⟩
  have hR : (mat (γ * (ι y')⁻¹)).map (psiT D τ) = 1 := by
    have h1 : (mat γ).map (psiT D τ) = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (mat (ι y')).map (psiT D τ) := by
      rw [← Matrix.map_mul, ← DenseP.mat_mul, inv_mul_cancel_right]
    rw [hγe, hy'] at h1
    have h2 : Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹) = 1 := by
      rw [← DenseP.reidx_mul]
      show Glob.reidx (mR (y' * y'⁻¹)) = 1
      rw [mul_inv_cancel]; exact DenseP.reidx_one
    calc (mat (γ * (ι y')⁻¹)).map (psiT D τ)
        = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.mul_assoc, ← h1, h2]
  generalize γ * (ι y')⁻¹ = x at hR ⊢
  apply Subtype.ext
  apply Units.ext
  show mat (x * ι y'') = mat (ι y'' * x)
  rw [DenseP.mat_mul, DenseP.mat_mul]
  apply Formalism.IndefR.Eqv.mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases h : τ' = τ
    · subst h; rw [hR]; simp only [Matrix.one_mul, Matrix.mul_one]
    · have h1 : (mat (ι y'')).map (psiT D τ') = 1 := by rw [← hc]; exact (hι.2 y'').2.1 τ' h
      rw [h1]; simp only [Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 y'').2.2]; simp only [Matrix.one_mul, Matrix.mul_one]

end PositivityTheory.Rg.Sw.Glob
