import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAwayA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DecH

/- English proof (translation)
Introduce `D n θ τ ι hθ hι g`. Take `⟨-, hιy⟩` from `hι`. Establish `hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * (Jst D n).map (incA D) * mat g = (Jst D n).map (incA D)` using `g.2`. Use `set Y := compAt θ τ (mat g) with hYdef`. Establish `hY : Yᴴ * reidx (JJ n) * Y = reidx (JJ n)`.

Use `congrArg (compAt θ τ) hg` as an intermediate fact. Rewrite `this` using `[DA.compAt_mul, DA.compAt_mul, DA.compAt_conjT θ hθ, DA.compAt_Jst θ hθ]`. Then use the resulting hypothesis. Establish `hinv : compAt θ τ (mat g⁻¹) * Y = 1`. Rewrite using `[hYdef, ← DA.compAt_mul, ← DA.mat_mul, inv_mul_cancel, DA.mat_one, DA.compAt_one]`. Establish `hYu : IsUnit Y.det` using `Matrix.isUnit_det_of_left_inverse hinv`.

Use `set M : M2 n := Y.submatrix finSumFinEquiv finSumFinEquiv with hMdef`. Establish `hMY : reidx M = Y` using `by ext i j; simp [reidx, hMdef]`. Establish `hMG : InG M`. Establish `h2 : JJ n = (reidx (JJ n)).submatrix finSumFinEquiv finSumFinEquiv` using `by ext i j; simp [reidx]`. Unfold `InG`.

Rewrite using `[h2, hMdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hY]`. Establish `hMu : IsUnit M.det` using `by rw [hMdef, det_submatrix_equiv_self]; exact hYu`. Use `set y := mkGR M hMu hMG with hydef`. Establish `hιY : compAt θ τ (mat (ι y)) = Y` using `by rw [(hιy y).1, hydef, mR_mkGR, hMY]`. Establish `htriv : compAt θ τ (mat (g * (ι y)⁻¹)) = 1`.

Establish `h3 : compAt θ τ (mat (g * (ι y)⁻¹)) * Y = Y`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]`. Use `_ = 1 := by rw [h3, Matrix.mul_nonsing_inv _ hYu]`.

Use `⟨g * (ι y)⁻¹, y, htriv, by group, ?_⟩` and prove the remaining obligations. Generalize the expression as in `g * (ι y)⁻¹ = x at htriv ⊢`. Introduce `y'`. Apply `DA.mat_inj` to reduce the goal to its premises. Rewrite using `[DA.mat_mul, DA.mat_mul]`.

Apply `GlobalTheory.StabAtPlace.mx_ext hθ` to reduce the goal to its premises. Rewrite using `[DA.finMap_mul, DA.finMap_mul, (hιy y').2.2, Matrix.mul_one, Matrix.one_mul]`. Introduce `τ'`. Rewrite using `[DA.compAt_mul, DA.compAt_mul]`. Distinguish the cases in `h : τ' = τ`.

Substitute `h` using the available equality. Rewrite using `[htriv, Matrix.mul_one, Matrix.one_mul]`. Rewrite using `[(hιy y').2.1 τ' h, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem decompAway : DecompAway := by
  intro D n θ τ ι hθ hι g
  obtain ⟨-, hιy⟩ := hι
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * (Jst D n).map (incA D) * mat g =
      (Jst D n).map (incA D) := g.2
  set Y := compAt θ τ (mat g) with hYdef
  have hY : Yᴴ * reidx (JJ n) * Y = reidx (JJ n) := by
    have := congrArg (compAt θ τ) hg
    rwa [DA.compAt_mul, DA.compAt_mul, DA.compAt_conjT θ hθ, DA.compAt_Jst θ hθ] at this
  have hinv : compAt θ τ (mat g⁻¹) * Y = 1 := by
    rw [hYdef, ← DA.compAt_mul, ← DA.mat_mul, inv_mul_cancel, DA.mat_one, DA.compAt_one]
  have hYu : IsUnit Y.det := Matrix.isUnit_det_of_left_inverse hinv
  set M : M2 n := Y.submatrix finSumFinEquiv finSumFinEquiv with hMdef
  have hMY : reidx M = Y := by ext i j; simp [reidx, hMdef]
  have hMG : InG M := by
    have h2 : JJ n = (reidx (JJ n)).submatrix finSumFinEquiv finSumFinEquiv := by ext i j; simp [reidx]
    unfold InG
    rw [h2, hMdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hY]
  have hMu : IsUnit M.det := by rw [hMdef, det_submatrix_equiv_self]; exact hYu
  set y := mkGR M hMu hMG with hydef
  have hιY : compAt θ τ (mat (ι y)) = Y := by rw [(hιy y).1, hydef, mR_mkGR, hMY]
  have htriv : compAt θ τ (mat (g * (ι y)⁻¹)) = 1 := by
    have h3 : compAt θ τ (mat (g * (ι y)⁻¹)) * Y = Y := by
      calc compAt θ τ (mat (g * (ι y)⁻¹)) * Y = compAt θ τ (mat (g * (ι y)⁻¹)) * compAt θ τ (mat (ι y)) := by rw [hιY]
        _ = compAt θ τ (mat (g * (ι y)⁻¹ * ι y)) := by rw [DA.mat_mul (g * (ι y)⁻¹) (ι y), DA.compAt_mul]
        _ = Y := by rw [inv_mul_cancel_right]
    calc compAt θ τ (mat (g * (ι y)⁻¹)) = compAt θ τ (mat (g * (ι y)⁻¹)) * Y * Y⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
      _ = 1 := by rw [h3, Matrix.mul_nonsing_inv _ hYu]
  refine ⟨g * (ι y)⁻¹, y, htriv, by group, ?_⟩
  generalize g * (ι y)⁻¹ = x at htriv ⊢
  intro y'
  apply DA.mat_inj
  rw [DA.mat_mul, DA.mat_mul]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [DA.finMap_mul, DA.finMap_mul, (hιy y').2.2, Matrix.mul_one, Matrix.one_mul]
  · intro τ'
    rw [DA.compAt_mul, DA.compAt_mul]
    by_cases h : τ' = τ
    · subst h
      rw [htriv, Matrix.mul_one, Matrix.one_mul]
    · rw [(hιy y').2.1 τ' h, Matrix.mul_one, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
