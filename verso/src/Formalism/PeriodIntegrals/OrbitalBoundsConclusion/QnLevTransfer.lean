import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel

/- English proof (translation)
Use `open PIQnLT Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q in`. Introduce `hL E _ _ k i r' z z' Y p q f g hg`. Establish `hinv : (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹` using `ιLev_inv hL g (isUnit_det_of_UH g hg)`. Establish `hm` using `mdim_lev k i r'`. Establish `hP : ∀ j, posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast hm j))` using `posL_lev k i r'`.

Establish `hx : ∀ j, xv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j = xv k r' z' 0 (Fin.cast hm j)`. Introduce `j`. Simplify using `only [xv]`. Rewrite using `[fvec_lift, hP, liftVec_lev]`. Establish `hxb : ∀ j, xbv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j = xbv k r' z' 0 (Fin.cast hm j)`.

Introduce `j`. Simplify using `only [xbv]`. Rewrite using `[fvec_lift, hP, bvec_lev, herm_liftVec]`. Establish `hy : ∀ j, yv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j = yv k r' z 0 g (Fin.cast hm j)`. Introduce `j`.

Simplify using `only [yv]`. Rewrite using `[hinv, fvec_lift, mulVec_liftVec, hP, liftVec_lev]`. Establish `hyb : ∀ j, ybv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j = ybv k r' z 0 g (Fin.cast hm j)`. Introduce `j`. Simplify using `only [ybv]`.

Rewrite using `[fvec_lift, hP, bvec_lev, mulVec_liftVec, herm_liftVec]`. Establish `hu` using `uC_lev k i r' Y`. Apply the tactic sequence `fin_cases p <;> fin_cases q`. Simplify using `only [tL, capL]`. Rewrite using `[hu]`.

Conclude with `capL_cast hL hm _ _ hP _ f g`. Simplify using `only [tL, Pi.neg_apply]`. Rewrite using `[hu]`. Use `congr 1`. Conclude with `chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hx j) (fun j => hyb j)`.

Simplify using `only [tL, Pi.neg_apply]`. Rewrite using `[hu]`. Use `congr 1`. Conclude with `chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hy j) (fun j => hxb j)`. Simplify using `only [tL, Pi.neg_apply]`.

Rewrite using `[hu]`. Use `congr 1`. Conclude with `second_capelli_minor_cast hL hm _ _ hP _ _ _ _ _ _ _ _ _ f g (fun j => hy j) (fun j => hx j) (fun j => hyb j) (fun j => hxb j)`.
-/
theorem level_transfer_of_levHom : Formalism.QuantumDeterminants.LevHom → Formalism.FourierDecayAlt.Q.LevelTransfer := by
  open PIQnLT Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q in
  intro hL E _ _ k i r' z z' Y p q f g hg
  have hinv : (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹ := ιLev_inv hL g (isUnit_det_of_UH g hg)
  have hm := mdim_lev k i r'
  have hP : ∀ j, posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast hm j)) :=
    posL_lev k i r'
  have hx : ∀ j, xv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j = xv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xv]
    rw [fvec_lift, hP, liftVec_lev]
  have hxb : ∀ j, xbv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j =
      xbv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xbv]
    rw [fvec_lift, hP, bvec_lev, herm_liftVec]
  have hy : ∀ j, yv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      yv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [yv]
    rw [hinv, fvec_lift, mulVec_liftVec, hP, liftVec_lev]
  have hyb : ∀ j, ybv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      ybv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [ybv]
    rw [fvec_lift, hP, bvec_lev, mulVec_liftVec, herm_liftVec]
  have hu := uC_lev k i r' Y
  fin_cases p <;> fin_cases q
  · simp only [tL, capL]
    rw [hu]
    exact capL_cast hL hm _ _ hP _ f g
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hx j) (fun j => hyb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hy j) (fun j => hxb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact second_capelli_minor_cast hL hm _ _ hP _ _ _ _ _ _ _ _ _ f g (fun j => hy j) (fun j => hx j)
      (fun j => hyb j) (fun j => hxb j)
