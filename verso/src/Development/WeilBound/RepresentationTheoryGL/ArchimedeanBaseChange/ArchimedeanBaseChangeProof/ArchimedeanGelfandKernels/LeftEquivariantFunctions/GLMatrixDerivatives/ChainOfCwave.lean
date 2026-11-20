import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCwaveB

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.RCalc (isOpen_GLs differentiableAt_of_smooth)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((g q.1 : ℂ)))` using `Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)`. Conclude with `h1.contDiffOn.smul hu.1`. Introduce `t x ht`. Simplify using `[hg.2.2 t ht]`.
-/
private theorem good_smul_bump_of_isWave {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u)
    (g : ℝ → ℝ) (T : ℝ) (hg : IsBump g T) :
    Good (GLs n) (fun q : ℝ × Mat n => ((g q.1 : ℂ)) • u q.1 q.2) T := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((g q.1 : ℂ))) :=
      Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)
    exact h1.contDiffOn.smul hu.1
  · intro t x ht
    simp [hg.2.2 t ht]

/- English proof (translation)
Introduce `n E u hu g T hg`. Establish `hG` using `good_smul_bump_of_isWave E u hu g T hg`. Use `⟨good_smooth isOpen_GLs _ T hG, ?_⟩` and prove the remaining obligations. Introduce `X x hx`. Unfold `Rd`.

Use `(good_fderiv_apply isOpen_GLs hG hx (x * X)).trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `t`. Establish `hd : DifferentiableAt ℝ (u t) x`. Apply `differentiableAt_of_smooth _ hx` to reduce the goal to its premises.

Establish `h2 : ContDiffOn ℝ ∞ (fun y : Mat n => Function.uncurry u (t, y)) (GLs n)` using `hu.1.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨mem_univ _, hy⟩)`. Conclude with `h2`. Establish `hf : fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x = ((g t : ℂ)) • fderiv ℝ (u t) x` using `(hd.hasFDerivAt.const_smul ((g t : ℂ))).fderiv`. Use `show (fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x) (x * X) = _`. Rewrite using `[hf]`.

Both sides reduce to the same expression.
-/
theorem paramInt : ParamInt := by
  intro n E u hu g T hg
  have hG := good_smul_bump_of_isWave E u hu g T hg
  refine ⟨good_smooth isOpen_GLs _ T hG, ?_⟩
  intro X x hx
  unfold Rd
  refine (good_fderiv_apply isOpen_GLs hG hx (x * X)).trans ?_
  congr 1
  funext t
  have hd : DifferentiableAt ℝ (u t) x := by
    apply differentiableAt_of_smooth _ hx
    have h2 : ContDiffOn ℝ ∞ (fun y : Mat n => Function.uncurry u (t, y)) (GLs n) :=
      hu.1.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨mem_univ _, hy⟩)
    exact h2
  have hf : fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x = ((g t : ℂ)) • fderiv ℝ (u t) x :=
    (hd.hasFDerivAt.const_smul ((g t : ℂ))).fderiv
  show (fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x) (x * X) = _
  rw [hf]
  rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
