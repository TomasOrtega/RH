import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

/- English proof (translation)
Use `continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => ?_` and prove the remaining obligations. Use `show ContinuousAt (fun c => w1 k r l c p q) c`. Simplify using `only [w1]`. Use `split_ifs`. Conclude with `continuousAt_id`.

Conclude with `(continuous_star.continuousAt).inv₀ (star_ne_zero.mpr hc)`. Conclude with `continuousAt_const`. Conclude with `continuousAt_const`.
-/
private theorem continuousAt_w1_of_ne_zero (k r : ℕ) (l : Fin r) {c : ℂ} (hc : c ≠ 0) :
    ContinuousAt (w1 k r l) c := by
  refine continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => ?_
  show ContinuousAt (fun c => w1 k r l c p q) c
  simp only [w1]
  split_ifs
  · exact continuousAt_id
  · exact (continuous_star.continuousAt).inv₀ (star_ne_zero.mpr hc)
  · exact continuousAt_const
  · exact continuousAt_const
/- English proof (translation)
Proceed by induction on `i using Fin.induction with`. Consider the case `zero`. Simplify using `only [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]`. Conclude with `continuousAt_const`. Consider the case `succ l ih`.

Simplify using `only [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]`. Use `ih.mul ?_` and prove the remaining obligations. Establish `hf : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => y.1 l) x` using `by fun_prop`. Conclude with `(continuousAt_w1_of_ne_zero k r l (hx l)).comp (f := fun y : (Fin r → ℂ) × Mx k r => y.1 l) hf`.
-/
private theorem continuousAt_wCell_fst_of_mem_OmX (k r : ℕ) (x : (Fin r → ℂ) × Mx k r) (hx : x.1 ∈ OmX r)
    (i : Fin (r + 1)) : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => wCell k r i y.1) x := by
  induction i using Fin.induction with
  | zero =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact continuousAt_const
  | succ l ih =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    refine ih.mul ?_
    have hf : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => y.1 l) x := by fun_prop
    exact (continuousAt_w1_of_ne_zero k r l (hx l)).comp (f := fun y : (Fin r → ℂ) × Mx k r => y.1 l) hf

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D`. Establish `hmem : ∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z'`. Introduce `x hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Formalism.FourierDecayAlt.P.TLB.wCell_gv (Pa := M.Par.mk k r 0 0 0 0) D hx`.

Conclude with `Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2`. Use `⟨hmem, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Conclude with `(continuousAt_wCell_fst_of_mem_OmX k r x hx.1 (Fin.last r)).mul continuous_snd.continuousAt`.

Introduce `g hg`. Conclude with `⟨hg.1, hg.2.2⟩`.
-/
theorem spectral_pairing_big_cell : RDSPEOm := by
  intro k r Wp Wq _ _ _ _ _ _ D
  have hmem : ∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact Formalism.FourierDecayAlt.P.TLB.wCell_gv (Pa := M.Par.mk k r 0 0 0 0) D hx
    · exact Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  refine ⟨hmem, ?_, ?_⟩
  · intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_wCell_fst_of_mem_OmX k r x hx.1 (Fin.last r)).mul continuous_snd.continuousAt
  · intro g hg
    exact ⟨hg.1, hg.2.2⟩

end Formalism.FourierDecayAlt.P.CutSE
