import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EPerpMid

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

/- English proof (translation)
Take `⟨h1, h2, hH, hef⟩` from `C.isT τ`. Conclude with `⟨h1, h2, hH, fun a => (hef a a rfl).1, fun a => (hef a a rfl).2⟩`.
-/
theorem trHyp_C (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (PtRepPf.frU X u (vOf X τ)) (C.Q τ) (C.Qi τ)
      (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) := by
  obtain ⟨h1, h2, hH, hef⟩ := C.isT τ
  exact ⟨h1, h2, hH, fun a => (hef a a rfl).1, fun a => (hef a a rfl).2⟩

/- English proof (translation)
Take `⟨v⟩ : Nonempty (InfinitePlace X.B.I.F)` from `inferInstance`. Establish `h` using `(PtRepPf.frU X (Classical.arbitrary D.what₂.Word) v).card`. Use linear arithmetic over natural numbers and integers.
-/
theorem n_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have h := (PtRepPf.frU X (Classical.arbitrary D.what₂.Word) v).card
  omega

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `C.isT τ`. Unfold `trG`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem trG_mul_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := by
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  unfold trG
  calc C.Qi τ * uMat γ * C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ)
      = C.Qi τ * uMat γ * (C.Q τ * C.Qi τ) * uMat γ⁻¹ * C.Q τ := by simp only [Matrix.mul_assoc]
    _ = C.Qi τ * (uMat γ * uMat γ⁻¹) * C.Q τ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul_inv, Matrix.mul_one, h1]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (trG_mul_inv C τ γ)`.
-/
theorem trG_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (trG (C.Q τ) (C.Qi τ) γ)⁻¹ = trG (C.Q τ) (C.Qi τ) γ⁻¹ :=
  Matrix.inv_eq_right_inv (trG_mul_inv C τ γ)

/- English proof (translation)
Take `⟨-, h2, -, -⟩` from `C.isT τ`. Unfold `trG`. Rewrite using `[Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem trG_mul (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) (a * b) = trG (C.Q τ) (C.Qi τ) a * trG (C.Q τ) (C.Qi τ) b := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc C.Qi τ * (uMat a * uMat b) * C.Q τ = C.Qi τ * uMat a * (C.Q τ * C.Qi τ) * uMat b * C.Q τ := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `γ μRv hH`. Take `⟨hσ, hne, hconc, hinv⟩` from `hH`. Take `⟨h1, h2, -, -⟩` from `C.isT τ`. Establish `hT` using `trHyp_C C u τ`. Establish `hT'` using `trHyp_C C u' τ`.

Use `set f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS := fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hf`. Establish `hemb : Topology.IsClosedEmbedding f` using `Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2`. Establish `hme : MeasurableEmbedding f` using `hemb.measurableEmbedding`. Establish `hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))` using `fun y => y.2`. Establish `hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ, trG (C.Q τ) (C.Qi τ) y ∈ RStab D.R.k D.R.rS (gB C τ γ)`.

Introduce and unpack `y ⟨hy1, hy2⟩`. Use `⟨Formalism.L2.SG.Pf.Bridge.fwd_N hT (hU y) hy1, ?_⟩` and prove the remaining obligations. Use `show (trG (C.Q τ) (C.Qi τ) γ)⁻¹ * trG (C.Q τ) (C.Qi τ) y * trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS`. Rewrite using `[trG_inv, ← trG_mul, ← trG_mul]`. Conclude with `Formalism.L2.SG.Pf.Bridge.fwd_N hT' (hU _) hy2`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hσ`. Conclude with `hme.sigmaFinite_map`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `h` using `congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0`. Simplify using `only [Measure.coe_zero, Pi.zero_apply] at h`. Rewrite `h` using `[hme.map_apply, Set.preimage_univ]`. Conclude with `Measure.measure_univ_eq_zero.1 h`. Rewrite using `[hme.map_apply]`.

Use `measure_mono_null (fun y hy => ?_) hconc` and prove the remaining obligations. Introduce `hyS`. Conclude with `hy (hfwd y hyS)`. Introduce `s hs`. Take `⟨hsN, hsN'⟩` from `hs`.

Establish `hmem` using `Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hsN.1`. Use `set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * s * C.Qi τ) hmem with hy0`. Establish `hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ`. Use `⟨Formalism.L2.SG.Pf.Bridge.inN_Q hT hsN, ?_⟩` and prove the remaining obligations. Use `show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))`.

Establish `e : uMat (γ⁻¹ * y0 * γ) = C.Q τ * ((gB C τ γ)⁻¹ * s * gB C τ γ) * C.Qi τ`. Rewrite using `[trG_inv]`. Use `show uMat (γ⁻¹ * y0 * γ) = C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ * s * (C.Qi τ * uMat γ * C.Q τ)) * C.Qi τ`. Rewrite using `[Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]`. Use `show uMat γ⁻¹ * (C.Q τ * s * C.Qi τ) * uMat γ = _`.

Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[h2, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h2, Matrix.mul_one]`. Rewrite using `[e]`.

Conclude with `Formalism.L2.SG.Pf.Bridge.inN_Q hT' hsN'`. Establish `hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ f = f ∘ (fun x => y0 * x)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, hf, Formalism.QuantumDeterminants.lmulM, Matrix.of_symm_apply]`. Rewrite using `[trG_mul]`.

Use `congr 1`. Use `show s = C.Qi τ * (C.Q τ * s * C.Qi τ) * C.Q τ`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]`. Establish `hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k` using `D.R.k) (r := D.R.rS) s) := by`.

Establish `: Continuous (Formalism.QuantumDeterminants.lmulM (k` using `D.R.k) (r := D.R.rS) s) := by`. Unfold `Formalism.QuantumDeterminants.lmulM`. Conclude with `continuous_const.matrix_mul continuous_id`. Conclude with `this.measurable`. Rewrite using `[Measure.map_map hcont_l hme.measurable, hcomp, ← Measure.map_map hme.measurable (continuous_mul_left y0).measurable, hinv y0 hy0S]`.
-/
theorem haarTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarTr C u u' τ := by
  intro γ μRv hH
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hT := trHyp_C C u τ
  have hT' := trHyp_C C u' τ
  set f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hf
  have hemb : Topology.IsClosedEmbedding f := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hme : MeasurableEmbedding f := hemb.measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := fun y => y.2

  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ, trG (C.Q τ) (C.Qi τ) y ∈ RStab D.R.k D.R.rS (gB C τ γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hT (hU y) hy1, ?_⟩
    show (trG (C.Q τ) (C.Qi τ) γ)⁻¹ * trG (C.Q τ) (C.Qi τ) y * trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS
    rw [trG_inv, ← trG_mul, ← trG_mul]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hT' (hU _) hy2
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI := hσ; exact hme.sigmaFinite_map
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * s * C.Qi τ) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
        (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hT hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = C.Q τ * ((gB C τ γ)⁻¹ * s * gB C τ γ) * C.Qi τ := by
        rw [trG_inv]
        show uMat (γ⁻¹ * y0 * γ) = C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ * s * (C.Qi τ * uMat γ * C.Q τ)) * C.Qi τ
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (C.Q τ * s * C.Qi τ) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hT' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ f = f ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hf, Formalism.QuantumDeterminants.lmulM, Matrix.of_symm_apply]
      rw [trG_mul]
      congr 1
      show s = C.Qi τ * (C.Q τ * s * C.Qi τ) * C.Q τ
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_mul_left y0).measurable, hinv y0 hy0S]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
