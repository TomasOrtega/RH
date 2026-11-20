import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodQuadraticFormsSmooth
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.SuperconnSmooth

section Generic

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : Set X}

/- English proof (translation)
Use `contDiffOn_pi.2 fun S => ?_` and prove the remaining obligations. Distinguish the cases in `hS : i ∈ S`. Simplify using `only [wedge, hS, if_true]`. Conclude with `contDiffOn_const.mul (contDiffOn_pi.1 hF _)`. Simplify using `only [wedge, hS, if_false]`.

Conclude with `contDiffOn_const`.
-/
theorem wedge_cd {m : ℕ} (i : Fin m) {F : X → Ext m} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun P => wedge i (F P)) U := by
  refine contDiffOn_pi.2 fun S => ?_
  by_cases hS : i ∈ S
  · simp only [wedge, hS, if_true]
    exact contDiffOn_const.mul (contDiffOn_pi.1 hF _)
  · simp only [wedge, hS, if_false]
    exact contDiffOn_const

/- English proof (translation)
Use `contDiffOn_pi.2 fun S => ?_` and prove the remaining obligations. Distinguish the cases in `hS : i ∈ S`. Simplify using `only [contr, hS, if_true]`. Conclude with `contDiffOn_const`. Simplify using `only [contr, hS, if_false]`.

Conclude with `contDiffOn_const.mul (contDiffOn_pi.1 hF _)`.
-/
theorem contr_cd {m : ℕ} (i : Fin m) {F : X → Ext m} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun P => contr i (F P)) U := by
  refine contDiffOn_pi.2 fun S => ?_
  by_cases hS : i ∈ S
  · simp only [contr, hS, if_true]
    exact contDiffOn_const
  · simp only [contr, hS, if_false]
    exact contDiffOn_const.mul (contDiffOn_pi.1 hF _)

end Generic

section Deriv

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {U : Set V}

/- English proof (translation)
Establish `hdf : ContDiffOn ℝ ∞ (fun P => fderiv ℝ f P) U` using `hf.fderiv_of_isOpen (m := ∞) hU (by simp)`. Unfold `d01`. Conclude with `(contDiffOn_const (c := (1 / 2 : ℂ))).smul ((hdf.clm_apply hv).add ((contDiffOn_const (c := Complex.I)).smul (hdf.clm_apply ((contDiffOn_const (c := Complex.I)).smul hv))))`.
-/
theorem dbar_contDiffOn (hU : IsOpen U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) {v : V → V}
    (hv : ContDiffOn ℝ ∞ v U) : ContDiffOn ℝ ∞ (fun P => d01 f P (v P)) U := by
  have hdf : ContDiffOn ℝ ∞ (fun P => fderiv ℝ f P) U := hf.fderiv_of_isOpen (m := ∞) hU (by simp)
  unfold d01
  exact (contDiffOn_const (c := (1 / 2 : ℂ))).smul ((hdf.clm_apply hv).add
    ((contDiffOn_const (c := Complex.I)).smul
      (hdf.clm_apply ((contDiffOn_const (c := Complex.I)).smul hv))))

/- English proof (translation)
Establish `hdf : ContDiffOn ℝ ∞ (fun P => fderiv ℝ f P) U` using `hf.fderiv_of_isOpen (m := ∞) hU (by simp)`. Unfold `d10`. Conclude with `(contDiffOn_const (c := (1 / 2 : ℂ))).smul ((hdf.clm_apply hv).sub ((contDiffOn_const (c := Complex.I)).smul (hdf.clm_apply ((contDiffOn_const (c := Complex.I)).smul hv))))`.
-/
theorem dholo_contDiffOn (hU : IsOpen U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) {v : V → V}
    (hv : ContDiffOn ℝ ∞ v U) : ContDiffOn ℝ ∞ (fun P => d10 f P (v P)) U := by
  have hdf : ContDiffOn ℝ ∞ (fun P => fderiv ℝ f P) U := hf.fderiv_of_isOpen (m := ∞) hU (by simp)
  unfold d10
  exact (contDiffOn_const (c := (1 / 2 : ℂ))).smul ((hdf.clm_apply hv).sub
    ((contDiffOn_const (c := Complex.I)).smul
      (hdf.clm_apply ((contDiffOn_const (c := Complex.I)).smul hv))))

end Deriv

end GlobalTheory.TorsionForm.SuperconnSmooth

namespace GlobalTheory.TorsionForm.SuperconnSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ}
  {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}

/- English proof (translation)
The claim follows from `hτ.1.prod isOpen_univ`.
-/
theorem isOpen_cov (hτ : IsPeriodMap B τ) : IsOpen (cov B g) := hτ.1.prod isOpen_univ

/- English proof (translation)
Establish `hd : ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) P.1` using `fun i j => (hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hP.1)`. Establish `hF : HasFDerivAt (fun b => per (τ b) (flat τ P)) (ContinuousLinearMap.pi fun i => ∑ j, (flat τ P (Sum.inl j) : ℂ) • fderiv ℂ (fun b => τ b j i) P.1) P.1`. Use `hasFDerivAt_pi.2 fun i => ?_` and prove the remaining obligations. Use `(HasFDerivAt.sum (u := Finset.univ) fun j _ => ((hd j i).hasFDerivAt.const_mul (flat τ P (Sum.inl j) : ℂ))).add_const (flat τ P (Sum.inr i) : ℂ)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `w`. Simplify using `[per, Matrix.vecMul, dotProduct]`. Simplify using `only [hor, hF.fderiv]`. Use extensionality with `i`. Both sides reduce to the same expression.

Simplify using the standard rewrite rules.
-/
theorem hor_eq (hτ : IsPeriodMap B τ) {P : Pt E g} (hP : P ∈ cov B g) (v : E) :
    hor τ P v = (v, fun i => ∑ j, (flat τ P (Sum.inl j) : ℂ) * fderiv ℂ (fun b => τ b j i) P.1 v) := by
  have hd : ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) P.1 := fun i j =>
    (hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hP.1)
  have hF : HasFDerivAt (fun b => per (τ b) (flat τ P))
      (ContinuousLinearMap.pi fun i => ∑ j, (flat τ P (Sum.inl j) : ℂ) • fderiv ℂ (fun b => τ b j i) P.1)
      P.1 := by
    refine hasFDerivAt_pi.2 fun i => ?_
    have := (HasFDerivAt.sum (u := Finset.univ) fun j _ =>
      ((hd j i).hasFDerivAt.const_mul (flat τ P (Sum.inl j) : ℂ))).add_const (flat τ P (Sum.inr i) : ℂ)
    convert this using 1
    · ext w
      simp [per, Matrix.vecMul, dotProduct]
  simp only [hor, hF.fderiv]
  ext i
  · rfl
  · simp

/- English proof (translation)
Establish `h1 : ContDiffOn ℂ ∞ (fun b => τ b i j) B` using `(GlobalTheory.ThetaMetSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn`. Establish `h2 : ContDiffOn ℂ ∞ (fun b => fderiv ℂ (fun b => τ b i j) b v) B` using `(h1.fderiv_of_isOpen (m := ∞) hτ.1 (by simp)).clm_apply contDiffOn_const`. Conclude with `(h2.restrict_scalars ℝ).comp contDiff_fst.contDiffOn fun P hP => hP.1`.
-/
theorem dtau_cd (hτ : IsPeriodMap B τ) (i j : Fin g) (v : E) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => fderiv ℂ (fun b => τ b i j) P.1 v) (cov B g) := by
  have h1 : ContDiffOn ℂ ∞ (fun b => τ b i j) B :=
    (GlobalTheory.ThetaMetSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn
      hτ.1.uniqueDiffOn
  have h2 : ContDiffOn ℂ ∞ (fun b => fderiv ℂ (fun b => τ b i j) b v) B :=
    (h1.fderiv_of_isOpen (m := ∞) hτ.1 (by simp)).clm_apply contDiffOn_const
  exact (h2.restrict_scalars ℝ).comp contDiff_fst.contDiffOn fun P hP => hP.1

/- English proof (translation)
Establish `hflat` using `(GlobalTheory.ThetaMetSmooth.smooth_main hτ).1`. Use `ContDiffOn.congr (f := fun P : Pt E g => (v, fun i => ∑ j, (flat τ P (Sum.inl j) : ℂ) * fderiv ℂ (fun b => τ b j i) P.1 v)) ?_ fun P hP => hor_eq hτ hP v` and prove the remaining obligations. Use `contDiffOn_const.prodMk (contDiffOn_pi.2 fun i => ContDiffOn.sum fun j _ => ?_)` and prove the remaining obligations. Conclude with `(Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.1 hflat (Sum.inl j))).mul (dtau_cd hτ j i v)`.
-/
theorem hor_cd (hτ : IsPeriodMap B τ) (v : E) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => hor τ P v) (cov B g) := by
  have hflat := (GlobalTheory.ThetaMetSmooth.smooth_main hτ).1
  refine ContDiffOn.congr (f := fun P : Pt E g =>
      (v, fun i => ∑ j, (flat τ P (Sum.inl j) : ℂ) * fderiv ℂ (fun b => τ b j i) P.1 v)) ?_
    fun P hP => hor_eq hτ hP v
  refine contDiffOn_const.prodMk (contDiffOn_pi.2 fun i => ContDiffOn.sum fun j _ => ?_)
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.1 hflat (Sum.inl j))).mul
    (dtau_cd hτ j i v)

end GlobalTheory.TorsionForm.SuperconnSmooth

namespace GlobalTheory.TorsionForm.SuperconnSmooth

/- English proof (translation)
Introduce `E _ _ _ g n B τ h β u s hτ hh hpos hs`. Establish `hU` using `isOpen_cov (g := g) hτ`. Establish `hlog : ContDiffOn ℝ ∞ (fun Q : Pt E g => (Real.log (h Q) : ℂ)) (cov B g)` using `Complex.ofRealCLM.contDiff.comp_contDiffOn (hh.log fun P hP => (hpos P hP).ne')`. Establish `hnab : ∀ {v : Pt E g → Pt E g}, ContDiffOn ℝ ∞ v (cov B g) → ContDiffOn ℝ ∞ (fun P => pointDifference h s P (v P)) (cov B g)` using `fun hv => (dholo_contDiffOn hU hs hv).add ((dholo_contDiffOn hU hlog hv).smul hs)`. Establish `hIm : ∀ a c, ContDiffOn ℝ ∞ (fun P : Pt E g => imPart τ P.1 a c) (cov B g)`.

Introduce `a c`. Use `Complex.ofRealCLM.contDiff.comp_contDiffOn (GlobalTheory.ThetaMetSmooth.im_smooth hτ a c)` as an intermediate fact. Simplify `this` using `[imPart, Function.comp_def]`. Establish `hnE : ContDiffOn ℝ ∞ (fun P => nablaE τ h β s P) (cov B g)`. Unfold `nablaE`.

Conclude with `ContDiffOn.sum fun i _ => (wedge_cd _ (hnab (hor_cd hτ (β i)))).add (wedge_cd _ ((dbar_contDiffOn hU hs (hor_cd hτ (β i))).add (GlobalTheory.TorsionForm.ConnSmooth.connForm_contDiffOn B τ s hτ hs (β i))))`. Establish `hdb : ContDiffOn ℝ ∞ (fun P => dbarV s P) (cov B g)`. Unfold `dbarV`. Conclude with `ContDiffOn.sum fun a _ => wedge_cd _ (dbar_contDiffOn hU hs contDiffOn_const)`. Establish `hda : ContDiffOn ℝ ∞ (fun P => dbarAdj τ h s P) (cov B g)`.

Unfold `dbarAdj`. Conclude with `(ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ => (contDiffOn_const.mul (hIm a c)).smul (contr_cd _ (hnab contDiffOn_const))).neg`. Unfold `superconn`. Conclude with `hnE.add ((contDiffOn_const (c := (Real.sqrt u : ℂ))).smul (hdb.add hda))`.
-/
theorem superconn_contDiffOn : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ)
    (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (s : Pt E g → Ext (n + n + g)),
    IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) →
    ContDiffOn ℝ ∞ s (cov B g) → ContDiffOn ℝ ∞ (superconn τ h β u s) (cov B g) := by
  intro E _ _ _ g n B τ h β u s hτ hh hpos hs
  have hU := isOpen_cov (g := g) hτ
  have hlog : ContDiffOn ℝ ∞ (fun Q : Pt E g => (Real.log (h Q) : ℂ)) (cov B g) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hh.log fun P hP => (hpos P hP).ne')
  have hnab : ∀ {v : Pt E g → Pt E g}, ContDiffOn ℝ ∞ v (cov B g) →
      ContDiffOn ℝ ∞ (fun P => pointDifference h s P (v P)) (cov B g) := fun hv =>
    (dholo_contDiffOn hU hs hv).add ((dholo_contDiffOn hU hlog hv).smul hs)
  have hIm : ∀ a c, ContDiffOn ℝ ∞ (fun P : Pt E g => imPart τ P.1 a c) (cov B g) := by
    intro a c
    have := Complex.ofRealCLM.contDiff.comp_contDiffOn (GlobalTheory.ThetaMetSmooth.im_smooth hτ a c)
    simpa [imPart, Function.comp_def] using this
  have hnE : ContDiffOn ℝ ∞ (fun P => nablaE τ h β s P) (cov B g) := by
    unfold nablaE
    exact ContDiffOn.sum fun i _ => (wedge_cd _ (hnab (hor_cd hτ (β i)))).add
      (wedge_cd _ ((dbar_contDiffOn hU hs (hor_cd hτ (β i))).add
        (GlobalTheory.TorsionForm.ConnSmooth.connForm_contDiffOn B τ s hτ hs (β i))))
  have hdb : ContDiffOn ℝ ∞ (fun P => dbarV s P) (cov B g) := by
    unfold dbarV
    exact ContDiffOn.sum fun a _ => wedge_cd _ (dbar_contDiffOn hU hs contDiffOn_const)
  have hda : ContDiffOn ℝ ∞ (fun P => dbarAdj τ h s P) (cov B g) := by
    unfold dbarAdj
    exact (ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ =>
      (contDiffOn_const.mul (hIm a c)).smul (contr_cd _ (hnab contDiffOn_const))).neg
  unfold superconn
  exact hnE.add ((contDiffOn_const (c := (Real.sqrt u : ℂ))).smul (hdb.add hda))

end GlobalTheory.TorsionForm.SuperconnSmooth
