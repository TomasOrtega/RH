import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatSmooth

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem symp_apply {g : ℕ} (v : Fin 2 → Fl g) : symp g v = riem (v 0) (v 1) := rfl

def quadL (g : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (F →L[ℝ] Fl g) →ₗ[ℝ] ((F →L[ℝ] Fl g) →L[ℝ] (F [⋀^Fin 2]→L[ℝ] ℝ)) where
  toFun L := (symp g).fderivCompContinuousLinearMap L
  map_add' L L' := by
    ext dL v
    simp [Fin.sum_univ_two, symp_apply, riem, Function.update_apply, ← Finset.sum_add_distrib]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  map_smul' c L := by
    ext dL v
    simp [Fin.sum_univ_two, symp_apply, riem, Function.update_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use extensionality with `v`. Simplify using `[quadL, Fin.sum_univ_two, symp_apply, riem, Function.update_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comp_eq_half (g : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] Fl g) :
    (symp g).compContinuousLinearMap L = (1 / 2 : ℝ) • quadL g F L L := by
  ext v
  simp [quadL, Fin.sum_univ_two, symp_apply, riem, Function.update_apply]
  ring

def quadCL (g : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    (F →L[ℝ] Fl g) →L[ℝ] ((F →L[ℝ] Fl g) →L[ℝ] (F [⋀^Fin 2]→L[ℝ] ℝ)) :=
  LinearMap.toContinuousLinearMap (quadL g F)

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)`.
-/
theorem contDiffOn_det_real {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    {M : X → Matrix (Fin n) (Fin n) ℝ} {s : Set X}
    (h : ∀ a b, ContDiffOn ℝ ∞ (fun v => M v a b) s) : ContDiffOn ℝ ∞ (fun v => (M v).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

/- English proof (translation)
Establish `e : ∀ v, (M v)⁻¹ a b = ((M v).det)⁻¹ * (M v).adjugate a b` using `fun v => by`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Both sides reduce to the same expression. Simplify using `only [e, Matrix.adjugate_apply]`. Use `ContDiffOn.mul ((contDiffOn_det_real h).inv hd) (contDiffOn_det_real fun c d => ?_)` and prove the remaining obligations.

Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`. Conclude with `contDiffOn_const`. Conclude with `h _ _`.
-/
theorem contDiffOn_inv_real {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    {M : X → Matrix (Fin n) (Fin n) ℝ} {s : Set X}
    (h : ∀ a b, ContDiffOn ℝ ∞ (fun v => M v a b) s) (hd : ∀ v ∈ s, (M v).det ≠ 0) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun v => (M v)⁻¹ a b) s := by
  have e : ∀ v, (M v)⁻¹ a b = ((M v).det)⁻¹ * (M v).adjugate a b := fun v => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  simp only [e, Matrix.adjugate_apply]
  refine ContDiffOn.mul ((contDiffOn_det_real h).inv hd) (contDiffOn_det_real fun c d => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact h _ _

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}

/- English proof (translation)
Set `e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)` to `(Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv`. Establish `h1 : AnalyticOnNhd ℂ (f ∘ e.symm) (e.symm ⁻¹' U)` using `ReciprocityTheory.AnForm.Osgood.osgood _ _ _ (hU.preimage e.symm.continuous) (hf.comp e.symm.differentiable.differentiableOn (Set.mapsTo_preimage _ _))`. Introduce `v hv`. Establish `h3 : AnalyticAt ℂ e v` using `e.toContinuousLinearMap.analyticAt v`. Establish `h2` using `(h1 (e v) (by simpa using hv)).comp h3`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules.
-/
theorem analyticOnNhd_of_differentiableOn {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    (Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv
  have h1 : AnalyticOnNhd ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    ReciprocityTheory.AnForm.Osgood.osgood _ _ _ (hU.preimage e.symm.continuous)
      (hf.comp e.symm.differentiable.differentiableOn (Set.mapsTo_preimage _ _))
  intro v hv
  have h3 : AnalyticAt ℂ e v := e.toContinuousLinearMap.analyticAt v
  have h2 := (h1 (e v) (by simpa using hv)).comp h3
  convert h2 using 1
  funext w
  simp

/- English proof (translation)
The claim follows from `hτ.1.prod isOpen_univ`.
-/
theorem isOpen_cov (hτ : IsPeriodMap B τ) : IsOpen (cov B g) := hτ.1.prod isOpen_univ

/- English proof (translation)
Establish `h0 : ContDiffOn ℂ ∞ (fun b => τ b i j) B` using `(analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn`. Establish `h1 : ContDiffOn ℝ ∞ (fun b => τ b i j) B` using `h0.restrict_scalars ℝ`. Conclude with `h1.comp contDiff_fst.contDiffOn fun P (hP : P ∈ cov B g) => hP.1`.
-/
theorem contDiffOn_tau (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => τ P.1 i j) (cov B g) := by
  have h0 : ContDiffOn ℂ ∞ (fun b => τ b i j) B :=
    (analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn
  have h1 : ContDiffOn ℝ ∞ (fun b => τ b i j) B := h0.restrict_scalars ℝ
  exact h1.comp contDiff_fst.contDiffOn fun P (hP : P ∈ cov B g) => hP.1

/- English proof (translation)
Establish `hre : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => (τ P.1 i j).re) (cov B g)` using `fun i j => Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_tau hτ i j)`. Establish `him : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => (τ P.1 i j).im) (cov B g)` using `fun i j => Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_tau hτ i j)`. Establish `hinv : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => ((τ P.1).map Complex.im)⁻¹ i j) (cov B g)` using `fun i j => contDiffOn_inv_real (fun a b => him a b) (fun P hP => (hτ.2.2 P.1 hP.1).2.det_pos.ne') i j`. Establish `hzr : ∀ i, ContDiffOn ℝ ∞ (fun P : Pt E g => (P.2 i).re) (cov B g)` using `fun i => (Complex.reCLM.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)).contDiffOn`. Establish `hzi : ∀ i, ContDiffOn ℝ ∞ (fun P : Pt E g => (P.2 i).im) (cov B g)` using `fun i => (Complex.imCLM.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)).contDiffOn`.

Use `contDiffOn_pi.2 fun k => ?_` and prove the remaining obligations. Consider the cases of `k with`. Consider the case `inl i`. Simplify using `only [flat, flatOf, Sum.elim_inl, Matrix.vecMul, dotProduct]`. Conclude with `ContDiffOn.sum fun j _ => (hzi j).mul (hinv j i)`.

Consider the case `inr i`. Simplify using `only [flat, flatOf, Sum.elim_inr, Matrix.vecMul, dotProduct, Pi.sub_apply]`. Conclude with `(hzr i).sub (ContDiffOn.sum fun j _ => (ContDiffOn.sum fun l _ => (hzi l).mul (hinv l j)).mul (hre j i))`.
-/
theorem contDiffOn_flat (hτ : IsPeriodMap B τ) : ContDiffOn ℝ ∞ (flat τ) (cov B g) := by
  have hre : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => (τ P.1 i j).re) (cov B g) := fun i j =>
    Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_tau hτ i j)
  have him : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => (τ P.1 i j).im) (cov B g) := fun i j =>
    Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_tau hτ i j)
  have hinv : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => ((τ P.1).map Complex.im)⁻¹ i j)
      (cov B g) := fun i j =>
    contDiffOn_inv_real (fun a b => him a b)
      (fun P hP => (hτ.2.2 P.1 hP.1).2.det_pos.ne') i j
  have hzr : ∀ i, ContDiffOn ℝ ∞ (fun P : Pt E g => (P.2 i).re) (cov B g) := fun i =>
    (Complex.reCLM.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)).contDiffOn
  have hzi : ∀ i, ContDiffOn ℝ ∞ (fun P : Pt E g => (P.2 i).im) (cov B g) := fun i =>
    (Complex.imCLM.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)).contDiffOn
  refine contDiffOn_pi.2 fun k => ?_
  cases k with
  | inl i =>
    simp only [flat, flatOf, Sum.elim_inl, Matrix.vecMul, dotProduct]
    exact ContDiffOn.sum fun j _ => (hzi j).mul (hinv j i)
  | inr i =>
    simp only [flat, flatOf, Sum.elim_inr, Matrix.vecMul, dotProduct, Pi.sub_apply]
    exact (hzr i).sub (ContDiffOn.sum fun j _ =>
      (ContDiffOn.sum fun l _ => (hzi l).mul (hinv l j)).mul (hre j i))

/- English proof (translation)
Establish `hdf : ContDiffOn ℝ ∞ (dflat τ) (cov B g)` using `(contDiffOn_flat hτ).fderiv_of_isOpen (isOpen_cov hτ) (by simp)`. Establish `e : om0 τ = fun P => (1 / 2 : ℝ) • quadCL g (Pt E g) (dflat τ P) (dflat τ P)`. Use function extensionality and compare the values at `P`. Conclude with `comp_eq_half g (dflat τ P)`. Rewrite using `[e]`.

Conclude with `(((quadCL g (Pt E g)).contDiff.comp_contDiffOn hdf).clm_apply hdf).const_smul _`.
-/
theorem om0_contDiffOn (hτ : IsPeriodMap B τ) : ContDiffOn ℝ ∞ (om0 τ) (cov B g) := by
  have hdf : ContDiffOn ℝ ∞ (dflat τ) (cov B g) :=
    (contDiffOn_flat hτ).fderiv_of_isOpen (isOpen_cov hτ) (by simp)
  have e : om0 τ = fun P => (1 / 2 : ℝ) • quadCL g (Pt E g) (dflat τ P) (dflat τ P) := by
    funext P
    exact comp_eq_half g (dflat τ P)
  rw [e]
  exact (((quadCL g (Pt E g)).contDiff.comp_contDiffOn hdf).clm_apply hdf).const_smul _

end GlobalTheory.FlatSmooth

/- English proof (translation)
Introduce `hτ` and use `GlobalTheory.FlatSmooth.om0_contDiffOn hτ`.
-/
theorem GlobalTheory.FlatSmooth.main : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
    IsPeriodMap B τ → ContDiffOn ℝ ∞ (om0 τ) (cov B g) :=
  fun hτ => GlobalTheory.FlatSmooth.om0_contDiffOn hτ
