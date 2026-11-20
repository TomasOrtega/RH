import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.TrWSmulComp

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Meas

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

/- English proof (translation)
Rewrite using `[ae_iff]`. Conclude with `h.2.2.1`.
-/
theorem ae_UH_of_haar {μG : Measure (Mt k r)} (h : IsHaarOn (UH (Hpk k r)) μG) :
    ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by
  rw [ae_iff]
  exact h.2.2.1

/- English proof (translation)
Establish `hc : Continuous fun g : Matrix n n ℂ => gᴴ * A * g` using `(continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id`. Conclude with `isClosed_eq hc continuous_const`.
-/
private theorem isClosed_UH' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    IsClosed (UH A) := by
  have hc : Continuous fun g : Matrix n n ℂ => gᴴ * A * g :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

/- English proof (translation)
Conclude with `((isClosed_UH' (Hpk k r)).preimage (continuous_id : Continuous fun y : Mt k r => y)).measurableSet`.
-/
theorem measurableSet_UH' : MeasurableSet {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  exact ((isClosed_UH' (Hpk k r)).preimage (continuous_id : Continuous fun y : Mt k r => y)).measurableSet

/- English proof (translation)
Establish `hσ` using `(ds_rep hds).2.2.2 w`. Establish `hof : Continuous fun y : Mt k r => (Matrix.of y : Mx k r)` using `continuous_id`. Conclude with `continuousOn_const.inner (hσ.comp hof.continuousOn fun y hy => hy)`.
-/
theorem coef_contOn {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) (w v : H) :
    ContinuousOn (fun y : Mt k r => ⟪v, σ (Matrix.of y) w⟫_ℂ) {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  have hσ := (ds_rep hds).2.2.2 w
  have hof : Continuous fun y : Mt k r => (Matrix.of y : Mx k r) := continuous_id
  exact continuousOn_const.inner (hσ.comp hof.continuousOn fun y hy => hy)

/- English proof (translation)
Establish `h1` using `(coef_contOn hds w v).aestronglyMeasurable (measurableSet_UH' (k := k) (r := r)) (μ := μG)`. Rewrite `h1` using `[Measure.restrict_eq_self_of_ae_mem (s := {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}) (ae_UH_of_haar hG)]`. Then use the resulting hypothesis.
-/
theorem coef_aesm {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG) (w v : H) :
    AEStronglyMeasurable (fun y : Mt k r => ⟪v, σ (Matrix.of y) w⟫_ℂ) μG := by
  have h1 := (coef_contOn hds w v).aestronglyMeasurable (measurableSet_UH' (k := k) (r := r)) (μ := μG)
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)})
    (ae_UH_of_haar hG)] at h1

def Tset (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ UH (Hpk k r) ∧ (Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r)}

/- English proof (translation)
Establish `h1 : ∀ u : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Mx k r => g *ᵥ u` using `fun u => continuous_id.matrix_mulVec continuous_const`. Simplify using `only [UWset, Set.ofPred_and, Set.ofPred_forall]`. Conclude with `(isClosed_UH' _).inter ((isClosed_iInter fun a => (isClosed_eq (h1 _) continuous_const).inter (isClosed_eq (h1 _) continuous_const)).inter (isClosed_eq (h1 _) continuous_const))`.
-/
private theorem isClosed_UWset' (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have h1 : ∀ u : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Mx k r => g *ᵥ u :=
    fun u => continuous_id.matrix_mulVec continuous_const
  simp only [UWset, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_UH' _).inter ((isClosed_iInter fun a =>
    (isClosed_eq (h1 _) continuous_const).inter (isClosed_eq (h1 _) continuous_const)).inter
      (isClosed_eq (h1 _) continuous_const))

/- English proof (translation)
Simplify using `only [Nset, Set.ofPred_and, Set.ofPred_forall]`. Conclude with `(isClosed_UH' _).inter ((isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const).inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iI …`.
-/
private theorem isClosed_Nset_bessel_line (k r : ℕ) : IsClosed (Nset k r) := by
  simp only [Nset, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_UH' _).inter ((isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem _ _) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const))

/- English proof (translation)
Establish `c1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r)` using `continuous_fst`. Establish `c2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r)` using `continuous_fst.comp continuous_snd`. Establish `c3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r)` using `continuous_snd.comp continuous_snd`. Conclude with `(((isClosed_UH' (Hpk k r)).preimage c1).inter (((isClosed_UWset' (k := k) (r := r) z).preimage c2).inter ((isClosed_Nset_bessel_line k r).preimage c3))).measurableSet`.
-/
theorem measurableSet_Tset (z : Fin (2 * r + k + 1) → ℂ) : MeasurableSet (Tset (k := k) (r := r) z) := by
  have c1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r) := continuous_fst
  have c2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r) :=
    continuous_fst.comp continuous_snd
  have c3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r) :=
    continuous_snd.comp continuous_snd
  exact (((isClosed_UH' (Hpk k r)).preimage c1).inter
    (((isClosed_UWset' (k := k) (r := r) z).preimage c2).inter ((isClosed_Nset_bessel_line k r).preimage c3))).measurableSet

/- English proof (translation)
Establish `h1 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ UH (Hpk k r)` using `Measure.quasiMeasurePreserving_fst.ae (ae_UH_of_haar hG)`. Establish `h2 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r` using `Measure.quasiMeasurePreserving_snd.ae hM1`. Use `filter_upwards [h1, h2] with q hq1 hq2`. Conclude with `⟨hq1, hq2⟩`.
-/
theorem joint_ae {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    [SFinite μG] (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ Tset z := by
  have h1 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ UH (Hpk k r) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_UH_of_haar hG)
  have h2 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hM1
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, hq2⟩

/- English proof (translation)
Establish `hσ` using `(ds_rep hds).2.2.2 w`. Establish `a1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r)` using `continuous_fst.comp continuous_snd`. Establish `a2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r)` using `continuous_snd.comp continuous_snd`. Establish `a3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r)` using `continuous_fst`. Establish `hc : Continuous fun q : Mt k r × (Mt k r × Mt k r) => sM q.2 * Matrix.of q.1`.

Unfold `sM`. Conclude with `(a1.matrix_mul a2).matrix_mul a3`. Use `continuousOn_const.inner (hσ.comp hc.continuousOn ?_)` and prove the remaining obligations. Introduce `q hq`. Take `⟨h1, h2, h3⟩` from `hq`.

Conclude with `hGr.1 _ (hGr.1 _ h2.1 _ h3.1) _ h1`.
-/
theorem matrix_coefficient_continuousOn {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z) (w v : H) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => ⟪v, σ (sM q.2 * Matrix.of q.1) w⟫_ℂ) (Tset z) := by
  have hσ := (ds_rep hds).2.2.2 w
  have a1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r) :=
    continuous_fst.comp continuous_snd
  have a2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r) :=
    continuous_snd.comp continuous_snd
  have a3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r) := continuous_fst
  have hc : Continuous fun q : Mt k r × (Mt k r × Mt k r) => sM q.2 * Matrix.of q.1 := by
    unfold sM
    exact (a1.matrix_mul a2).matrix_mul a3
  refine continuousOn_const.inner (hσ.comp hc.continuousOn ?_)
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hq
  exact hGr.1 _ (hGr.1 _ h2.1 _ h3.1) _ h1

/- English proof (translation)
Establish `h` using `(matrix_coefficient_continuousOn hds hGr w v).aestronglyMeasurable (measurableSet_Tset z) (μ := μG.prod (μW.prod μN))`. Rewrite `h` using `[Measure.restrict_eq_self_of_ae_mem (joint_ae hG hM1)]`. Then use the resulting hypothesis.
-/
theorem matrix_coefficient_ae_strongly_measurable {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z)
    {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μG] (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) (w v : H) :
    AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) => ⟪v, σ (sM q.2 * Matrix.of q.1) w⟫_ℂ)
      (μG.prod (μW.prod μN)) := by
  have h := (matrix_coefficient_continuousOn hds hGr w v).aestronglyMeasurable (measurableSet_Tset z) (μ := μG.prod (μW.prod μN))
  rwa [Measure.restrict_eq_self_of_ae_mem (joint_ae hG hM1)] at h

/- English proof (translation)
Use `h.1` as an intermediate fact. Use `infer_instance`.
-/
theorem sfinite_haar {μG : Measure (Mt k r)} (h : IsHaarOn (UH (Hpk k r)) μG) : SFinite μG := by
  have := h.1
  infer_instance

end Meas

end PI.WBL.FSW
