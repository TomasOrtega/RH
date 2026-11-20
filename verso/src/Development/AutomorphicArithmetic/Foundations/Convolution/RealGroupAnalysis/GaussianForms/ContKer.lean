import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Use `continuous_of_dominated (bound := fun y => ‖f y‖) ?_ ?_ hfi.norm ?_` and prove the remaining obligations. Introduce `p`. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `((ha.comp (continuous_const.prodMk continuous_id)).mul hfc).mul (hb.comp (continuous_const.prodMk continuous_id))`. Introduce `p`.

Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, ha1, hb1, one_mul, mul_one]`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Conclude with `((ha.comp (continuous_id.prodMk continuous_const)).mul continuous_const).mul (hb.comp (continuous_id.prodMk continuous_const))`.
-/
private lemma cont_param {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {μ : Measure Y} {f : Y → ℂ} (hfc : Continuous f) (hfi : Integrable f μ)
    {a b : X × Y → ℂ} (ha : Continuous a) (hb : Continuous b)
    (ha1 : ∀ z, ‖a z‖ = 1) (hb1 : ∀ z, ‖b z‖ = 1) :
    Continuous fun p : X => ∫ y, a (p, y) * f y * b (p, y) ∂μ := by
  refine continuous_of_dominated (bound := fun y => ‖f y‖) ?_ ?_ hfi.norm ?_
  · intro p
    refine Continuous.aestronglyMeasurable ?_
    exact ((ha.comp (continuous_const.prodMk continuous_id)).mul hfc).mul
      (hb.comp (continuous_const.prodMk continuous_id))
  · intro p
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_mul, ha1, hb1, one_mul, mul_one]
  · refine Eventually.of_forall fun y => ?_
    exact ((ha.comp (continuous_id.prodMk continuous_const)).mul continuous_const).mul
      (hb.comp (continuous_id.prodMk continuous_const))

section
variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp continuous_adelicChar`.
-/
private theorem cψ : Continuous (ψ : A F → ℂ) := continuous_subtype_val.comp continuous_adelicChar
/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
private theorem nψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _
/- English proof (translation)
Unfold `q4`. Use `fun_prop`.
-/
private theorem cq (δ : F) : Continuous (q4 δ : V4 F → A F) := by
  unfold q4
  fun_prop
/- English proof (translation)
The claim follows from `cψ.comp ((continuous_fst.comp continuous_fst).mul ((cq δ).comp continuous_snd))`.
-/
private theorem ca (δ : F) : Continuous fun z : (A F × V4 F) × V4 F => ψ (z.1.1 * q4 δ z.2) :=
  cψ.comp ((continuous_fst.comp continuous_fst).mul ((cq δ).comp continuous_snd))
/- English proof (translation)
Establish `h : Continuous fun z : (A F × V4 F) × V4 F => B4 δ z.2 z.1.2`. Unfold `B4`. Use `fun_prop`. Conclude with `cψ.comp h`.
-/
private theorem cb (δ : F) : Continuous fun z : (A F × V4 F) × V4 F => ψ (B4 δ z.2 z.1.2) := by
  have h : Continuous fun z : (A F × V4 F) × V4 F => B4 δ z.2 z.1.2 := by
    unfold B4
    fun_prop
  exact cψ.comp h
/- English proof (translation)
The claim follows from `cont_param (continuous_of_mem_schwartzBruhatPi φ.2) (integrable_of_mem_schwartzBruhatPi φ.2) (ca δ) (cb δ) (fun _ => nψ _) (fun _ => nψ _)`.
-/
private theorem key (δ : F) (φ : S4 F) :
    Continuous fun p : A F × V4 F => ∫ y, ψ (p.1 * q4 δ y) * φ.1 y * ψ (B4 δ y p.2) ∂(adeleMeasurePi F) :=
  cont_param (continuous_of_mem_schwartzBruhatPi φ.2) (integrable_of_mem_schwartzBruhatPi φ.2)
    (ca δ) (cb δ) (fun _ => nψ _) (fun _ => nψ _)
end

/- English proof (translation)
Introduce `F _ _ δ φ`. Conclude with `key δ φ`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.contKer :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F), Continuous fun p : A F × V4 F => ft4 δ (fun y => ψ (p.1 * q4 δ y) * φ.1 y) p.2 := by
  intro F _ _ δ φ
  exact key δ φ
