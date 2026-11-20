import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

/- English proof (translation)
Simplify using `only [Nset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]`. Use `IsClosed.inter ?_ (IsClosed.inter ?_ ?_)` and prove the remaining obligations. Establish `hc : Continuous fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y`. Establish `h0 : Continuous fun y : Mt k r => (Matrix.of y : Matrix _ _ ℂ)` using `continuous_id`. Conclude with `(h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0`.

Conclude with `isClosed_eq hc continuous_const`. Use `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const`. Use `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const`.
-/
theorem nset_closed (k r : ℕ) : IsClosed {y : Mt k r | Matrix.of y ∈ Nset k r} := by
  simp only [Nset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · have hc : Continuous fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y := by
      have h0 : Continuous fun y : Mt k r => (Matrix.of y : Matrix _ _ ℂ) := continuous_id
      exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  · refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const

/- English proof (translation)
Introduce `ι _ k r`. Establish `hS : MeasurableSet {y : Mt k r | Matrix.of y ∈ Nset k r}` using `(nset_closed k r).measurableSet`. Establish `hH` using `(GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1`. Use `haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1`. Establish `hset : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} = ⋂ w, Function.eval w ⁻¹' {y : Mt k r | Matrix.of y ∈ Nset k r}`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hset]`. Conclude with `MeasurableSet.iInter fun w => measurable_pi_apply w hS`.

Rewrite using `[hset, Set.compl_iInter]`. Use `measure_iUnion_null fun w => ?_` and prove the remaining obligations. Rewrite using `[← Set.preimage_compl]`. Conclude with `Measure.pi_eval_preimage_null _ (by simpa [Set.compl_setOf] using hH.2.2.1)`.
-/
theorem pi_nset_full : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  intro ι _ k r
  have hS : MeasurableSet {y : Mt k r | Matrix.of y ∈ Nset k r} := (nset_closed k r).measurableSet
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hset : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
      ⋂ w, Function.eval w ⁻¹' {y : Mt k r | Matrix.of y ∈ Nset k r} := by
    ext x; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact MeasurableSet.iInter fun w => measurable_pi_apply w hS
  · rw [hset, Set.compl_iInter]
    refine measure_iUnion_null fun w => ?_
    rw [← Set.preimage_compl]
    exact Measure.pi_eval_preimage_null _ (by simpa [Set.compl_setOf] using hH.2.2.1)

end GlobalTheory.SnMass.VolN
