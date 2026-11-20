import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivApply
open MeasureTheory

namespace GlobalTheory.WeakDeriv

/- English proof (translation)
Use `haveI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ) := Module.Finite.of_injective ((ContinuousMultilinearMap.toMultilinearMapLinear : ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => D) ℂ)) ContinuousMultilinea …`. Conclude with `Module.Finite.of_restrictScalars_finite ℝ ℂ _`.
-/
theorem finiteDimensional_multilinear {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] (n : ℕ) :
    FiniteDimensional ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ) := by
  haveI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ) :=
    Module.Finite.of_injective
      ((ContinuousMultilinearMap.toMultilinearMapLinear :
        ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => D) ℂ))
      ContinuousMultilinearMap.toMultilinearMap_injective
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

/- English proof (translation)
Use `haveI := finiteDimensional_multilinear (D := D) n`. Use `set A := GlobalTheory.SchwInt.iterEvalCLM (V := D) n x`. Set `b` to `Module.finBasis ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ)`. Set `e` to `b.equivFunL`. Establish `h1 : Continuous fun s => e (A (f s))`.

Use `continuous_pi fun i => ?_` and prove the remaining obligations. Conclude with `hf ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (Module.finrank ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ)) => ℂ) i).comp ((e : ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ →L[ℂ] _).comp A))`. Establish `h2 : Continuous fun s => e.symm (e (A (f s)))` using `e.symm.continuous.comp h1`. Simplify `h2` using `[A]`.
-/
theorem continuous_iteratedFDeriv_of_weak {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [TopologicalSpace S]
    (f : S → SchwartzMap D ℂ)
    (hf : ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, Continuous fun s => T (f s))
    (n : ℕ) (x : D) : Continuous fun s => iteratedFDeriv ℝ n (f s) x := by
  haveI := finiteDimensional_multilinear (D := D) n
  set A := GlobalTheory.SchwInt.iterEvalCLM (V := D) n x
  let b := Module.finBasis ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ)
  let e := b.equivFunL
  have h1 : Continuous fun s => e (A (f s)) := by
    refine continuous_pi fun i => ?_
    exact hf ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (Module.finrank ℂ
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ)) => ℂ) i).comp
      ((e : ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ →L[ℂ] _).comp A))
  have h2 : Continuous fun s => e.symm (e (A (f s))) := e.symm.continuous.comp h1
  simpa [A] using h2

end GlobalTheory.WeakDeriv
