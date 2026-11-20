import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Introduce `d d' S A B h`. Establish `hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))` using `Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)`. Establish `hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A)` using `by open scoped Matrix.Norms.Operator in`. Conclude with `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A`. Establish `hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B)` using `by open scoped Matrix.Norms.Operator in`.

Conclude with `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B`. Use `hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `S.sum_mem fun n _ => ?_` and prove the remaining obligations. Conclude with `S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.expSub :
    ∀ (d d' : ℕ) (S : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))
      (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ), (A, B) ∈ S → (NormedSpace.exp A, NormedSpace.exp B) ∈ S := by
  intro d d' S A B h
  have hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B
  refine hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  exact S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)
