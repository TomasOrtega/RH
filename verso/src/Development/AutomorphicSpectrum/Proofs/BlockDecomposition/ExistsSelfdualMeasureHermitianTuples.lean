import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ψ hψ n`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Set `b` to `Module.finBasis F E`. Take `⟨B, hsym, hdet, -, hR'⟩` from `GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ _ b`. Take `⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)`.

Use `haveI := h1`. Use `haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩`. Use `haveI := hBor n M`. Establish `hc : IsHomeomorph (GlobalTheory.CompanionTheory.SW.SdTuples.cf (F` using `F) (E := E) (AF F) b) := hcc _ b`. Establish `hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm`.

Unfold `Matrix.IsSymm`. Rewrite using `[Matrix.blockDiagonal_transpose]`. Simplify using `only [hsym.eq]`. Establish `hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0`. Rewrite using `[Matrix.det_blockDiagonal]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => hdet`. Take `⟨μ, hμ⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_selfDual_form ψ hψ _ hsym' hdet' (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M)`. Use `⟨μ, ?_⟩` and prove the remaining obligations. Unfold `SdW`. Establish `hf : (fun X Y : Fin n → Fin M → AF F ⊗[F] E => ψ (BR (AF F) σ J X Y)) = fun X Y => ψ (dotProduct (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M X) (Matrix.mulVec ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F (AF F))) (GlobalTheory.CompanionTheory.SW.SdTuples …`.

Use function extensionality and compare the values at `X Y`. Rewrite using `[← GlobalTheory.CompanionTheory.SW.SdTuples.BR_eq hc J B (hR' (AF F)).1 X Y]`. Rewrite using `[hf]`. Conclude with `hμ`.
-/
theorem exists_sdW_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ μ : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨B, hsym, hdet, -, hR'⟩ :=
    GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ _ b
  obtain ⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := hBor n M
  have hc : IsHomeomorph (GlobalTheory.CompanionTheory.SW.SdTuples.cf (F := F) (E := E) (AF F) b) := hcc _ b
  have hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    simp only [hsym.eq]
  have hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hdet
  obtain ⟨μ, hμ⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_selfDual_form ψ hψ _ hsym' hdet'
    (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M)
  refine ⟨μ, ?_⟩
  unfold SdW
  have hf : (fun X Y : Fin n → Fin M → AF F ⊗[F] E => ψ (BR (AF F) σ J X Y)) = fun X Y =>
      ψ (dotProduct (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M X) (Matrix.mulVec
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F (AF F)))
        (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M Y))) := by
    funext X Y
    rw [← GlobalTheory.CompanionTheory.SW.SdTuples.BR_eq hc J B (hR' (AF F)).1 X Y]
  rw [hf]
  exact hμ

end GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN
