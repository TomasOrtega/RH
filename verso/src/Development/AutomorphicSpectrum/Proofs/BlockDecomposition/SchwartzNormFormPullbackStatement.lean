import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzNormFormPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSchwartzNormFormPullback.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.schwartz_norm_form_pullback : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (f : F → ℂ), f ∈ schwartzBruhat F → (fun x : E => f (Algebra.norm F x)) ∈ schwartzBruhat E := by
  first | exact @GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat | exact GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat <;> assumption)
