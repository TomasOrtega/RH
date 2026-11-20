import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2Inner
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegralEqL2Inner.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.integral_eq_l2_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | exact GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner <;> assumption)
