import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RatVecDomain.exists_fundamentalDomain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFundDomainRationalPointsAdeleTupleFinitePo.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ 𝓕₁ : Set (κ → AF F), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ ∧ μ 𝓕₁ ≠ 0 ∧ μ 𝓕₁ ≠ ⊤ := by
  first | exact @GlobalTheory.RatVecDomain.exists_fundamentalDomain | exact GlobalTheory.RatVecDomain.exists_fundamentalDomain | (intros; apply GlobalTheory.RatVecDomain.exists_fundamentalDomain <;> assumption)
