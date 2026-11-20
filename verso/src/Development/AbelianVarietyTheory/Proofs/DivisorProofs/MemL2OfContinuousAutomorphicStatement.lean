import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemL2OfContinuousAutomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemL2OfContinuousAutomorphic.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.memL2_of_continuous_automorphic : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → Links.IsMeasDef V K μ 𝓕 →
  ∀ u : GA D V → ℂ, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) → GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ u := by
  first | exact @GlobalTheory.DefiniteSqInt.memL2_of_continuous_definite | exact GlobalTheory.DefiniteSqInt.memL2_of_continuous_definite | (intros; apply GlobalTheory.DefiniteSqInt.memL2_of_continuous_definite <;> assumption)
