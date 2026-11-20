import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTest
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuadraticWeilUnipotentTorusPreserveTest.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.quadraticWeil_unipotent_torus_preserve_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → (∀ z, IsTest (nOp A ψ x z φ)) ∧ ∀ s, IsTest (mOp A ω s φ) := by
  first | exact @GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | exact GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | (intros; apply GlobalTheory.JR.WeilQuad.isTest_nOp_mOp <;> assumption)
