import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHyperbolicWeylActionEqFourierEtaleL.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  first | exact @GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | exact GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | (intros; apply GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB <;> assumption)
