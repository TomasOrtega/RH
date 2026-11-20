import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInertPlaceKernelSignEqEtaGramDet.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapSign_eq_eta_gramDet | exact GlobalTheory.KapLat.kapSign_eq_eta_gramDet | (intros; apply GlobalTheory.KapLat.kapSign_eq_eta_gramDet <;> assumption)
