import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatProdEqEtaResultantMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSgnLatProdEqEtaResultantMul.lean&line=260#L260)
-/
theorem _root_.GlobalTheory.T.sgnLat_prod_eq_eta_resultant_mul : ∀ (K : UQ) (B₁ B₂ : InvAlg K), (B₁.P * B₂.P).Separable → ∀ M ∈ (B₁.prod B₂).Lin, (B₁.prod B₂).sgnLat M = K.eta (resultant B₁.P B₂.P) * B₁.sgnLat (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * B₂.sgnLat (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | exact GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | (intros; apply GlobalTheory.UnitLemma.SgnProd.sgnLat_prod <;> assumption)
