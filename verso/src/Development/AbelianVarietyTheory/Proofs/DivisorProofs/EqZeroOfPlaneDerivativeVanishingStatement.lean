import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPlaneDerivativeVanishing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfPlaneDerivativeVanishing.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_plane_derivative_vanishing : ∀ (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2) (f₀ : SInf F (Fin n × Fin d)),
    (∀ γ : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd γ →
      ∃ β : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd β ∧ ∃ c : ℂ, ∀ x, dH γ 0 ⇑f₀ x = c * dH 0 β ⇑f₀ x) →
    (∀ x₁, f₀ (ins0 hd x₁) = 0) → f₀ = 0 := by
  first | exact @GlobalTheory.ThK.PlaneEv.eq_zero_of_dH_plane_of_ins0 | exact GlobalTheory.ThK.PlaneEv.eq_zero_of_dH_plane_of_ins0 | (intros; apply GlobalTheory.ThK.PlaneEv.eq_zero_of_dH_plane_of_ins0 <;> assumption)
