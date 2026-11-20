import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportFrameAlongUnitaryAdelic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.St.G.FrMap.transport` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTransportFrameAlongUnitaryAdelic.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.transport_frame_along_unitary_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  first | exact @GlobalTheory.St.G.FrMap.transport | exact GlobalTheory.St.G.FrMap.transport | (intros; apply GlobalTheory.St.G.FrMap.transport <;> assumption)
