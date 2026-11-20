import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocalFieldIso.isTateEps_transport` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTateEpsilonTransport.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.tate_epsilon_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  first | exact @GlobalTheory.LocalFieldIso.isTateEps_transport | exact GlobalTheory.LocalFieldIso.isTateEps_transport | (intros; apply GlobalTheory.LocalFieldIso.isTateEps_transport <;> assumption)
