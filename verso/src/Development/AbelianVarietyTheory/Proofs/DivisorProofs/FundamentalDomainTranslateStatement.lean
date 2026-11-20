import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainTranslate
import Mathlib

open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.fundamentalDomain_translate_conj` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFundamentalDomainTranslate.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.fundamental_domain_translate : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (Q : Subgroup G) (𝓓 : Set G) (m : G), IsFundamentalDomain Q 𝓓 μ → IsFundamentalDomain (Q.map (MulAut.conj m⁻¹).toMonoidHom) ((fun g => m⁻¹ * g) '' 𝓓) μ ∧ ∀ φ : G → ENNReal, ∫⁻ g in 𝓓, φ (m⁻¹ * g) ∂μ = ∫⁻ g in (fun g => m⁻¹ * g) '' 𝓓, φ g ∂μ := by
  first | exact @GlobalTheory.fundamentalDomain_translate_conj | exact GlobalTheory.fundamentalDomain_translate_conj | (intros; apply GlobalTheory.fundamentalDomain_translate_conj <;> assumption)
