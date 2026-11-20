import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibility
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FHodgeTateChartDivisibility.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.hodge_tate_chart_divisibility : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow | exact GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow <;> assumption)
