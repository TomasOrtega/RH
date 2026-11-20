import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePadicIntDomainEmbedding
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFinitePadicIntDomainEmbedding.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.exists_finite_padicInt_domain_embedding : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C → (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D), Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  first | exact @GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | exact GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | (intros; apply GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain <;> assumption)
