import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard

/- English proof (translation)
Establish `e : (F →+* ℝ) ≃ (F →+* ℂ)` using `{ toFun := fun σ => Complex.ofRealHom.comp σ invFun := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding left_inv := fun σ => by`. Use extensionality with `x`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Simplify using `[ComplexEmbedding.IsReal.coe_embedding_apply]`. Use `right_inv := fun φ => by`.

Use extensionality with `x`. Simplify using `[ComplexEmbedding.IsReal.coe_embedding_apply] }`. Establish `hc : Nat.card (F →+* ℂ) = Module.finrank ℚ F`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Embeddings.card F ℂ`.

Use `⟨Finite.of_equiv _ e.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr e, hc]`.
-/
theorem finite_and_card_realEmbeddings (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  have e : (F →+* ℝ) ≃ (F →+* ℂ) :=
    { toFun := fun σ => Complex.ofRealHom.comp σ
      invFun := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
      left_inv := fun σ => by
        ext x
        apply Complex.ofReal_injective
        simp [ComplexEmbedding.IsReal.coe_embedding_apply]
      right_inv := fun φ => by
        ext x
        simp [ComplexEmbedding.IsReal.coe_embedding_apply] }
  have hc : Nat.card (F →+* ℂ) = Module.finrank ℚ F := by
    rw [Nat.card_eq_fintype_card]
    exact Embeddings.card F ℂ
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard
