import Mathlib
open NumberField

namespace GlobalTheory

open TensorProduct in

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem natCard_quot_maximal_smul_top_eq {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) = Nat.card (R ⧸ P) ^ Module.finrank R M := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  rw [← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]
  congr 1
  let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
    rw [Module.rankAtStalk_eq]
    exact Ideal.finrank_fiber_eq_finrank _
  rw [← h2, ← h1]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem natCard_quot_smul_top_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La →
    ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g →
    Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧
      Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  intro E _ _ La _ _ hfin hproj I g hg hI
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact hg.prime.irreducible)
  have hne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  have hR : Nat.card (𝓞 E ⧸ I) = g := by
    rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcard := natCard_quot_maximal_smul_top_eq (R := 𝓞 E) (M := La) I
  rw [hR] at hcard
  refine ⟨?_, hcard.le⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hg.ne_zero

end GlobalTheory
