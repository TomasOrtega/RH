import Mathlib
open NumberField

namespace GlobalTheory

open TensorProduct in

/- English proof (translation)
Set `_` to `Ideal.Quotient.field P`. Establish `e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M))` using `TensorProduct.quotTensorEquivQuotSMul M P`. Rewrite using `[← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]`. Use `congr 1`. Set `q : PrimeSpectrum (R ⧸ P)` to `⟨⊥, Ideal.isPrime_bot⟩`.

Establish `h1` using `Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q`. Rewrite `h1` using `[Module.rankAtStalk_eq_finrank_of_free]`. Establish `h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M`. Rewrite using `[Module.rankAtStalk_eq]`. Conclude with `Ideal.finrank_fiber_eq_finrank _`.

Rewrite using `[← h2, ← h1]`. Both sides reduce to the same expression.
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
Introduce `E _ _ La _ _ hfin hproj I g hg hI`. Establish `hprime : I.IsPrime` using `Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact hg.prime.irreducible)`. Establish `hne : I ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hI` using `[Ideal.absNorm_bot]`.

Conclude with `hg.ne_zero hI.symm`. Establish `hmax : I.IsMaximal` using `hprime.isMaximal hne`. Establish `hR : Nat.card (𝓞 E ⧸ I) = g`. Rewrite using `[← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hcard` using `natCard_quot_maximal_smul_top_eq (R := 𝓞 E) (M := La) I`.

Rewrite `hcard` using `[hR]`. Use `⟨?_, hcard.le⟩` and prove the remaining obligations. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[hcard]`. Conclude with `pow_ne_zero _ hg.ne_zero`.
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
