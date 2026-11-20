import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardRingHomRealEqNrRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionIsGaloisAndEmbeddingStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Establish `h` using `Set.ncard_add_ncard_compl {φ : F →+* ℝ | 0 < φ δ}`. Establish `hc : {φ : F →+* ℝ | 0 < φ δ}ᶜ = {φ : F →+* ℝ | φ δ < 0}`. Use extensionality with `φ`. Establish `: φ δ ≠ 0` using `by simpa using hδ`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]`.

Conclude with `⟨fun a => lt_of_le_of_ne a this, le_of_lt⟩`. Rewrite `h` using `[hc]`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem card_real_eq_pos_add_tReal (F : Type) [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) :
    Nat.card (F →+* ℝ) = Nat.card {φ : F →+* ℝ // 0 < φ δ} + tReal F δ := by
  classical
  have h := Set.ncard_add_ncard_compl {φ : F →+* ℝ | 0 < φ δ}
  have hc : {φ : F →+* ℝ | 0 < φ δ}ᶜ = {φ : F →+* ℝ | φ δ < 0} := by
    ext φ
    have : φ δ ≠ 0 := by simpa using hδ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun a => lt_of_le_of_ne a this, le_of_lt⟩
  rw [hc] at h
  rw [← h]
  rfl

/- English proof (translation)
Establish `hext` using `(GlobalTheory.T.isQuadraticSqrtExtension_isGalois_and_embedding F E δ θ σ h).2.2 ℝ`. Establish `key : ∀ p : Bool × {φ : F →+* ℝ // 0 < φ δ}, ∃ ψ : E →+* ℝ, (∀ a : F, ψ (algebraMap F E a) = p.2.1 a) ∧ (0 < ψ θ ↔ p.1 = true)`. Introduce and unpack `⟨b, φ, hφ⟩`. Establish `hs : 0 < Real.sqrt (φ δ)` using `Real.sqrt_pos.mpr hφ`. Consider the cases of `b`.

Take `⟨ψ, h1, h2⟩` from `hext φ (-Real.sqrt (φ δ)) (by rw [neg_sq, Real.sq_sqrt hφ.le])`. Use `⟨ψ, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Simplify using `only [Bool.false_eq_true, iff_false, not_lt]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨ψ, h1, h2⟩` from `hext φ (Real.sqrt (φ δ)) (by rw [Real.sq_sqrt hφ.le])`. Use `⟨ψ, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Simplify using `using hφ`. Use `choose f hf1 hf2 using key`.

Establish `hinj : Function.Injective f`. Introduce `p q hpq`. Use `Prod.ext ?_ (Subtype.ext (RingHom.ext fun a => ?_))` and prove the remaining obligations. Use `(hf2 p).symm.trans (hpq ▸ hf2 q)` as an intermediate fact. Conclude with `Bool.eq_iff_iff.mpr this`.

Rewrite using `[← hf1 p a, ← hf1 q a, hpq]`. Use `Nat.card_le_card_of_injective f hinj` as an intermediate fact. Simplify `this` using `[Nat.card_prod]`.
-/
theorem two_mul_card_pos_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E) (h : IsQuad δ θ σ) :
    2 * Nat.card {φ : F →+* ℝ // 0 < φ δ} ≤ Nat.card (E →+* ℝ) := by
  classical
  have hext := (GlobalTheory.T.isQuadraticSqrtExtension_isGalois_and_embedding F E δ θ σ h).2.2 ℝ
  have key : ∀ p : Bool × {φ : F →+* ℝ // 0 < φ δ}, ∃ ψ : E →+* ℝ,
      (∀ a : F, ψ (algebraMap F E a) = p.2.1 a) ∧ (0 < ψ θ ↔ p.1 = true) := by
    rintro ⟨b, φ, hφ⟩
    have hs : 0 < Real.sqrt (φ δ) := Real.sqrt_pos.mpr hφ
    cases b
    · obtain ⟨ψ, h1, h2⟩ := hext φ (-Real.sqrt (φ δ)) (by rw [neg_sq, Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simp only [Bool.false_eq_true, iff_false, not_lt]
      linarith
    · obtain ⟨ψ, h1, h2⟩ := hext φ (Real.sqrt (φ δ)) (by rw [Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simpa using hφ
  choose f hf1 hf2 using key
  have hinj : Function.Injective f := by
    intro p q hpq
    refine Prod.ext ?_ (Subtype.ext (RingHom.ext fun a => ?_))
    · have := (hf2 p).symm.trans (hpq ▸ hf2 q)
      exact Bool.eq_iff_iff.mpr this
    · rw [← hf1 p a, ← hf1 q a, hpq]
  have := Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_prod] using this

/- English proof (translation)
Introduce `F E _ _ _ _ _ δ θ σ h`. Establish `hδ : δ ≠ 0` using `fun h0 => h.nonsq (h0 ▸ IsSquare.zero)`. Establish `h1` using `card_real_eq_pos_add_tReal F δ hδ`. Establish `h2` using `two_mul_card_pos_le F E δ θ σ h`. Rewrite `h1`, `h2` using `[GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces']`.

Establish `h3` using `InfinitePlace.card_add_two_mul_card_eq_rank F`. Establish `h4` using `InfinitePlace.card_add_two_mul_card_eq_rank E`. Establish `h5` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F`. Establish `h6` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E`. Establish `h7 : Module.finrank F E = 2` using `(GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ h).2.2.2.2.2.2`.

Establish `h8` using `Module.finrank_mul_finrank ℚ F E`. Rewrite `h8` using `[h7]`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_card_infinitePlace_le :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F)
      (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ →
      2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  intro F E _ _ _ _ _ δ θ σ h
  have hδ : δ ≠ 0 := fun h0 => h.nonsq (h0 ▸ IsSquare.zero)
  have h1 := card_real_eq_pos_add_tReal F δ hδ
  have h2 := two_mul_card_pos_le F E δ θ σ h
  rw [GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces'] at h1 h2
  have h3 := InfinitePlace.card_add_two_mul_card_eq_rank F
  have h4 := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h5 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : Module.finrank F E = 2 := (GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ h).2.2.2.2.2.2
  have h8 := Module.finrank_mul_finrank ℚ F E
  rw [h7] at h8
  omega

end GlobalTheory.QNorm
