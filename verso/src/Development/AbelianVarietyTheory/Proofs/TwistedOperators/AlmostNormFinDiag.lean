import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

/- English proof (translation)
Establish `hr : Module.finrank K L = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two K L`. Use `haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ hr`. Establish `hc : Nat.card (L ≃ₐ[K] L) = 2` using `(IsGalois.card_aut_eq_finrank K L).trans hr`. Use `haveI : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)`. Take `⟨σ, hσ⟩` from `exists_ne (1 : L ≃ₐ[K] L)`.

Establish `h2 : σ * σ = 1` using `by rw [← sq, ← hc]; exact pow_card_eq_one'`. Take `⟨δ, b, h1, h0, -, h3⟩` from `GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr (fun x => by`. Use `congrArg (fun τ : L ≃ₐ[K] L => τ x) h2` as an intermediate fact. Simplify using `using this)`. Use the proof step `(by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hσ (AlgEquiv.ext h))`. Conclude with `⟨δ, b, h1, h0, h3⟩`.
-/
theorem AlmostNorm.exists_basis_sq (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (b : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ b 0 = 1 ∧
      b 1 * b 1 = algebraMap K L δ := by
  have hr : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ hr
  have hc : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hr
  haveI : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[K] L)
  have h2 : σ * σ = 1 := by rw [← sq, ← hc]; exact pow_card_eq_one'
  obtain ⟨δ, b, h1, h0, -, h3⟩ := GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr
    (fun x => by
      have := congrArg (fun τ : L ≃ₐ[K] L => τ x) h2
      simpa using this)
    (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h))
  exact ⟨δ, b, h1, h0, h3⟩

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ t`. Take `⟨δ, b, hδ, h0, h1⟩` from `AlmostNorm.exists_basis_sq K L`. Establish `hδ0 : δ ≠ 0` using `fun h => hδ (h ▸ IsSquare.zero)`. Use `(((GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).union (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ0))).union (GlobalTheory.QNorm.finite_valuation_ne_one K t)).subset ?_` and prove the remaining obligations. Introduce `v hv`.

Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Units.val_mk0] at hn`. Take `⟨⟨h2, hd⟩, ht⟩` from `hn`. Establish `key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x` using `fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Take `⟨x, -, y, -, h⟩` from `GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v (algebraMap K _ δ) (algebraMap K _ (t : K)) (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2) (by rw [key, hd]) (by rw [key, ht])`.

Conclude with `hv ((mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩)`.
-/
theorem almostNorm_finDiag :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L], ∀ t : Kˣ, AlmostNorm K L (finDiag K t) := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine (((GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ0))).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K t)).subset ?_
  intro v hv
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Units.val_mk0] at hn
  obtain ⟨⟨h2, hd⟩, ht⟩ := hn
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  obtain ⟨x, -, y, -, h⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v
    (algebraMap K _ δ) (algebraMap K _ (t : K))
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2) (by rw [key, hd]) (by rw [key, ht])
  exact hv ((mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩)

end GlobalTheory.QuadSymbol
