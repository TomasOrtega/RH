import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `haveI hred : IsReduced (Ω ⊗[L] Ω) := GlobalTheory.ReducedAlg.isReduced_tensor (k := L) Ω Ω`. Establish `he : (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) ≠ 0`. Introduce `h`. Establish `h1 : (a ⊗ₜ[L] (1 : Ω) : Ω ⊗[L] Ω) = (1 : Ω) ⊗ₜ[L] a` using `sub_eq_zero.mp h`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual L Ω, φ 1 ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `one_ne_zero ((Module.forall_dual_apply_eq_zero_iff L (1 : Ω)).mp hc)`. Establish `h2` using `congrArg (fun x => TensorProduct.rid L Ω (LinearMap.lTensor Ω φ x)) h1`. Simplify using `only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h2`.

Apply `ha` to reduce the goal to its premises. Use `⟨(φ 1)⁻¹ * φ a, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hφ, one_smul]`. Establish `hn : ¬ IsNilpotent (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω)` using `fun h => he h.eq_zero`. Rewrite `hn` using `[nilpotent_iff_mem_prime]`.

Use `push_neg at hn`. Take `⟨J, hJ, heJ⟩` from `hn`. Use `haveI := hJ`. Set `g : (Ω ⊗[L] Ω) →+* FractionRing ((Ω ⊗[L] Ω) ⧸ J)` to `(algebraMap ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J))).comp (Ideal.Quotient.mk J)`. Use `⟨FractionRing ((Ω ⊗[L] Ω) ⧸ J), inferInstance, g.comp (Algebra.TensorProduct.includeLeftRingHom), g.comp (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := Ω)).toRingHom, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `l`. Simplify using `only [RingHom.comp_apply]`. Use `congr 1`. Use `show (algebraMap L Ω l) ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] (algebraMap L Ω l)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.

Introduce `h`. Apply `heJ` to reduce the goal to its premises. Establish `h3 : g (a ⊗ₜ[L] (1 : Ω)) = g ((1 : Ω) ⊗ₜ[L] a)` using `h`. Establish `h4` using `IsFractionRing.injective ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J)) h3`. Conclude with `Ideal.Quotient.eq.mp h4`.
-/
theorem exists_embeddings_agree_on_subfield_ne (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω]
    [CharZero L] (a : Ω) (ha : a ∉ Set.range (algebraMap L Ω)) :
    ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F),
      i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  haveI hred : IsReduced (Ω ⊗[L] Ω) := GlobalTheory.ReducedAlg.isReduced_tensor (k := L) Ω Ω
  have he : (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) ≠ 0 := by
    intro h
    have h1 : (a ⊗ₜ[L] (1 : Ω) : Ω ⊗[L] Ω) = (1 : Ω) ⊗ₜ[L] a := sub_eq_zero.mp h
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L Ω, φ 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff L (1 : Ω)).mp hc)
    have h2 := congrArg (fun x => TensorProduct.rid L Ω (LinearMap.lTensor Ω φ x)) h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h2
    apply ha
    refine ⟨(φ 1)⁻¹ * φ a, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  have hn : ¬ IsNilpotent (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) :=
    fun h => he h.eq_zero
  rw [nilpotent_iff_mem_prime] at hn
  push_neg at hn
  obtain ⟨J, hJ, heJ⟩ := hn
  haveI := hJ
  let g : (Ω ⊗[L] Ω) →+* FractionRing ((Ω ⊗[L] Ω) ⧸ J) :=
    (algebraMap ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J))).comp (Ideal.Quotient.mk J)
  refine ⟨FractionRing ((Ω ⊗[L] Ω) ⧸ J), inferInstance,
    g.comp (Algebra.TensorProduct.includeLeftRingHom),
    g.comp (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := Ω)).toRingHom, ?_, ?_⟩
  · ext l
    simp only [RingHom.comp_apply]
    congr 1
    show (algebraMap L Ω l) ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] (algebraMap L Ω l)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · intro h
    apply heJ
    have h3 : g (a ⊗ₜ[L] (1 : Ω)) = g ((1 : Ω) ⊗ₜ[L] a) := h
    have h4 := IsFractionRing.injective ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J)) h3
    exact Ideal.Quotient.eq.mp h4

end GlobalTheory
