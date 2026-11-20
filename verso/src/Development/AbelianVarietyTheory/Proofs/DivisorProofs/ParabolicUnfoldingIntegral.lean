import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `using mat_inv_mul' (F := F) g⁻¹`.
-/
theorem mat_mul_inv' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  simpa using mat_inv_mul' (F := F) g⁻¹

/- English proof (translation)
Take `⟨hu1, hu2⟩` from `hu`. Establish `hx' : mat g⁻¹ *ᵥ incV F H.x = incV F H.x` using `by conv_lhs => rw [← hx]`. Rewrite using `[Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]`. Establish `hι' : mat g⁻¹ * incM F H.ι = incM F H.ι * mat g₁⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc (mat g⁻¹), Matrix.mul_assoc (incM F H.ι), mat_mul_inv', Matrix.mul_one]`. Use `_ = incM F H.ι * mat g₁⁻¹ := by`. Rewrite using `[← hι, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]`. Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, hu1, hx']`.

Take `⟨a, ha⟩` from `hu2 (mat g₁ *ᵥ z)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `e1 : mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₁ *ᵥ z)`. Rewrite using `[Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec]`. Establish `e2 : mat g⁻¹ *ᵥ (incM F H.ι *ᵥ (mat g₁ *ᵥ z)) = incM F H.ι *ᵥ z`.

Rewrite using `[Matrix.mulVec_mulVec, hι', ← Matrix.mulVec_mulVec]`. Use `congr 1`. Rewrite using `[Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]`. Rewrite using `[mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx', e2]`.
-/
theorem conj_mem_unipSet {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} (H : Plane E n n₁) (g : UA σ W.J)
    (g₁ : UA σ W₁.J) (hx : mat g *ᵥ incV F H.x = incV F H.x) (hι : mat g * incM F H.ι = incM F H.ι * mat g₁)
    (u : UA σ W.J) (hu : u ∈ unipSet σ W H) : g⁻¹ * u * g ∈ unipSet σ W H := by
  obtain ⟨hu1, hu2⟩ := hu
  have hx' : mat g⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
  have hι' : mat g⁻¹ * incM F H.ι = incM F H.ι * mat g₁⁻¹ := by
    calc mat g⁻¹ * incM F H.ι = mat g⁻¹ * (incM F H.ι * mat g₁) * mat g₁⁻¹ := by
          rw [Matrix.mul_assoc (mat g⁻¹), Matrix.mul_assoc (incM F H.ι), mat_mul_inv', Matrix.mul_one]
      _ = incM F H.ι * mat g₁⁻¹ := by
          rw [← hι, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  refine ⟨?_, fun z => ?_⟩
  · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, hu1, hx']
  · obtain ⟨a, ha⟩ := hu2 (mat g₁ *ᵥ z)
    refine ⟨a, ?_⟩
    have e1 : mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₁ *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec]
    have e2 : mat g⁻¹ *ᵥ (incM F H.ι *ᵥ (mat g₁ *ᵥ z)) = incM F H.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, hι', ← Matrix.mulVec_mulVec]
      congr 1
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add,
      Matrix.mulVec_smul, hx', e2]

end GlobalTheory.UnipCT

end
