import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n n₁ Y Y₁ H h₁ m hm`. Take `⟨hx, -, hι⟩` from `hm`. Establish `hx' : mat m *ᵥ incV F H.x = incV F H.x` using `by simpa using hx`. Establish `hxi : mat m⁻¹ *ᵥ incV F H.x = incV F H.x` using `by conv_lhs => rw [← hx']`. Rewrite using `[Matrix.mulVec_mulVec, FlagPar.mat_inv_mul, Matrix.one_mulVec]`.

Establish `hh : mat h₁ * mat h₁⁻¹ = 1` using `by rw [← FlagPar.mat_mul, mul_inv_cancel, FlagPar.mat_one]`. Establish `hιi : mat m⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc (mat m⁻¹), Matrix.mul_assoc (incM F H.ι), hh, Matrix.mul_one]`. Use `_ = incM F H.ι * mat h₁⁻¹ := by rw [← hι, ← Matrix.mul_assoc, FlagPar.mat_inv_mul, Matrix.one_mul]`.

Introduce `u hu`. Proceed by induction on `hu using Subgroup.closure_induction with`. Consider the case `mem u hu`. Take `⟨h1, h2⟩` from `hu`. Apply `Subgroup.subset_closure` to reduce the goal to its premises.

Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxi, h1, hx']`. Take `⟨a, ha⟩` from `h2 (mat h₁⁻¹ *ᵥ z)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `e1 : mat m⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z)`.

Rewrite using `[Matrix.mulVec_mulVec, hιi, ← Matrix.mulVec_mulVec]`. Establish `e2 : mat m *ᵥ (incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z)) = incM F H.ι *ᵥ z`. Rewrite using `[Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat h₁), hh, Matrix.one_mulVec]`. Rewrite using `[FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx', e2]`. Consider the case `one => simp`.

Consider the case `mul x y _ _ hx hy`. Use `mul_mem hx hy` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Consider the case `inv x _ hx`. Use `inv_mem hx` as an intermediate fact.

Simplify `this` using `[mul_assoc]`.
-/
theorem levi_conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (h₁ : UA σ Y₁.J) (m : UA σ Y.J),
    IsLevi (W₁ := Y₁) H 1 h₁ m → ∀ u ∈ unip σ Y H, m * u * m⁻¹ ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H h₁ m hm
  obtain ⟨hx, -, hι⟩ := hm
  have hx' : mat m *ᵥ incV F H.x = incV F H.x := by simpa using hx
  have hxi : mat m⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx']
    rw [Matrix.mulVec_mulVec, FlagPar.mat_inv_mul, Matrix.one_mulVec]
  have hh : mat h₁ * mat h₁⁻¹ = 1 := by rw [← FlagPar.mat_mul, mul_inv_cancel, FlagPar.mat_one]
  have hιi : mat m⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * mat h₁) * mat h₁⁻¹ := by
          rw [Matrix.mul_assoc (mat m⁻¹), Matrix.mul_assoc (incM F H.ι), hh, Matrix.mul_one]
      _ = incM F H.ι * mat h₁⁻¹ := by rw [← hι, ← Matrix.mul_assoc, FlagPar.mat_inv_mul, Matrix.one_mul]
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨h1, h2⟩ := hu
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ?_⟩
    · rw [FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxi, h1, hx']
    · obtain ⟨a, ha⟩ := h2 (mat h₁⁻¹ *ᵥ z)
      refine ⟨a, ?_⟩
      have e1 : mat m⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, hιi, ← Matrix.mulVec_mulVec]
      have e2 : mat m *ᵥ (incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z)) = incM F H.ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat h₁), hh, Matrix.one_mulVec]
      rw [FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add,
        Matrix.mulVec_smul, hx', e2]
  | one => simp
  | mul x y _ _ hx hy =>
    have := mul_mem hx hy
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have := inv_mem hx
    simpa [mul_assoc] using this

end GlobalTheory.LeviHC
