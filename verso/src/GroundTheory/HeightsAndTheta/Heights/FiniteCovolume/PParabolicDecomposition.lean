import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `M x₀ hx₀ hiso g`. Establish `hz : ∀ w, vecAt v x₀ w ≠ 0` using `h₅ x₀ hx₀`. Establish `hzi : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0` using `fun w => by`. Rewrite using `[← h₂, hiso, map_zero]`. Establish `hzi' : ∀ w, star (invApply g (vecAt v x₀) w) ⬝ᵥ (gramAt h v w *ᵥ invApply g (vecAt v x₀) w) = 0` using `fun w => by`.

Rewrite using `[h₄, hzi]`. Establish `hginv : ∀ w, (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)` using `fun w => rfl`. Establish `hz' : ∀ w, invApply g (vecAt v x₀) w ≠ 0`. Introduce `w hw`. Apply `hz w` to reduce the goal to its premises.

Establish `e : ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ invApply g (vecAt v x₀) w = vecAt v x₀ w`. Rewrite using `[invApply, hginv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[← e, hw, Matrix.mulVec_zero]`. Establish `hmaj : ∀ w, IsMajorantOf (gramAt h v w) (M.P w)` using `fun w => ⟨M.posDef w, (h₃ w).1, (h₃ w).2, M.siegel w⟩`. Use `choose k hkH hkP c hc using fun w => h₁ _ _ (hmaj w) _ _ (hz w) (hz' w) (hzi w) (hzi' w)`.

Establish `hkA : k ∈ archUnitary h v` using `(Subgroup.mem_pi _).2 fun w _ => hkH w`. Use `set kk : archUnitary h v := ⟨k, hkA⟩ with hkk`. Establish `hkS : kk ∈ M.stab`. Rewrite using `[Majorant.stab, Subgroup.mem_subgroupOf]`. Conclude with `(Subgroup.mem_pi _).2 fun w _ => hkP w`.

Use `⟨g * kk⁻¹, kk, hkS, by group, fun w => ⟨(c w)⁻¹, ?_⟩⟩` and prove the remaining obligations. Establish `hcw : c w ≠ 0`. Introduce `h0`. Apply `hz' w` to reduce the goal to its premises. Establish `e` using `congrArg (fun y => (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y) (hc w)`.

Simplify using `only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at e`. Conclude with `e`. Establish `hk : (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = (c w)⁻¹ • invApply g (vecAt v x₀) w`. Establish `e` using `congrArg (fun y => (c w)⁻¹ • ((((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y)) (hc w)`. Simplify using `only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hcw, one_smul] at e`.

Conclude with `e.symm`. Establish `hp : (((g * kk⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) * (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)` using `rfl`. Rewrite using `[hp, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, invApply, hginv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem ParabolicDecomposition.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : KTransitive.Statement ι) (h₂ : HermAtPlace.Statement h v)
    (h₃ : GramAtData.Statement h v) (h₄ : ArchInvariant.Statement h v)
    (h₅ : VecAtNeZero.Statement v) : ParabolicDecomposition.Statement h v := by
  intro M x₀ hx₀ hiso g
  have hz : ∀ w, vecAt v x₀ w ≠ 0 := h₅ x₀ hx₀
  have hzi : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← h₂, hiso, map_zero]
  have hzi' : ∀ w, star (invApply g (vecAt v x₀) w) ⬝ᵥ
      (gramAt h v w *ᵥ invApply g (vecAt v x₀) w) = 0 := fun w => by
    rw [h₄, hzi]

  have hginv : ∀ w, (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := fun w => rfl
  have hz' : ∀ w, invApply g (vecAt v x₀) w ≠ 0 := by
    intro w hw
    apply hz w
    have e : ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ invApply g (vecAt v x₀) w =
        vecAt v x₀ w := by
      rw [invApply, hginv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← e, hw, Matrix.mulVec_zero]
  have hmaj : ∀ w, IsMajorantOf (gramAt h v w) (M.P w) := fun w =>
    ⟨M.posDef w, (h₃ w).1, (h₃ w).2, M.siegel w⟩
  choose k hkH hkP c hc using fun w =>
    h₁ _ _ (hmaj w) _ _ (hz w) (hz' w) (hzi w) (hzi' w)
  have hkA : k ∈ archUnitary h v := (Subgroup.mem_pi _).2 fun w _ => hkH w
  set kk : archUnitary h v := ⟨k, hkA⟩ with hkk
  have hkS : kk ∈ M.stab := by
    rw [Majorant.stab, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_pi _).2 fun w _ => hkP w
  refine ⟨g * kk⁻¹, kk, hkS, by group, fun w => ⟨(c w)⁻¹, ?_⟩⟩
  have hcw : c w ≠ 0 := by
    intro h0
    apply hz' w
    have e := congrArg (fun y => (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at e
    exact e

  have hk : (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      (c w)⁻¹ • invApply g (vecAt v x₀) w := by
    have e := congrArg (fun y => (c w)⁻¹ • ((((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y)) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hcw, one_smul] at e
    exact e.symm
  have hp : (((g * kk⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) * (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := rfl
  rw [hp, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, invApply, hginv, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
