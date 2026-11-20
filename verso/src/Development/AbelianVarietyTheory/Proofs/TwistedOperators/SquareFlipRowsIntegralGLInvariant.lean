import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPrimFrameGlMulIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqCharStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumQuotientIntegerMatricesInvariantIntegralGLMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.SquareFlipRows

/- English proof (translation)
Introduce `k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ u hu X`. Establish `hM : (invT u⁻¹).val = u.valᵀ` using `by rw [invT_val, inv_inv]`. Establish `hMK : invT u⁻¹ ∈ KO k A` using `invT_mem_KO (inv_mem hu)`. Establish `hdep : HasDepth ϖ e (blockLat ϖ e (Assignment.two.block D₁ D₂)) (phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ))`. Establish `h1` using `(FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e (Assignment.one.block D₁ D₂) hϖ hψ).1 Φ hΦ`.

Establish `h2` using `@FrameDepth.hasDepth_phiA k _ _ _ _ _ _ A A' (D₁ ⊕ D₂) _ _ _ _ _ _ μ (by assumption) σ ν ϖ e (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν h1`. Rewrite using `[← compl_block_one, ← latA_blockLat]`. Conclude with `h2`. Establish `triv : ∀ y ∈ 𝒪[k], ψ y = 1` using `fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))`. Establish `hφu : ∀ Y, (ν (gdet u) : ℂ) * phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) (u.valᵀ * Y) = phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) Y`.

Introduce `Y`. Rewrite using `[phiA, phiA, ← hM, GlobalTheory.PrimFrameLeft.isPrimFrame_gl_mul_iff _ _ hMK]`. Distinguish the cases in `hY : IsPrimFrame (latA ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))) Y`. Rewrite using `[if_pos hY, if_pos hY]`. Take `⟨h, rfl⟩` from `(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hY.1`.

Rewrite using `[hM]`. Conclude with `GlobalTheory.T.frameTestFunction_transpose_integralGL_mul_eq_char μ σ ν _ u hu h`. Rewrite using `[if_neg hY, if_neg hY, mul_zero]`. Establish `hb : ∀ (Q : D₁ ⊕ D₂ → Prop), (∀ j ∈ Assignment.two.block D₁ D₂, Q j) ↔ ∀ c, Q (Sum.inr c)`. Introduce `Q`.

Use `⟨fun h c => h _ (by simp [Assignment.block]), fun h j hj => ?_⟩` and prove the remaining obligations. Consider the cases of `j with`. Consider the case `inl c => simp [Assignment.block] at hj`. Consider the case `inr c => exact h c`. Use `set X' : Matrix A (D₁ ⊕ D₂) k := fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂) with hX'`.

Establish `hcond : (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X' i j ∈ 𝒪[k]) ↔ (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k])`. Simplify using `only [hb]`. Use `mul_mul_mem_matLat_iff (inv_mem hu) (one_mem (KO k D₂)) X.toCols₂` as an intermediate fact. Rewrite `this` using `[mem_matLat_stdLat, mem_matLat_stdLat, Units.val_one, Matrix.mul_one]`. Simplify `this` using `[hX', Matrix.toCols₂]`.

Establish `hset : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k, setCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) = u.valᵀ * setCols (Assignment.two.block D₁ D₂) X Z`. Introduce `Z`. Rewrite using `[hM]`. Use extensionality with `i j`. Break down `j with c | c` into its components or cases.

Simplify using `[setCols, Assignment.block, hX', Matrix.mul_apply, Matrix.toCols₁]`. Apply the tactic sequence `simp [setCols, Assignment.block, Matrix.mul_apply] first | rfl | exact Matrix.mul_apply | (erw [Matrix.mul_apply]; simp)`. Establish `hsub : X'.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) = (u⁻¹).val * X.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂)`. Use extensionality with `i ⟨j, hj⟩`. Break down `j with c | c` into its components or cases.

Simplify using `[Assignment.block] at hj`. Simplify using `[hX', Matrix.mul_apply, Matrix.toCols₂]`. Establish `hpair : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k, pairCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) = pairCols (Assignment.two.block D₁ D₂) X Z`. Introduce `Z`. Rewrite using `[pairCols_eq_trace, pairCols_eq_trace, hsub, hM, transpose_mul, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul]`.

Unfold `squareFlip`. Rewrite using `[compl_block_one, invFourierSum_inv_apply, invFourierSum_inv_apply]`. Distinguish the cases in `hX : ∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]`. Rewrite using `[if_pos hX, if_pos (hcond.2 hX)] set φ := phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)`. Establish `hg : ∀ Z Z' : Matrix A (Assignment.two.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) → (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) (Z + Z') = (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assig …`.

Introduce `Z Z' hZ'`. Establish `e1 : setCols (Assignment.two.block D₁ D₂) X' (Z + Z') = setCols (Assignment.two.block D₁ D₂) X' Z + setCols (Assignment.two.block D₁ D₂) 0 Z'`. Apply the tactic sequence `ext i j; by_cases h : j ∈ Assignment.two.block D₁ D₂ <;> simp [setCols, h]`. Establish `e2 : pairCols (Assignment.two.block D₁ D₂) X' (Z + Z') = pairCols (Assignment.two.block D₁ D₂) X' Z + pairCols (Assignment.two.block D₁ D₂) X' Z'`. Simplify using `[pairCols, add_mul, Finset.sum_add_distrib]`.

Establish `e3 : pairCols (Assignment.two.block D₁ D₂) X' Z' ∈ 𝒪[k]` using `Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (hZ' i j) (hcond.2 hX i j j.2)`. Simplify using `only`. Rewrite using `[e1, e2, hdep.2, AddChar.map_add_eq_mul, triv _ e3, mul_one]`. Use `FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩` and prove the remaining obligations. Simplify `hZ' i ⟨j, hj⟩` using `[setCols, hj]`.

Simplify using `[setCols, hj]`. Establish `key` using `GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left ϖ e hϖ (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) hg (invT u⁻¹) hMK`. Use `beta_reduce at key`. Rewrite using `[← key, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations.

Rewrite using `[hset, hpair, ← mul_assoc, hφu]`. Rewrite using `[if_neg hX, if_neg (mt hcond.1 hX), mul_zero]`.
-/
theorem squareFlip_one_rows : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ u ∈ KO k A, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      (ν (gdet u) : ℂ) * squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ
          (fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂)) =
        squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ X := by

  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ u hu X
  have hM : (invT u⁻¹).val = u.valᵀ := by rw [invT_val, inv_inv]
  have hMK : invT u⁻¹ ∈ KO k A := invT_mem_KO (inv_mem hu)
  have hdep : HasDepth ϖ e (blockLat ϖ e (Assignment.two.block D₁ D₂))
      (phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    have h1 := (FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e (Assignment.one.block D₁ D₂) hϖ hψ).1 Φ hΦ
    have h2 := @FrameDepth.hasDepth_phiA k _ _ _ _ _ _ A A' (D₁ ⊕ D₂) _ _ _ _ _ _ μ (by assumption) σ ν ϖ e
      (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν h1
    rw [← compl_block_one, ← latA_blockLat]; exact h2
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hφu : ∀ Y, (ν (gdet u) : ℂ) * phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) (u.valᵀ * Y) =
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) Y := by
    intro Y
    classical
    rw [phiA, phiA, ← hM, GlobalTheory.PrimFrameLeft.isPrimFrame_gl_mul_iff _ _ hMK]
    by_cases hY : IsPrimFrame (latA ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))) Y
    · rw [if_pos hY, if_pos hY]
      obtain ⟨h, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hY.1
      rw [hM]
      exact GlobalTheory.T.frameTestFunction_transpose_integralGL_mul_eq_char μ σ ν _ u hu h
    · rw [if_neg hY, if_neg hY, mul_zero]
  have hb : ∀ (Q : D₁ ⊕ D₂ → Prop), (∀ j ∈ Assignment.two.block D₁ D₂, Q j) ↔ ∀ c, Q (Sum.inr c) := by
    intro Q
    refine ⟨fun h c => h _ (by simp [Assignment.block]), fun h j hj => ?_⟩
    cases j with
    | inl c => simp [Assignment.block] at hj
    | inr c => exact h c
  set X' : Matrix A (D₁ ⊕ D₂) k := fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂) with hX'
  have hcond : (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X' i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]) := by
    simp only [hb]
    have := mul_mul_mem_matLat_iff (inv_mem hu) (one_mem (KO k D₂)) X.toCols₂
    rw [mem_matLat_stdLat, mem_matLat_stdLat, Units.val_one, Matrix.mul_one] at this
    simpa [hX', Matrix.toCols₂] using this
  have hset : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      setCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) =
        u.valᵀ * setCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [hM]
    ext i j
    rcases j with c | c
    · simp [setCols, Assignment.block, hX', Matrix.mul_apply, Matrix.toCols₁]
    · simp [setCols, Assignment.block, Matrix.mul_apply]
      first | rfl | exact Matrix.mul_apply | (erw [Matrix.mul_apply]; simp)
  have hsub : X'.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) =
      (u⁻¹).val * X.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) := by
    ext i ⟨j, hj⟩
    rcases j with c | c
    · simp [Assignment.block] at hj
    · simp [hX', Matrix.mul_apply, Matrix.toCols₂]
  have hpair : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      pairCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) = pairCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [pairCols_eq_trace, pairCols_eq_trace, hsub, hM, transpose_mul, ← Matrix.mul_assoc, trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul]
  unfold squareFlip
  rw [compl_block_one, invFourierSum_inv_apply, invFourierSum_inv_apply]
  by_cases hX : ∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]
  · rw [if_pos hX, if_pos (hcond.2 hX)]
    set φ := phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
    have hg : ∀ Z Z' : Matrix A (Assignment.two.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) →
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) (Z + Z') =
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) Z := by
      intro Z Z' hZ'
      have e1 : setCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          setCols (Assignment.two.block D₁ D₂) X' Z + setCols (Assignment.two.block D₁ D₂) 0 Z' := by
        ext i j; by_cases h : j ∈ Assignment.two.block D₁ D₂ <;> simp [setCols, h]
      have e2 : pairCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          pairCols (Assignment.two.block D₁ D₂) X' Z + pairCols (Assignment.two.block D₁ D₂) X' Z' := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      have e3 : pairCols (Assignment.two.block D₁ D₂) X' Z' ∈ 𝒪[k] :=
        Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (hZ' i j) (hcond.2 hX i j j.2)
      simp only
      rw [e1, e2, hdep.2, AddChar.map_add_eq_mul, triv _ e3, mul_one]
      refine FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
      · simpa [setCols, hj] using hZ' i ⟨j, hj⟩
      · simp [setCols, hj]
    have key := GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left ϖ e hϖ (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) hg (invT u⁻¹) hMK
    beta_reduce at key
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hset, hpair, ← mul_assoc, hφu]
  · rw [if_neg hX, if_neg (mt hcond.1 hX), mul_zero]

end GlobalTheory.SquareFlipRows
