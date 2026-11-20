import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftResMulSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.FrameSubst

/- English proof (translation)
Establish `hG'` using `((mem_KO_iff G).1 hG).1`. Simplify using `only [vecMul, dotProduct]`. Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' (hx i) ((Valuation.mem_integer_iff _ _).1 (hG' i j))).trans (by rw [mul_one])`.
-/
theorem vecMul_bound {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k)
    (hx : ∀ j, valuation k (x j) ≤ valuation k c) (j : n) : valuation k ((x ᵥ* G.val) j) ≤ valuation k c := by
  have hG' := ((mem_KO_iff G).1 hG).1
  simp only [vecMul, dotProduct]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hx i) ((Valuation.mem_integer_iff _ _).1 (hG' i j))).trans (by rw [mul_one])

/- English proof (translation)
Use `⟨fun h j => ?_, fun h => vecMul_bound hG c x h⟩` and prove the remaining obligations. Use `vecMul_bound ((KO k n).inv_mem hG) c _ h j` as an intermediate fact. Rewrite `this` using `[vecMul_vecMul, Units.mul_inv, vecMul_one]`. Then use the resulting hypothesis.
-/
theorem vecMul_bound_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k) :
    (∀ j, valuation k ((x ᵥ* G.val) j) ≤ valuation k c) ↔ ∀ j, valuation k (x j) ≤ valuation k c := by
  refine ⟨fun h j => ?_, fun h => vecMul_bound hG c x h⟩
  have := vecMul_bound ((KO k n).inv_mem hG) c _ h j
  rwa [vecMul_vecMul, Units.mul_inv, vecMul_one] at this

/- English proof (translation)
Introduce `x`. Establish `hl : ∀ j, (x ᵥ* G.val) (Sum.inl j) = ((fun i => x (Sum.inl i)) ᵥ* G₁.val) j` using `fun j => by`. Simplify using `[hG, vecMul, dotProduct, Fintype.sum_sum_type]`. Establish `hr : ∀ j, (x ᵥ* G.val) (Sum.inr j) = ((fun i => x (Sum.inr i)) ᵥ* G₂.val) j` using `fun j => by`. Simplify using `[hG, vecMul, dotProduct, Fintype.sum_sum_type]`.

Rewrite using `[mem_blockLat_two, mem_blockLat_two]`. Simplify using `only [hl, hr]`. Use `and_congr ?_ (vecMul_bound_iff h₂ _ _)` and prove the remaining obligations. Use `vecMul_bound_iff h₁ 1 (fun i => x (Sum.inl i))` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_glLat_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D₁ D₂ : Type} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ϖ : kˣ) (e : ℕ)
    {G₁ : GL D₁ k} {G₂ : GL D₂ k} (h₁ : G₁ ∈ KO k D₁) (h₂ : G₂ ∈ KO k D₂) (G : GL (D₁ ⊕ D₂) k)
    (hG : G.val = fromBlocks G₁.val 0 0 G₂.val) : G ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) := by
  intro x
  have hl : ∀ j, (x ᵥ* G.val) (Sum.inl j) = ((fun i => x (Sum.inl i)) ᵥ* G₁.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  have hr : ∀ j, (x ᵥ* G.val) (Sum.inr j) = ((fun i => x (Sum.inr i)) ᵥ* G₂.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  rw [mem_blockLat_two, mem_blockLat_two]
  simp only [hl, hr]
  refine and_congr ?_ (vecMul_bound_iff h₂ _ _)
  have := vecMul_bound_iff h₁ 1 (fun i => x (Sum.inl i))
  simpa using this

/- English proof (translation)
Use `⟨fun h => ?_, fun h => Model.isPrimFrame_mul h g hg⟩` and prove the remaining obligations. Use `Model.isPrimFrame_mul h g⁻¹ ((glLat Λ).inv_mem hg)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem isPrimFrame_mul_glLat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] {Λ : Submodule 𝒪[k] (D → k)} (g : GL D k)
    (hg : g ∈ glLat Λ) (X : Matrix A D k) : IsPrimFrame Λ (X * g.val) ↔ IsPrimFrame Λ X := by
  refine ⟨fun h => ?_, fun h => Model.isPrimFrame_mul h g hg⟩
  have := Model.isPrimFrame_mul h g⁻¹ ((glLat Λ).inv_mem hg)
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

/- English proof (translation)
Distinguish the cases in `hX : ∃ h : GL D k, X = X0 k σ * (invT h).val`. Take `⟨h, rfl⟩` from `hX`. Establish `e1 : X0 k σ * (invT h).val * (invT H).val = X0 k σ * (invT (h * H)).val`. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc]`. Establish `e2 : smallF μ ν (fun Y => Ψ (Y * H.val)) (Y0 k σ * h.val) = smallF μ ν Ψ (Y0 k σ * (h * H).val)`.

Unfold `smallF`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Rewrite using `[e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, gdet_mul, map_mul, apow_mul, hH, Units.val_mul, Units.val_inv_eq_inv_val]`.

Establish `hn : (ν (gdet H) : ℂ) ≠ 0` using `Units.ne_zero _`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hX' : ¬ ∃ h : GL D k, X * (invT H).val = X0 k σ * (invT h).val`.

Introduce and unpack `⟨h, hh⟩`. Apply `hX` to reduce the goal to its premises. Use `⟨h * H⁻¹, ?_⟩` and prove the remaining obligations. Use `congrArg (· * ((invT H)⁻¹).val) hh` as an intermediate fact. Simplify using `only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this`.

Rewrite using `[this, map_mul, map_inv, Units.val_mul]`. Rewrite using `[fFun, dif_neg hX, fFun, dif_neg hX', mul_zero]`.
-/
theorem fFun_comp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ)
    (H : GL D k) (hH : apow (gdet H) ((Fintype.card D : ℂ) / 2) = 1) (X : Matrix A D k) :
    fFun μ σ ν (fun Y => Ψ (Y * H.val)) X = (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) * fFun μ σ ν Ψ (X * (invT H).val) := by
  classical
  by_cases hX : ∃ h : GL D k, X = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have e1 : X0 k σ * (invT h).val * (invT H).val = X0 k σ * (invT (h * H)).val := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc]
    have e2 : smallF μ ν (fun Y => Ψ (Y * H.val)) (Y0 k σ * h.val) = smallF μ ν Ψ (Y0 k σ * (h * H).val) := by
      unfold smallF; congr 1; funext g; simp only [Units.val_mul, Matrix.mul_assoc]
    rw [e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, gdet_mul, map_mul, apow_mul, hH, Units.val_mul,
      Units.val_inv_eq_inv_val]
    have hn : (ν (gdet H) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    simp only [Units.val_mul]
    ring
  · have hX' : ¬ ∃ h : GL D k, X * (invT H).val = X0 k σ * (invT h).val := by
      rintro ⟨h, hh⟩
      apply hX
      refine ⟨h * H⁻¹, ?_⟩
      have := congrArg (· * ((invT H)⁻¹).val) hh
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
      rw [this, map_mul, map_inv, Units.val_mul]
    rw [fFun, dif_neg hX, fFun, dif_neg hX', mul_zero]

/- English proof (translation)
Introduce `k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ν ϖ e Ψ M₁ hM₁ M₂ hM₂ X`. Set `H : GL (D₁ ⊕ D₂) k` to `⟨fromBlocks (invT M₁).val 0 0 M₂.val, fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩`. Establish `hHinv : (invT H).val = fromBlocks M₁.val 0 0 (invT M₂).val`. Rewrite using `[invT_val]`. Use `show (fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val)ᵀ = _`.

Rewrite using `[fromBlocks_transpose, invT_inv_val, transpose_transpose, transpose_zero, transpose_zero, ← invT_val]`. Establish `hdet : gdet H = (gdet M₁)⁻¹ * gdet M₂`. Rewrite using `[← gdet_invT]`. Use `ext`. Simplify using `only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]`.

Conclude with `det_fromBlocks_zero₁₂ _ _ _`. Establish `habs : apow (gdet H) ((Fintype.card (D₁ ⊕ D₂) : ℂ) / 2) = 1`. Rewrite using `[hdet, apow_mul, apow_inv, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₁), apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₂), one_mul]`. Establish `hfac : (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) = (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ)`. Rewrite using `[hdet, map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]`.

Establish `hgl : invT H ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂))` using `mem_glLat_fromBlocks ϖ e hM₁ (invT_mem_KO hM₂) _ hHinv`. Use `show phiA μ σ ν ϖ e _ (fun Y => Ψ (Y * H.val)) X = _`. Rewrite using `[← hHinv]`. Unfold `phiA`. Rewrite using `[latA_blockLat, compl_block_one, isPrimFrame_mul_glLat (invT H) hgl]`.

Use `split_ifs`. Rewrite using `[fFun_comp_mul μ σ ν Ψ H habs X, hfac]`. Simplify using the standard rewrite rules.
-/
theorem phiA_blockSubst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' (D₁ ⊕ D₂) k → ℂ), ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂,
    ∀ X : Matrix A (D₁ ⊕ D₂) k,
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
          (fun Y => Ψ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) Ψ (X * fromBlocks M₁.val 0 0 (invT M₂).val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ν ϖ e Ψ M₁ hM₁ M₂ hM₂ X
  classical
  let H : GL (D₁ ⊕ D₂) k := ⟨fromBlocks (invT M₁).val 0 0 M₂.val, fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  have hHinv : (invT H).val = fromBlocks M₁.val 0 0 (invT M₂).val := by
    rw [invT_val]
    show (fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val)ᵀ = _
    rw [fromBlocks_transpose, invT_inv_val, transpose_transpose, transpose_zero, transpose_zero, ← invT_val]
  have hdet : gdet H = (gdet M₁)⁻¹ * gdet M₂ := by
    rw [← gdet_invT]
    ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_fromBlocks_zero₁₂ _ _ _
  have habs : apow (gdet H) ((Fintype.card (D₁ ⊕ D₂) : ℂ) / 2) = 1 := by
    rw [hdet, apow_mul, apow_inv, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₁),
      apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₂), one_mul]
  have hfac : (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) = (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) := by
    rw [hdet, map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
  have hgl : invT H ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) :=
    mem_glLat_fromBlocks ϖ e hM₁ (invT_mem_KO hM₂) _ hHinv
  show phiA μ σ ν ϖ e _ (fun Y => Ψ (Y * H.val)) X = _
  rw [← hHinv]
  unfold phiA
  rw [latA_blockLat, compl_block_one, isPrimFrame_mul_glLat (invT H) hgl]
  split_ifs
  · rw [fFun_comp_mul μ σ ν Ψ H habs X, hfac]
  · simp

end GlobalTheory.FrameSubst
