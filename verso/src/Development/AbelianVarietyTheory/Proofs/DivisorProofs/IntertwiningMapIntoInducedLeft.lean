import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhat
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section

namespace GlobalTheory.KSplitInd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Frames
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

/- English proof (translation)
Use extensionality with `i j`. Take `⟨x, rfl⟩` from `σ.surjective j`. Rewrite using `[frameMatrixFirstColumnBlock_mul_apply, transpose_apply]`. Use `congrFun (congrFun hb x) (Sum.inl i)` as an intermediate fact. Simplify using `only [submatrix_apply] at this`.

Rewrite using `[this]`. Break down `x with l | l` into its components or cases. Simplify using `[X0, Matrix.mul_apply]`. Simplify using `[X0, Matrix.mul_apply]`.
-/
theorem transpose_mul_base_matrix (σ : A ⊕ A' ≃ D) (b : GL D k) (g : GL A k) (d : GL A' k) (N : Matrix A A' k)
    (hb : b.val.submatrix σ σ = fromBlocks g.val N 0 d.val) : g.valᵀ * X0 k σ = X0 k σ * b.valᵀ := by
  ext i j
  obtain ⟨x, rfl⟩ := σ.surjective j
  rw [frameMatrixFirstColumnBlock_mul_apply, transpose_apply]
  have := congrFun (congrFun hb x) (Sum.inl i)
  simp only [submatrix_apply] at this
  rw [this]
  rcases x with l | l
  · simp [X0, Matrix.mul_apply]
  · simp [X0, Matrix.mul_apply]

/- English proof (translation)
Establish `h1 : (invT g).val * g.valᵀ = 1` using `by rw [← invT_inv_val]; exact Units.mul_inv _`. Establish `h2 : b.valᵀ * (invT b).val = 1` using `by rw [← invT_inv_val]; exact Units.inv_mul _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← transpose_mul_base_matrix σ b g d N hb, Matrix.mul_assoc (invT g).val]`. Use `_ = (invT g).val * X0 k σ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem base_matrix_mul_inverse_transpose (σ : A ⊕ A' ≃ D) (b : GL D k) (g : GL A k) (d : GL A' k) (N : Matrix A A' k)
    (hb : b.val.submatrix σ σ = fromBlocks g.val N 0 d.val) : X0 k σ * (invT b).val = (invT g).val * X0 k σ := by
  have h1 : (invT g).val * g.valᵀ = 1 := by rw [← invT_inv_val]; exact Units.mul_inv _
  have h2 : b.valᵀ * (invT b).val = 1 := by rw [← invT_inv_val]; exact Units.inv_mul _
  calc X0 k σ * (invT b).val = (invT g).val * g.valᵀ * X0 k σ * (invT b).val := by rw [h1, Matrix.one_mul]
    _ = (invT g).val * (X0 k σ * b.valᵀ) * (invT b).val := by
        rw [← transpose_mul_base_matrix σ b g d N hb, Matrix.mul_assoc (invT g).val]
    _ = (invT g).val * X0 k σ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show b.val.det = g.val.det * d.val.det`. Rewrite using `[← det_submatrix_equiv_self σ, hb, det_fromBlocks_zero₂₁]`.
-/
theorem gdet_block (σ : A ⊕ A' ≃ D) (b : GL D k) (g : GL A k) (d : GL A' k) (N : Matrix A A' k)
    (hb : b.val.submatrix σ σ = fromBlocks g.val N 0 d.val) : gdet b = gdet g * gdet d := by
  apply Units.ext
  show b.val.det = g.val.det * d.val.det
  rw [← det_submatrix_equiv_self σ, hb, det_fromBlocks_zero₂₁]

/- English proof (translation)
The claim follows from `map_one _`.
-/
theorem gdet_one' : gdet (1 : GL D k) = 1 := map_one _

end Frames

/- English proof (translation)
Use function extensionality and compare the values at `X`. Simplify using `[omA]`.
-/
theorem omA_one_one {a d : ℕ} (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin d) k → ℂ) : omA ν β 1 1 Φ = Φ := by
  funext X; simp [omA]

/- English proof (translation)
Introduce `k _ _ _ _ a a' α β l hβ hl Φ hΦ`. Use `⟨fun b A D N hb h => ?_, ?_⟩` and prove the remaining obligations. Use `set σ := (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) with hσ set φ : Matrix (Fin a) (Fin a) k → ℂ := fun g => omA (α / β) β 1 h Φ (g * X0 k σ) with hφdef`. Establish `hφ : φ ∈ SB _` using `restrict_X0 (omA_mem_SB _ _ _ _ hΦ)`. Establish `hφ' : (fun X => φ ((1 : GL (Fin a) k).val * X * (invT A).val)) ∈ SB _` using `comp_mul_mem_SB 1 (invT A) hφ`.

Establish `e1 : (fun g => omA (α / β) β 1 (b * h) Φ (g * X0 k σ)) = ((β (gdet b) : ℂ) * apow (gdet b) (-(a : ℂ) / 2)) • (fun X => φ ((1 : GL (Fin a) k).val * X * (invT A).val))`. Rewrite using `[← one_mul (1 : GL (Fin a) k), omA_mul]`. Use function extensionality and compare the values at `g`. Use `show (((α / β) (gdet (1 : GL (Fin a) k)))⁻¹ : ℂˣ) * (β (gdet b) : ℂ) * apow (gdet (1 : GL (Fin a) k)) _ * apow (gdet b) _ * omA (α / β) β 1 h Φ (((1 : GL (Fin a) k)⁻¹).val * (g * X0 k σ) * (invT b).val) = _`. Simplify using `only [hφdef, Pi.smul_apply, smul_eq_mul, map_one, inv_one, Units.val_one, Matrix.one_mul, apow_one, mul_one, one_mul, Fintype.card_fin, Matrix.mul_assoc, base_matrix_mul_inverse_transpose σ b A D N hb]`.

Establish `e2` using `hl.2.2 1 (invT A) φ hφ`. Use `show l (fun g => omA (α / β) β 1 (b * h) Φ (g * X0 k σ)) = _ * l φ`. Rewrite using `[e1, hl.2.1 _ _ hφ', ← e2, gdet_block σ b A D N hb, gdet_one', one_mul, gdet_invT, apow_inv, map_mul, apow_mul, MonoidHom.div_apply, map_inv, map_inv]`. Establish `hA : apow (gdet A) ((a' : ℂ) / 2) * apow (gdet A) (-(((a + a' : ℕ) : ℂ) / 2)) = apow (gdet A) (-(a : ℂ) / 2)`. Rewrite using `[← apow_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hαA : (α (gdet A) : ℂ) ≠ 0` using `Units.ne_zero _`. Simplify using `only [Units.val_mul, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]`.

Rewrite using `[← hA]`. Clear the denominators using the available nonvanishing facts. Establish `hO` using `GlobalTheory.OmAStab.isOpen_omA_stab k a (a + a') (α / β) β hβ.1 Φ hΦ`. Establish `h1 : (1 : GL (Fin (a + a')) k) ∈ {h | omA (α / β) β 1 h Φ = Φ}` using `omA_one_one _ _ Φ`. Use `filter_upwards [hO.mem_nhds h1] with u hu h`.

Establish `hu' : omA (α / β) β 1 u Φ = Φ` using `hu`. Rewrite using `[← mapA_omA_right, hu']`.
-/
theorem mapA_mem_indSp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ), IsSmU β →
    IsEqv (α / β) (((a + a' : ℕ) : ℂ) / 2) l → ∀ Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k),
      mapA a' l (α / β) β Φ ∈ indSp a a' α β := by
  intro k _ _ _ _ a a' α β l hβ hl Φ hΦ
  refine ⟨fun b A D N hb h => ?_, ?_⟩
  · set σ := (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) with hσ
    set φ : Matrix (Fin a) (Fin a) k → ℂ := fun g => omA (α / β) β 1 h Φ (g * X0 k σ) with hφdef
    have hφ : φ ∈ SB _ := restrict_X0 (omA_mem_SB _ _ _ _ hΦ)
    have hφ' : (fun X => φ ((1 : GL (Fin a) k).val * X * (invT A).val)) ∈ SB _ := comp_mul_mem_SB 1 (invT A) hφ
    have e1 : (fun g => omA (α / β) β 1 (b * h) Φ (g * X0 k σ)) =
        ((β (gdet b) : ℂ) * apow (gdet b) (-(a : ℂ) / 2)) • (fun X => φ ((1 : GL (Fin a) k).val * X * (invT A).val)) := by
      rw [← one_mul (1 : GL (Fin a) k), omA_mul]
      funext g
      show (((α / β) (gdet (1 : GL (Fin a) k)))⁻¹ : ℂˣ) * (β (gdet b) : ℂ) * apow (gdet (1 : GL (Fin a) k)) _ *
        apow (gdet b) _ * omA (α / β) β 1 h Φ (((1 : GL (Fin a) k)⁻¹).val * (g * X0 k σ) * (invT b).val) = _
      simp only [hφdef, Pi.smul_apply, smul_eq_mul, map_one, inv_one, Units.val_one, Matrix.one_mul, apow_one,
        mul_one, one_mul, Fintype.card_fin, Matrix.mul_assoc, base_matrix_mul_inverse_transpose σ b A D N hb]
    have e2 := hl.2.2 1 (invT A) φ hφ
    show l (fun g => omA (α / β) β 1 (b * h) Φ (g * X0 k σ)) = _ * l φ
    rw [e1, hl.2.1 _ _ hφ', ← e2, gdet_block σ b A D N hb, gdet_one', one_mul, gdet_invT, apow_inv, map_mul,
      apow_mul, MonoidHom.div_apply, map_inv, map_inv]
    have hA : apow (gdet A) ((a' : ℂ) / 2) * apow (gdet A) (-(((a + a' : ℕ) : ℂ) / 2)) = apow (gdet A) (-(a : ℂ) / 2) := by
      rw [← apow_add]; congr 1; push_cast; ring
    have hαA : (α (gdet A) : ℂ) ≠ 0 := Units.ne_zero _
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
    rw [← hA]
    field_simp
  · have hO := GlobalTheory.OmAStab.isOpen_omA_stab k a (a + a') (α / β) β hβ.1 Φ hΦ
    have h1 : (1 : GL (Fin (a + a')) k) ∈ {h | omA (α / β) β 1 h Φ = Φ} := omA_one_one _ _ Φ
    filter_upwards [hO.mem_nhds h1] with u hu h
    have hu' : omA (α / β) β 1 u Φ = Φ := hu
    rw [← mapA_omA_right, hu']

end GlobalTheory.KSplitInd

end
