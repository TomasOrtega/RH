import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

/- English proof (translation)
Establish `hJ` using `GlobalTheory.DatumEigen.int_of_mem hu`. Establish `hl` using `(mem_parahoric.1 hu).2`. Take `⟨hyi, hyd, hyl⟩` from `hy`. Establish `hprod : ∀ i l, (u.val * y) i l ∈ 𝒪[k]` using `fun i l => by`. Rewrite using `[mul_apply]`.

Conclude with `sum_mem fun m _ => mul_mem (hJ i m) (hyi m l)`. Establish `hcong : valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1`. Rewrite using `[← det_mul]`. Use `GlobalTheory.DatumEigen.val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)` and prove the remaining obligations. Rewrite using `[mul_apply]`.

Conclude with `sum_mem fun m _ => mul_mem (hJ _ _) (hyi _ _)`. Simplify using `only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]`. Conclude with `Valuation.map_sum_lt _ one_ne_zero fun m _ => GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)`. Establish `hd1 : valuation k (u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) = 1`. Rewrite using `[map_mul, hyd, mul_one, (GlobalTheory.DatumEigen.val_det_blocks hu).1]`.

Use `⟨⟨hprod, ?_, ?_⟩, hcong⟩` and prove the remaining obligations. Rewrite using `[← hd1]`. Use `Valuation.map_eq_of_sub_lt _ ?_` and prove the remaining obligations. Rewrite using `[hd1]`. Conclude with `hcong`.

Introduce `e a`. Rewrite using `[mul_apply, Fintype.sum_sum_type]`. Use `Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_) (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `GlobalTheory.DatumEigen.val_mul_lt (hyi _ _) (hl _ _)`.

Conclude with `GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)`.
-/
theorem inSupp_mul_left {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {u : GL (A ⊕ D') k}
    (hu : u ∈ parahoric k A D') : InSupp (u.val * y) ∧
      valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
  have hJ := GlobalTheory.DatumEigen.int_of_mem hu
  have hl := (mem_parahoric.1 hu).2
  obtain ⟨hyi, hyd, hyl⟩ := hy
  have hprod : ∀ i l, (u.val * y) i l ∈ 𝒪[k] := fun i l => by
    rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hyi m l)
  have hcong : valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine GlobalTheory.DatumEigen.val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hyi _ _)
    · simp only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)
  have hd1 : valuation k (u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hyd, mul_one, (GlobalTheory.DatumEigen.val_det_blocks hu).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact GlobalTheory.DatumEigen.val_mul_lt (hyi _ _) (hl _ _)
    · exact GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
/- English proof (translation)
Establish `hlt : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Rewrite using `[val_torusElt]`. Introduce `i j`. Rewrite using `[diagonal_apply]`. Use `split_ifs`.

Use `show valuation k _ ≤ 1`. Rewrite using `[map_zpow₀]`. Apply the tactic sequence `exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)`. Conclude with `zero_mem _`.
-/
theorem torusElt_indic_int {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D') :
    IsIntM (torusElt k D' ϖ (indic s)).val := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [val_torusElt]
  intro i j
  rw [diagonal_apply]; split_ifs
  · show valuation k _ ≤ 1
    rw [map_zpow₀]
    exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
  · exact zero_mem _

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hy`. Take `⟨a, b, c, e⟩` from `isIntM_toBlocks (show IsIntM y from h1)`. Rewrite using `[fromBlocks_diag_mul]`. Use `⟨⟨isIntM_fromBlocks_iff.2 ⟨a, b, isIntM_mul ht c, isIntM_mul ht e⟩, by simpa using h2, fun i j => ?_⟩, toBlocks_fromBlocks₁₁ _ _ _ _⟩` and prove the remaining obligations. Rewrite using `[fromBlocks_apply₂₁]`.

Conclude with `val_lt_mul ht (fun a b => h3 a b) i j`.
-/
theorem inSupp_diag_mul {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {t : Matrix D' D' k} (ht : IsIntM t) :
    InSupp ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y) ∧
      ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y).toBlocks₁₁ = y.toBlocks₁₁ := by
  obtain ⟨h1, h2, h3⟩ := hy
  obtain ⟨a, b, c, e⟩ := isIntM_toBlocks (show IsIntM y from h1)
  rw [fromBlocks_diag_mul]
  refine ⟨⟨isIntM_fromBlocks_iff.2 ⟨a, b, isIntM_mul ht c, isIntM_mul ht e⟩, by simpa using h2, fun i j => ?_⟩,
    toBlocks_fromBlocks₁₁ _ _ _ _⟩
  rw [fromBlocks_apply₂₁]
  exact val_lt_mul ht (fun a b => h3 a b) i j

open Classical in

/- English proof (translation)
Introduce `k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s j hj d hd x`. Use `set y := ((j * mtor ϖ (indic s))⁻¹).1 * x with hydef`. Use `⟨fun hW => ?_, fun hW => by simp only [datum, dif_neg hW]⟩` and prove the remaining obligations. Use `set T := torusElt k D' ϖ (indic s) with hT`. Establish `hg0 : (mtor (A` using `A) ϖ (indic s)).val = fromBlocks (1 : Matrix A A k) 0 0 T.val := by`.

Rewrite using `[mtor_eq_dg, val_dg]`. Establish `hx : x = j.val * ((mtor (A` using `A) ϖ (indic s)).val * y) := by`. Rewrite using `[hydef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Take `⟨hg, hg11⟩` from `inSupp_diag_mul hW (torusElt_indic_int hϖ s)`. Rewrite `hg`, `hg11` using `[← hg0]`.

Take `⟨hs, hc⟩` from `inSupp_mul_left hg hj`. Rewrite `hc` using `[← hx, hg11]`. Rewrite `hs` using `[← hx]`. Take `⟨h11, h22⟩` from `GlobalTheory.DatumEigen.val_det_blocks hj`. Establish `n11 : j.val.toBlocks₁₁.det ≠ 0` using `fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11`.

Use `set u₁ : kˣ := Units.mk0 _ n11 with hu₁`. Establish `hdv : valuation k (d : k) = 1` using `by rw [hd]; exact h22`. Establish `t1 : ξ (GeneralLinearGroup.det j) = ξ (u₁ * d)`. Use `GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, hd, GeneralLinearGroup.val_det_apply]`.

Conclude with `GlobalTheory.DatumEigen.det_cong hj`. Establish `t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hW.det_ne * u₁)`. Use `GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hW.2.1, one_mul]; exact h11) ?_` and prove the remaining obligations. Use `show valuation k (x.toBlocks₁₁.det - y.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1`. Rewrite using `[mul_comm (y.toBlocks₁₁.det)]`.

Conclude with `hc`. Simplify using `only [datum, dif_pos hs, dif_pos hW]`. Rewrite using `[t1, t2, ← Units.val_mul]`. Use `congr 1`. Simplify using `only [map_mul]`.

Use `group`.
-/
theorem coset_term : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, (InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → ((ξ d * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = datum ξ x) ∧ (¬ InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = 0) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s j hj d hd x
  set y := ((j * mtor ϖ (indic s))⁻¹).1 * x with hydef
  refine ⟨fun hW => ?_, fun hW => by simp only [datum, dif_neg hW]⟩
  set T := torusElt k D' ϖ (indic s) with hT
  have hg0 : (mtor (A := A) ϖ (indic s)).val = fromBlocks (1 : Matrix A A k) 0 0 T.val := by
    rw [mtor_eq_dg, val_dg]
  have hx : x = j.val * ((mtor (A := A) ϖ (indic s)).val * y) := by
    rw [hydef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  obtain ⟨hg, hg11⟩ := inSupp_diag_mul hW (torusElt_indic_int hϖ s)
  rw [← hg0] at hg hg11
  obtain ⟨hs, hc⟩ := inSupp_mul_left hg hj
  rw [← hx, hg11] at hc
  rw [← hx] at hs
  obtain ⟨h11, h22⟩ := GlobalTheory.DatumEigen.val_det_blocks hj
  have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  set u₁ : kˣ := Units.mk0 _ n11 with hu₁
  have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
  have t1 : ξ (GeneralLinearGroup.det j) = ξ (u₁ * d) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
    rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.DatumEigen.det_cong hj
  have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hW.det_ne * u₁) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hW.2.1, one_mul]; exact h11) ?_
    show valuation k (x.toBlocks₁₁.det - y.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1
    rw [mul_comm (y.toBlocks₁₁.det)]
    exact hc
  simp only [datum, dif_pos hs, dif_pos hW]
  rw [t1, t2, ← Units.val_mul]
  congr 1
  simp only [map_mul]
  group

end GlobalTheory.ParHeckeTarget
