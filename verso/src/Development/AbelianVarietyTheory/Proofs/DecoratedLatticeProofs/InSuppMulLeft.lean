import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.DatumEigenLeft

open GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

omit [Fintype D] [DecidableEq D] in

/- English proof (translation)
Establish `hJ` using `int_of_mem hj`. Establish `hl` using `(mem_parahoric.1 hj).2`. Take `⟨hxi, hxd, hxl⟩` from `hx`. Establish `hprod : ∀ i l, (j.val * x) i l ∈ 𝒪[k]` using `fun i l => by`. Rewrite using `[mul_apply]`.

Conclude with `sum_mem fun m _ => mul_mem (hJ i m) (hxi m l)`. Establish `hcong : valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1`. Rewrite using `[← det_mul]`. Use `val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)` and prove the remaining obligations. Rewrite using `[mul_apply]`.

Conclude with `sum_mem fun m _ => mul_mem (hJ _ _) (hxi _ _)`. Simplify using `only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]`. Conclude with `Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hJ _ _) (hxl _ _)`. Establish `hd1 : valuation k (j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) = 1`. Rewrite using `[map_mul, hxd, mul_one, (val_det_blocks hj).1]`.

Use `⟨⟨hprod, ?_, ?_⟩, hcong⟩` and prove the remaining obligations. Rewrite using `[← hd1]`. Use `Valuation.map_eq_of_sub_lt _ ?_` and prove the remaining obligations. Rewrite using `[hd1]`. Conclude with `hcong`.

Introduce `e a`. Rewrite using `[mul_apply, Fintype.sum_sum_type]`. Use `Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_) (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `val_mul_lt (hxi _ _) (hl _ _)`.

Conclude with `val_mul_lt (hJ _ _) (hxl _ _)`.
-/
theorem inSupp_mul_left {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D') k}
    (hj : j ∈ parahoric k A D') : InSupp (j.val * x) ∧
      valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (j.val * x) i l ∈ 𝒪[k] := fun i l => by
    rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hxi m l)
  have hcong : valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hxi _ _)
    · simp only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hJ _ _) (hxl _ _)
  have hd1 : valuation k (j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, mul_one, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hxi _ _) (hl _ _)
    · exact val_mul_lt (hJ _ _) (hxl _ _)

end GlobalTheory.DatumEigenLeft

namespace GlobalTheory.DatumEigenLeft
open GlobalTheory.DatumEigen

/- English proof (translation)
Introduce `k _ _ _ _ A D D' _ _ _ _ _ _ ξ μS μT hξ hμ j hj d hd`. Use function extensionality and compare the values at `x`. Establish `hK` using `(mem_parahoric.1 hj).1`. Establish `hdetv : valuation k (GeneralLinearGroup.det j : k) = 1` using `(nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)`. Establish `hμj : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j)`.

Use `hμ _ hdetv` as an intermediate fact. Rewrite `this` using `[MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]`. Then use the resulting hypothesis. Simplify using `only [omTwo, om, Pi.smul_apply, smul_eq_mul, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, MonoidHom.inv_apply, map_one, inv_one, Units.val_one, one_mul, Real.one_rpow, Complex.ofReal_one, mul_one, inv_inv]`. Rewrite using `[show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one, Units.val_mul, hμj]`. Establish `hT : (μT (GeneralLinearGroup.det j) : ℂ) ≠ 0` using `Units.ne_zero _`.

Establish `e1 : ((ξ (GeneralLinearGroup.det j) : ℂ) * (((μT (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ)) * ((μT (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x)) = (ξ (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x)`. Rewrite using `[Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Establish `hx : x = j.val * ((j⁻¹ : GL (A ⊕ D') k).val * x)`.

Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Generalize the expression as in `(j⁻¹ : GL (A ⊕ D') k).val * x = y at hx ⊢`. Substitute `hx` using the available equality. Unfold `datum`. Take `⟨h11, h22⟩` from `val_det_blocks hj`.

Distinguish the cases in `hy : InSupp y`. Take `⟨hs, hc⟩` from `inSupp_mul_left hy hj`. Establish `n11 : j.val.toBlocks₁₁.det ≠ 0` using `fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11`. Use `set u : kˣ := Units.mk0 _ n11 with hu`. Establish `hdv : valuation k (d : k) = 1` using `by rw [hd]; exact h22`.

Establish `t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d)`. Use `tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, hd, GeneralLinearGroup.val_det_apply]`. Conclude with `det_cong hj`. Establish `t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (u * Units.mk0 _ hy.det_ne)`.

Use `tame_eq hξ (by rw [Units.val_mul, map_mul, hu, Units.val_mk0, Units.val_mk0, hy.2.1, h11, mul_one]) ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mk0, Units.val_mk0]`. Conclude with `hc`. Rewrite using `[dif_pos hs, dif_pos hy, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv, inv_inv, t1, t2, map_mul, map_mul]`. Simplify using `only [Units.val_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hs : ¬ InSupp (j.val * y)` using `fun hs => by`. Use `(inSupp_mul_left hs (inv_mem hj)).1` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Conclude with `hy this`.

Rewrite using `[dif_neg hs, dif_neg hy, mul_zero, mul_zero]`.
-/
theorem omTwo_datum_inv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → ∀ j ∈ parahoric k A D', ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D') (A ⊕ D') k).toBlocks₂₂.det → omTwo μS μT (1 : GL (A ⊕ D) k) j (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) = (ξ d : ℂ) • (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ξ μS μT hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hμ _ hdetv
    rwa [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, MonoidHom.inv_apply,
    map_one, inv_one, Units.val_one, one_mul, Real.one_rpow, Complex.ofReal_one, mul_one, inv_inv]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one, Units.val_mul,
    hμj]
  have hT : (μT (GeneralLinearGroup.det j) : ℂ) ≠ 0 := Units.ne_zero _
  have e1 : ((ξ (GeneralLinearGroup.det j) : ℂ) * (((μT (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ)) *
      ((μT (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x)) =
      (ξ (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [Units.val_inv_eq_inv_val]; field_simp
  rw [e1]
  have hx : x = j.val * ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  generalize (j⁻¹ : GL (A ⊕ D') k).val * x = y at hx ⊢
  subst hx
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hy : InSupp y
  · obtain ⟨hs, hc⟩ := inSupp_mul_left hy hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (u * Units.mk0 _ hy.det_ne) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hu, Units.val_mk0, Units.val_mk0, hy.2.1, h11, mul_one]) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dif_pos hs, dif_pos hy, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv, inv_inv, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul]
    ring
  · have hs : ¬ InSupp (j.val * y) := fun hs => by
      have := (inSupp_mul_left hs (inv_mem hj)).1
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
      exact hy this
    rw [dif_neg hs, dif_neg hy, mul_zero, mul_zero]

end GlobalTheory.DatumEigenLeft
