import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerSquare

/- English proof (translation)
Establish `hcont : Continuous fun x => ker X.Γ φ x y` using `(hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)`. Use `⟨hcont.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `hφ.1.bounded_above_of_compact_support hφ.2`. Establish `hΩ : IsCompact (tsupport φ)` using `hφ.2`. Establish `hbound` using `hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y`.

Establish `hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤` using `hΩ.inv.measure_lt_top.ne`. Establish `hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤` using `(hC X).1 _ (hΩ.inv.mul hΩ) y`. Establish `hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ * cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤` using `ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top`. Rewrite using `[eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]`. Simplify using `only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]`.

Conclude with `hbound.trans_lt hfin`.
-/
theorem memLp_column (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by
  have hcont : Continuous fun x => ker X.Γ φ x y :=
    (hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have hΩ : IsCompact (tsupport φ) := hφ.2
  have hbound := hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y
  have hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤ := hΩ.inv.measure_lt_top.ne
  have hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤ :=
    (hC X).1 _ (hΩ.inv.mul hΩ) y
  have hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ *
      cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact hbound.trans_lt hfin

/- English proof (translation)
Take `⟨-, hcont, -, hadj, hconj, -⟩` from `hK X φ hφ`. Establish `hc : Continuous fun y => ker X.Γ φ x y` using `hcont.comp (continuous_const.prodMk continuous_id)`. Use `(memLp_column hK hC hS X (adj φ) hadj x).of_le hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Rewrite using `[hconj y x, RCLike.norm_conj]`.
-/
theorem memLp_row (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (x : X.G) : MemLp (fun y => ker X.Γ φ x y) 2 X.ν := by
  obtain ⟨-, hcont, -, hadj, hconj, -⟩ := hK X φ hφ
  have hc : Continuous fun y => ker X.Γ φ x y :=
    hcont.comp (continuous_const.prodMk continuous_id)
  refine (memLp_column hK hC hS X (adj φ) hadj x).of_le hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [hconj y x, RCLike.norm_conj]

/- English proof (translation)
Introduce `hK hC hS X φ hφ` and use `⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩`.
-/
theorem kernel_rows_columns_square_integrable : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := fun hK hC hS X φ hφ =>
  ⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩

end GlobalTheory.CompanionTheory.KerSquare
