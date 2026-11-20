import Mathlib

open ValuativeRel MeasureTheory Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.LocalModule

/- English proof (translation)
Introduce `k _ _ _ _ u hu`. Use `borelize k`. Establish `hsc : IsCompact {x : k | valuation k x ≤ 1}` using `IsNonarchimedeanLocalField.isCompact_closedBall k 1`. Establish `hso : IsOpen {x : k | valuation k x ≤ 1}` using `Valuation.isOpen_integer (v := valuation k)`. Establish `hus : u • {x : k | valuation k x ≤ 1} = {x : k | valuation k x ≤ 1}`.

Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `only [Set.mem_ofPred_eq, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_mul]`. Establish `h0 : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ 0` using `(hso.measure_pos Measure.addHaar ⟨0, by simp⟩).ne'`. Establish `hfin : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ ⊤` using `hsc.measure_lt_top.ne`.

Conclude with `distribHaarChar_eq_of_measure_smul_eq_mul h0 hfin (by rw [hus, ENNReal.coe_one, one_mul])`.
-/
theorem distribHaarChar_eq_one_of_valuation_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (u : kˣ), valuation k (u : k) = 1 → distribHaarChar k u = 1 := by
  intro k _ _ _ _ u hu
  borelize k
  have hsc : IsCompact {x : k | valuation k x ≤ 1} :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hso : IsOpen {x : k | valuation k x ≤ 1} :=
    Valuation.isOpen_integer (v := valuation k)
  have hus : u • {x : k | valuation k x ≤ 1} = {x : k | valuation k x ≤ 1} := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_ofPred_eq, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hu, inv_one, one_mul]
  have h0 : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ 0 :=
    (hso.measure_pos Measure.addHaar ⟨0, by simp⟩).ne'
  have hfin : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ ⊤ := hsc.measure_lt_top.ne
  exact distribHaarChar_eq_of_measure_smul_eq_mul h0 hfin (by rw [hus, ENNReal.coe_one, one_mul])

end GlobalTheory.CompanionTheory.LocalModule
