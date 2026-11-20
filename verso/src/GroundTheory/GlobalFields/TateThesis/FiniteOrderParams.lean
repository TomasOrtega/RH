import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
set_option maxSynthPendingDepth 1

open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

open IdeleGroup

variable (χ : HeckeCharacter K)

/- English proof (translation)
Take `⟨n, hn, hχ⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Use `⟨n, hn, fun x ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[toIdele_apply, ← ContinuousMonoidHom.pow_apply, hχ]`. Both sides reduce to the same expression.
-/
theorem exists_toIdele_pow_eq_one (h : IsOfFinOrder χ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : IdeleGroup K, χ.toIdele x ^ n = 1 := by
  obtain ⟨n, hn, hχ⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine ⟨n, hn, fun x ↦ ?_⟩
  rw [toIdele_apply, ← ContinuousMonoidHom.pow_apply, hχ]
  rfl

/- English proof (translation)
Take `⟨n, hn, hpow⟩` from `χ.exists_toIdele_pow_eq_one h`. Establish `hr : 0 < (x : ℝ) ^ (n⁻¹ : ℝ)` using `Real.rpow_pos_of_pos hx _`. Establish `hy : Units.mk0 _ hr.ne' ^ n = x` using `Units.ext (by`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hx.le hn.ne'])`. Rewrite using `[← hy, map_pow]`.

Conclude with `hpow (infiniteEmbedding w (realUnitsHom hw (Units.mk0 _ hr.ne')))`.
-/
theorem realComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsReal) {x : ℝˣ} (hx : 0 < (x : ℝ)) : χ.realComponent hw x = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  have hr : 0 < (x : ℝ) ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos hx _
  have hy : Units.mk0 _ hr.ne' ^ n = x := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hx.le hn.ne'])
  rw [← hy, map_pow]
  exact hpow (infiniteEmbedding w (realUnitsHom hw (Units.mk0 _ hr.ne')))

/- English proof (translation)
Take `⟨n, hn, hpow⟩` from `χ.exists_toIdele_pow_eq_one h`. Take `⟨y, hy⟩` from `IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[zero_pow hn.ne']`.

Conclude with `z.ne_zero hy.symm`. Establish `hyz : Units.mk0 y hy0 ^ n = z` using `Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])`. Rewrite using `[← hyz, map_pow]`. Conclude with `hpow (infiniteEmbedding w (complexUnitsHom hw (Units.mk0 y hy0)))`.
-/
theorem complexComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsComplex) (z : ℂˣ) : χ.complexComponent hw z = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact z.ne_zero hy.symm
  have hyz : Units.mk0 y hy0 ^ n = z := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])
  rw [← hyz, map_pow]
  exact hpow (infiniteEmbedding w (complexUnitsHom hw (Units.mk0 y hy0)))

end HeckeCharacter

end

end GroundTheory.Global
