import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Schur

open PositivityTheory.Rg.BcB.E1

variable {α : Type} [MeasurableSpace α] {ν : Measure α}

/- English proof (translation)
Establish `h` using `eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)`. Simplify `h` using `[ENNReal.rpow_ofNat]`.
-/
theorem eLpNorm_two_sq (f : α → ℂ) : eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
  simpa [ENNReal.rpow_ofNat] using h

/- English proof (translation)
Establish `hkK : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ)` using `hk.enorm`. Establish `hgm : AEMeasurable (fun y => ‖g y‖ₑ) ν` using `hg.1.enorm`. Establish `key` using `hS α ν (fun x y => ‖k x y‖ₑ) A (fun y => ‖g y‖ₑ) hkK hgm hr hc`. Establish `hgfin : eLpNorm g 2 ν ≠ ⊤` using `hg.2.ne`. Establish `hsq : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν = eLpNorm g 2 ν ^ 2` using `(eLpNorm_two_sq g).symm`.

Establish `hbound : ∫⁻ x, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂ν ≤ (A * eLpNorm g 2 ν) ^ 2`. Rewrite using `[mul_pow, ← hsq]`. Conclude with `key`. Establish `hfin : (A * eLpNorm g 2 ν) ^ 2 ≠ ⊤` using `ENNReal.pow_ne_top (ENNReal.mul_ne_top hA hgfin)`. Establish `hprod : AEStronglyMeasurable (fun p : α × α => k p.1 p.2 * g p.2) (ν.prod ν)` using `(hk.stronglyMeasurable.aestronglyMeasurable).mul hg.1.comp_snd`.

Establish `hSm : AEStronglyMeasurable (fun x => ∫ y, k x y * g y ∂ν) ν` using `hprod.integral_prod_right'`. Establish `hhm : AEMeasurable (fun x => ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ν`. Establish `: AEMeasurable (fun p : α × α => ‖k p.1 p.2‖ₑ * ‖g p.2‖ₑ) (ν.prod ν)`. Simplify `hprod.enorm` using `[enorm_mul]`. Conclude with `this.lintegral_prod_right'`.

Establish `hle : eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν`. Use `(ENNReal.pow_right_strictMono two_ne_zero).le_iff_le.1 ?_` and prove the remaining obligations. Rewrite using `[eLpNorm_two_sq]`. Use `le_trans (lintegral_mono fun x => ?_) hbound` and prove the remaining obligations. Use `pow_le_pow_left' ?_ 2` and prove the remaining obligations.

Use `(enorm_integral_le_lintegral_enorm _).trans ?_` and prove the remaining obligations. Simplify using `[enorm_mul]`. Use `⟨⟨hSm, lt_of_le_of_lt hle (ENNReal.mul_ne_top hA hgfin).lt_top⟩, hle, ?_⟩` and prove the remaining obligations. Establish `hae : ∀ᵐ x ∂ν, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 < ⊤` using `ae_lt_top' (hhm.pow_const 2) (ne_top_of_le_ne_top hfin hbound)`. Use `filter_upwards [hae] with x hx`.

Establish `hxf : ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν < ⊤`. Use `lt_top_iff_ne_top.2 fun hcon => ?_` and prove the remaining obligations. Simplify using `[hcon] at hx`. Establish `hkx : Measurable (k x)` using `hk.of_uncurry_left`. Use `⟨hkx.aestronglyMeasurable.mul hg.1, ?_⟩` and prove the remaining obligations.

Simplify `hxf` using `[HasFiniteIntegral, enorm_mul]`.
-/
theorem schur_memLp (hS : SchurL) [SFinite ν] (k : α → α → ℂ) (A : ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) (hA : A ≠ ⊤)
    (hr : ∀ x, ∫⁻ y, ‖k x y‖ₑ ∂ν ≤ A) (hc : ∀ y, ∫⁻ x, ‖k x y‖ₑ ∂ν ≤ A)
    (g : α → ℂ) (hg : MemLp g 2 ν) :
    MemLp (fun x => ∫ y, k x y * g y ∂ν) 2 ν ∧
      eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν ∧
      ∀ᵐ x ∂ν, Integrable (fun y => k x y * g y) ν := by
  have hkK : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.enorm
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) ν := hg.1.enorm
  have key := hS α ν (fun x y => ‖k x y‖ₑ) A (fun y => ‖g y‖ₑ) hkK hgm hr hc
  have hgfin : eLpNorm g 2 ν ≠ ⊤ := hg.2.ne
  have hsq : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν = eLpNorm g 2 ν ^ 2 := (eLpNorm_two_sq g).symm
  have hbound : ∫⁻ x, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂ν ≤ (A * eLpNorm g 2 ν) ^ 2 := by
    rw [mul_pow, ← hsq]; exact key
  have hfin : (A * eLpNorm g 2 ν) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top hA hgfin)
  have hprod : AEStronglyMeasurable (fun p : α × α => k p.1 p.2 * g p.2) (ν.prod ν) :=
    (hk.stronglyMeasurable.aestronglyMeasurable).mul hg.1.comp_snd
  have hSm : AEStronglyMeasurable (fun x => ∫ y, k x y * g y ∂ν) ν :=
    hprod.integral_prod_right'
  have hhm : AEMeasurable (fun x => ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ν := by
    have : AEMeasurable (fun p : α × α => ‖k p.1 p.2‖ₑ * ‖g p.2‖ₑ) (ν.prod ν) := by
      simpa [enorm_mul] using hprod.enorm
    exact this.lintegral_prod_right'
  have hle : eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν := by
    refine (ENNReal.pow_right_strictMono two_ne_zero).le_iff_le.1 ?_
    rw [eLpNorm_two_sq]
    refine le_trans (lintegral_mono fun x => ?_) hbound
    refine pow_le_pow_left' ?_ 2
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp [enorm_mul]
  refine ⟨⟨hSm, lt_of_le_of_lt hle (ENNReal.mul_ne_top hA hgfin).lt_top⟩, hle, ?_⟩
  have hae : ∀ᵐ x ∂ν, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 < ⊤ :=
    ae_lt_top' (hhm.pow_const 2) (ne_top_of_le_ne_top hfin hbound)
  filter_upwards [hae] with x hx
  have hxf : ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hcon => ?_
    simp [hcon] at hx
  have hkx : Measurable (k x) := hk.of_uncurry_left
  refine ⟨hkx.aestronglyMeasurable.mul hg.1, ?_⟩
  simpa [HasFiniteIntegral, enorm_mul] using hxf

/- English proof (translation)
Introduce `α _ ν _ k A hk hA hr hc`. Establish `H` using `fun f : Lp ℂ 2 ν => schur_memLp hS k A hk hA hr hc (f : α → ℂ) (Lp.memLp f)`. Set `L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν` to `{ toFun := fun f => (H f).1.toLp _ map_add' := by`. Introduce `f g`. Apply `Lp.ext` to reduce the goal to its premises.

Establish `h1` using `(H (f + g)).1.coeFn_toLp`. Establish `h2` using `(H f).1.coeFn_toLp`. Establish `h3` using `(H g).1.coeFn_toLp`. Establish `h4` using `Lp.coeFn_add ((H f).1.toLp _) ((H g).1.toLp _)`. Use `filter_upwards [h1, h2, h3, h4, (H f).2.2, (H g).2.2] with x e1 e2 e3 e4 i1 i2`.

Rewrite using `[e1, e4, Pi.add_apply, e2, e3, ← integral_add i1 i2]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [Lp.coeFn_add f g] with y hy`. Rewrite using `[hy, Pi.add_apply, mul_add]`. Use the proof step `map_smul' := by`.

Introduce `c f`. Apply `Lp.ext` to reduce the goal to its premises. Establish `h1` using `(H (c • f)).1.coeFn_toLp`. Establish `h2` using `(H f).1.coeFn_toLp`. Establish `h4` using `Lp.coeFn_smul c ((H f).1.toLp _)`.

Use `filter_upwards [h1, h2, h4] with x e1 e2 e4`. Rewrite using `[e1, RingHom.id_apply, e4, Pi.smul_apply, e2, smul_eq_mul, ← integral_const_mul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [Lp.coeFn_smul c f] with y hy`. Rewrite using `[hy, Pi.smul_apply, smul_eq_mul]`.

Use `ring }`. Use `⟨L.mkContinuous A.toReal ?_, fun f => (H f).1.coeFn_toLp⟩` and prove the remaining obligations. Introduce `f`. Express the relevant statement in the definitionally equal form `‖(H f).1.toLp _‖ ≤ A.toReal * ‖f‖`. Rewrite using `[Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]`.

Conclude with `ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.memLp f).2.ne) (H f).2.1`.
-/
theorem schurOp_of_schurL (hS : SchurL) : SchurOp := by
  intro α _ ν _ k A hk hA hr hc
  have H := fun f : Lp ℂ 2 ν => schur_memLp hS k A hk hA hr hc (f : α → ℂ) (Lp.memLp f)
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (H f).1.toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        have h1 := (H (f + g)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h3 := (H g).1.coeFn_toLp
        have h4 := Lp.coeFn_add ((H f).1.toLp _) ((H g).1.toLp _)
        filter_upwards [h1, h2, h3, h4, (H f).2.2, (H g).2.2] with x e1 e2 e3 e4 i1 i2
        rw [e1, e4, Pi.add_apply, e2, e3, ← integral_add i1 i2]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        have h1 := (H (c • f)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h4 := Lp.coeFn_smul c ((H f).1.toLp _)
        filter_upwards [h1, h2, h4] with x e1 e2 e4
        rw [e1, RingHom.id_apply, e4, Pi.smul_apply, e2, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul]
        ring }
  refine ⟨L.mkContinuous A.toReal ?_, fun f => (H f).1.coeFn_toLp⟩
  intro f
  change ‖(H f).1.toLp _‖ ≤ A.toReal * ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.memLp f).2.ne) (H f).2.1

end GlobalTheory.CompanionTheory.Schur

end
