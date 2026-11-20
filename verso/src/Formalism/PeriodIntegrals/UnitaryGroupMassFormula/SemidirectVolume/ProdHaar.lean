import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeQuotientHolds

noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

/- English proof (translation)
Introduce `X _ _ _ _ K N H hS hK hN hH hC μN hμN μH hμH`. Take `⟨hnorm, e, he⟩` from `hS`. Take `⟨_, _, _, _⟩` from `hK`. Take `⟨_, _, _, _⟩` from `hN`. Take `⟨_, _, _, _⟩` from `hH`.

Establish `hem : Measurable e` using `e.continuous.measurable`. Establish `hPF : ProdF K N H ((μN.prod μH).map e) μN μH`. Introduce `f hf`. Establish `h1 : Measurable (fun k : K => f (k : X))` using `hf.comp measurable_subtype_coe`. Rewrite using `[lintegral_map h1 hem, lintegral_prod (fun p => f ((e p : K) : X)) (h1.comp hem).aemeasurable]`.

Simplify using `only [he]`. Use `⟨(μN.prod μH).map e, ?_, hPF⟩` and prove the remaining obligations. Establish `hLI : (Measure.map e (μN.prod μH)).IsMulLeftInvariant`. Prove the components needed by the constructor for the conclusion. Introduce `k`.

Use `set p0 := e.symm k with hp0`. Establish `hk : (k : X) = (p0.1 : X) * (p0.2 : X)`. Rewrite using `[← he, hp0, Homeomorph.apply_symm_apply]`. Set `T : N × H → N × H` to `fun p => e.symm (k * e p)`. Establish `hTc : Continuous T` using `e.symm.continuous.comp (continuous_const.mul e.continuous)`.

Establish `hTm : Measurable T` using `hTc.measurable`. Set `A : N → N` to `fun m => ⟨(p0.1 : X) * ((p0.2 : X) * (m : X) * (p0.2 : X)⁻¹), N.mul_mem p0.1.2 (hnorm _ p0.2.2 _ m.2)⟩`. Set `C : N → N` to `fun m => ⟨(p0.2 : X) * (m : X) * (p0.2 : X)⁻¹, hnorm _ p0.2.2 _ m.2⟩`. Establish `hT : ∀ p : N × H, T p = (A p.1, p0.2 * p.2)`. Introduce `p`.

Apply `e.injective` to reduce the goal to its premises. Simplify using `only [T, Homeomorph.apply_symm_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_mul, he, he, hk]`. Simplify using `only [A, Subgroup.coe_mul]`.

Use `group`. Establish `hTAB : T = Prod.map A (fun h => p0.2 * h)` using `funext fun p => hT p`. Establish `hAm : Measurable A`. Establish `hA1 : A = fun m => (T (m, 1)).1` using `funext fun m => by rw [hT]`. Rewrite using `[hA1]`.

Use `first`. Consider the case `exact (continuous_fst.comp (hTc.comp (continuous_id.prodMk continuous_const))).measurable`. Consider the case `exact (continuous_fst.comp (hTc.comp (continuous_id.prod_mk continuous_const))).measurable`. Establish `hCA : C = fun m => p0.1⁻¹ * A m` using `funext fun m => Subtype.ext (by`. Simplify using `only [A, C, Subgroup.coe_mul, Subgroup.coe_inv]`.

Use the proof step `group)`. Establish `hCm : Measurable C`. Rewrite using `[hCA]`. Conclude with `(measurable_const_mul _).comp hAm`. Establish `hCinv : Measure.map C μN = μN`.

Use extensionality with `S hS`. Rewrite using `[Measure.map_apply hCm hS]`. Take `⟨B, hB, rfl⟩` from `hS`. Establish `key` using `hC μN hμN (p0.2 : X) p0.2.2 (B.indicator 1) (measurable_one.indicator hB)`. Establish `e1 : ∫⁻ n, B.indicator 1 ((p0.2 : X) * (n : X) * (p0.2 : X)⁻¹) ∂μN = μN (C ⁻¹' (Subtype.val ⁻¹' B))`.

Rewrite using `[← lintegral_indicator_one (hCm (measurable_subtype_coe hB))]`. Use `first`. Consider the case `rfl`. Consider the case `(congr 1; funext n; simp [Set.indicator_apply, C])`. Establish `e2 : ∫⁻ n, B.indicator 1 (n : X) ∂μN = μN (Subtype.val ⁻¹' B)`.

Rewrite using `[← lintegral_indicator_one (measurable_subtype_coe hB)]`. Use `first`. Consider the case `rfl`. Consider the case `(congr 1; funext n; simp [Set.indicator_apply])`. Rewrite using `[← e1, key, e2]`.

Establish `hA : Measure.map A μN = μN`. Establish `hAC : A = (fun m => p0.1 * m) ∘ C`. Use function extensionality and compare the values at `fun m => Subtype.ext (by simp only [A, C, Function.comp_apply, Subgroup.coe_mul])`. Rewrite using `[hAC, ← Measure.map_map (measurable_const_mul _) hCm, hCinv, map_mul_left_eq_self]`. Establish `hB : Measure.map (fun h : H => p0.2 * h) μH = μH` using `map_mul_left_eq_self μH p0.2`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.map_map (measurable_const_mul k) hem]`. Use `_ = Measure.map (e ∘ T) (μN.prod μH) := by`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Simplify using `[T]`. Use `_ = Measure.map e (Measure.map T (μN.prod μH)) := by rw [Measure.map_map hem hTm]`. Use `_ = Measure.map e (μN.prod μH) := by`. Rewrite using `[hTAB, ← Measure.map_prod_map _ _ hAm (measurable_const_mul _), hA, hB]`. Establish `hFC : IsFiniteMeasureOnCompacts (Measure.map e (μN.prod μH))`.

Prove the components needed by the constructor for the conclusion. Introduce `C hCc`. Rewrite using `[Measure.map_apply hem hCc.measurableSet]`. Conclude with `(e.isCompact_preimage.mpr hCc).measure_lt_top`. Establish `hOP : (Measure.map e (μN.prod μH)).IsOpenPosMeasure`.

Prove the components needed by the constructor for the conclusion. Introduce `U hU hne`. Rewrite using `[Measure.map_apply hem hU.measurableSet]`. Conclude with `(hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)`. Conclude with `⟨⟩`.
-/
theorem product_haar_measure_holds : ProdHaarG := by
  intro X _ _ _ _ K N H hS hK hN hH hC μN hμN μH hμH
  obtain ⟨hnorm, e, he⟩ := hS
  obtain ⟨_, _, _, _⟩ := hK
  obtain ⟨_, _, _, _⟩ := hN
  obtain ⟨_, _, _, _⟩ := hH
  have hem : Measurable e := e.continuous.measurable
  have hPF : ProdF K N H ((μN.prod μH).map e) μN μH := by
    intro f hf
    have h1 : Measurable (fun k : K => f (k : X)) := hf.comp measurable_subtype_coe
    rw [lintegral_map h1 hem, lintegral_prod (fun p => f ((e p : K) : X)) (h1.comp hem).aemeasurable]
    simp only [he]
  refine ⟨(μN.prod μH).map e, ?_, hPF⟩
  have hLI : (Measure.map e (μN.prod μH)).IsMulLeftInvariant := by
    constructor
    intro k
    set p0 := e.symm k with hp0
    have hk : (k : X) = (p0.1 : X) * (p0.2 : X) := by
      rw [← he, hp0, Homeomorph.apply_symm_apply]
    let T : N × H → N × H := fun p => e.symm (k * e p)
    have hTc : Continuous T := e.symm.continuous.comp (continuous_const.mul e.continuous)
    have hTm : Measurable T := hTc.measurable
    let A : N → N := fun m => ⟨(p0.1 : X) * ((p0.2 : X) * (m : X) * (p0.2 : X)⁻¹),
      N.mul_mem p0.1.2 (hnorm _ p0.2.2 _ m.2)⟩
    let C : N → N := fun m => ⟨(p0.2 : X) * (m : X) * (p0.2 : X)⁻¹, hnorm _ p0.2.2 _ m.2⟩
    have hT : ∀ p : N × H, T p = (A p.1, p0.2 * p.2) := by
      intro p
      apply e.injective
      simp only [T, Homeomorph.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_mul, he, he, hk]
      simp only [A, Subgroup.coe_mul]
      group
    have hTAB : T = Prod.map A (fun h => p0.2 * h) := funext fun p => hT p
    have hAm : Measurable A := by
      have hA1 : A = fun m => (T (m, 1)).1 := funext fun m => by rw [hT]
      rw [hA1]
      first
        | exact (continuous_fst.comp (hTc.comp (continuous_id.prodMk continuous_const))).measurable
        | exact (continuous_fst.comp (hTc.comp (continuous_id.prod_mk continuous_const))).measurable
    have hCA : C = fun m => p0.1⁻¹ * A m := funext fun m => Subtype.ext (by
      simp only [A, C, Subgroup.coe_mul, Subgroup.coe_inv]
      group)
    have hCm : Measurable C := by
      rw [hCA]
      exact (measurable_const_mul _).comp hAm
    have hCinv : Measure.map C μN = μN := by
      ext S hS
      rw [Measure.map_apply hCm hS]
      obtain ⟨B, hB, rfl⟩ := hS
      have key := hC μN hμN (p0.2 : X) p0.2.2 (B.indicator 1) (measurable_one.indicator hB)
      have e1 : ∫⁻ n, B.indicator 1 ((p0.2 : X) * (n : X) * (p0.2 : X)⁻¹) ∂μN =
          μN (C ⁻¹' (Subtype.val ⁻¹' B)) := by
        rw [← lintegral_indicator_one (hCm (measurable_subtype_coe hB))]
        first
          | rfl
          | (congr 1; funext n; simp [Set.indicator_apply, C])
      have e2 : ∫⁻ n, B.indicator 1 (n : X) ∂μN = μN (Subtype.val ⁻¹' B) := by
        rw [← lintegral_indicator_one (measurable_subtype_coe hB)]
        first
          | rfl
          | (congr 1; funext n; simp [Set.indicator_apply])
      rw [← e1, key, e2]
    have hA : Measure.map A μN = μN := by
      have hAC : A = (fun m => p0.1 * m) ∘ C :=
        funext fun m => Subtype.ext (by simp only [A, C, Function.comp_apply, Subgroup.coe_mul])
      rw [hAC, ← Measure.map_map (measurable_const_mul _) hCm, hCinv, map_mul_left_eq_self]
    have hB : Measure.map (fun h : H => p0.2 * h) μH = μH := map_mul_left_eq_self μH p0.2
    calc Measure.map (k * ·) (Measure.map e (μN.prod μH))
        = Measure.map ((k * ·) ∘ e) (μN.prod μH) := by
          rw [Measure.map_map (measurable_const_mul k) hem]
      _ = Measure.map (e ∘ T) (μN.prod μH) := by
          congr 1
          funext p
          simp [T]
      _ = Measure.map e (Measure.map T (μN.prod μH)) := by rw [Measure.map_map hem hTm]
      _ = Measure.map e (μN.prod μH) := by
          rw [hTAB, ← Measure.map_prod_map _ _ hAm (measurable_const_mul _), hA, hB]
  have hFC : IsFiniteMeasureOnCompacts (Measure.map e (μN.prod μH)) := by
    constructor
    intro C hCc
    rw [Measure.map_apply hem hCc.measurableSet]
    exact (e.isCompact_preimage.mpr hCc).measure_lt_top
  have hOP : (Measure.map e (μN.prod μH)).IsOpenPosMeasure := by
    constructor
    intro U hU hne
    rw [Measure.map_apply hem hU.measurableSet]
    exact (hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)
  exact ⟨⟩

end PI.VolSemiDirect.W
