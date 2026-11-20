import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RowsCompactSum

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

/- English proof (translation)
The claim follows from `continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)`.
-/
theorem contFin : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pFin E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)

/- English proof (translation)
The claim follows from `continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)`.
-/
theorem contInf : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pInf E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)

/- English proof (translation)
Take `⟨R, hR⟩` from `hC₀.exists_bound_of_continuousOn (contInf (E := E) (k := k)).continuousOn`. Use `⟨(1 + max R 0) ^ M, by positivity, fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ C₀`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy), ← ENNReal.ofReal_mul (by positivity)]`. Rewrite using `[← ENNReal.ofReal_one]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `h0 : 0 < (1 + ‖fun i => pInf E (y i)‖) ^ M` using `by positivity`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ h0, one_mul]`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Use `hR y hy` as an intermediate fact.

Combine the linear relations using `[le_max_left R 0]`. Rewrite using `[Set.indicator_of_notMem hy]`. Conclude with `bot_le`.
-/
theorem one_le (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (M : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal B * ENNReal.ofReal
      (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn (contInf (E := E) (k := k)).continuousOn
  refine ⟨(1 + max R 0) ^ M, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy), ← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 < (1 + ‖fun i => pInf E (y i)‖) ^ M := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h0, one_mul]
    apply pow_le_pow_left₀ (by positivity)
    have := hR y hy
    linarith [le_max_left R 0]
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

/- English proof (translation)
Establish `hCf : IsCompact ((fun y (i : Fin k) => pFin E (y i)) '' C₀)` using `hC₀.image contFin`. Take `⟨M, C, hMC⟩` from `hG3 E k _ hCf a ha`. Take `⟨B, hB, hB1⟩` from `one_le C₀ hC₀ M`. Establish `hlast` using `(hN E k k hk le_rfl).2.2.2.2.2.2.2.2.2`. Use `⟨B, max C 0, hB, le_max_right _ _, fun g r hr hrh => ?_⟩` and prove the remaining obligations.

Establish `hinj : Function.Injective (fun ξ : RowT E k k => (⟨ξ.1, ξ.2.1⟩ : {ξ : Fin k → E // ξ ≠ 0}))`. Introduce `x y h`. Simplify using `only [Subtype.mk.injEq] at h`. Conclude with `Subtype.ext h`. Set `F : {ξ : Fin k → E // ξ ≠ 0} → ℝ≥0∞` to `fun ξ => ENNReal.ofReal (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹) fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))`.

Establish `hF : ∑' ξ, F ξ ≤ ENNReal.ofReal (C * (r ^ a)⁻¹)` using `hMC g r hr hrh`. Establish `h1 : ∀ ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤ ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩`. Introduce `ξ`. Rewrite using `[hlast]`. Conclude with `hB1 _`.

Combine the equalities or inequalities in the displayed calculation. Use `hF.trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations. Use `gcongr`. Conclude with `le_max_left _ _`. Use `_ = ENNReal.ofReal (B * (max C 0 * (r ^ a)⁻¹)) := (ENNReal.ofReal_mul hB).symm`.
-/
theorem sum_le (hN : N0) (hG3 : ThetaSeriesBound) (hk : 1 ≤ k) (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (ha : k ≤ a) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ (g : GA E k) (r : ℝ), 0 < r → (∀ ξ, ξ ≠ 0 → r ≤ height g ξ) →
      ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
        ENNReal.ofReal (B * (C * (r ^ a)⁻¹)) := by
  have hCf : IsCompact ((fun y (i : Fin k) => pFin E (y i)) '' C₀) := hC₀.image contFin
  obtain ⟨M, C, hMC⟩ := hG3 E k _ hCf a ha
  obtain ⟨B, hB, hB1⟩ := one_le C₀ hC₀ M
  have hlast := (hN E k k hk le_rfl).2.2.2.2.2.2.2.2.2
  refine ⟨B, max C 0, hB, le_max_right _ _, fun g r hr hrh => ?_⟩
  have hinj : Function.Injective (fun ξ : RowT E k k => (⟨ξ.1, ξ.2.1⟩ : {ξ : Fin k → E // ξ ≠ 0})) := by
    intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  let F : {ξ : Fin k → E // ξ ≠ 0} → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))
  have hF : ∑' ξ, F ξ ≤ ENNReal.ofReal (C * (r ^ a)⁻¹) := hMC g r hr hrh
  have h1 : ∀ ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
      ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := by
    intro ξ
    rw [hlast]
    exact hB1 _
  calc _ ≤ ∑' ξ : RowT E k k, ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := ENNReal.tsum_le_tsum h1
    _ ≤ ∑' ξ, ENNReal.ofReal B * F ξ := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun ξ => ENNReal.ofReal B * F ξ)
    _ = ENNReal.ofReal B * ∑' ξ, F ξ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (max C 0 * (r ^ a)⁻¹) := by
        gcongr
        refine hF.trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (B * (max C 0 * (r ^ a)⁻¹)) := (ENNReal.ofReal_mul hB).symm

/- English proof (translation)
Establish `hDt` using `(hD E k).1 g`. Establish `hK'` using `hK E k hk`. Establish `hp : 0 < Dt g ^ ((k : ℝ)⁻¹)` using `Real.rpow_pos_of_pos hDt _`. Use `⟨mul_pos (hK'.2.1 g) hp, fun ξ hξ => ?_⟩` and prove the remaining obligations. Establish `h1` using `hK'.2.2.1 g ξ hξ`.

Establish `h2 : height g ξ = ht g ξ * Dt g ^ ((k : ℝ)⁻¹)`. Unfold `ht`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h2]`. Conclude with `mul_le_mul_of_nonneg_right h1 hp.le`.
-/
theorem r_le (hD : D0) (hK : K1) (hk : 1 ≤ k) (g : GA E k) :
    0 < dmin g * Dt g ^ ((k : ℝ)⁻¹) ∧ ∀ ξ, ξ ≠ 0 → dmin g * Dt g ^ ((k : ℝ)⁻¹) ≤ height g ξ := by
  have hDt := (hD E k).1 g
  have hK' := hK E k hk
  have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
  refine ⟨mul_pos (hK'.2.1 g) hp, fun ξ hξ => ?_⟩
  have h1 := hK'.2.2.1 g ξ hξ
  have h2 : height g ξ = ht g ξ * Dt g ^ ((k : ℝ)⁻¹) := by
    unfold ht; field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 hp.le

end RowsCompactSum

/- English proof (translation)
Introduce `hD hN _ hG3 hK E _ _ _ k hk C₀ hC₀`. Use `⟨fun g => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨B, C, hB, hC, h⟩` from `RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ k le_rfl`. Take `⟨hr, hrh⟩` from `RowsCompactSum.r_le hD hK hk g`. Establish `hfin` using `h g _ hr hrh`.

Establish `hne : ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≠ ⊤` using `ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin`. Use `(ENNReal.finite_const_le_of_tsum_ne_top hne one_ne_zero).subset fun ξ hξ => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hξ ⊢`. Rewrite using `[Set.indicator_of_mem hξ]`. Take `⟨B, C, hB, hC, h⟩` from `RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ a ha`.

Use `⟨B * C, fun g => ?_⟩` and prove the remaining obligations. Take `⟨hr, hrh⟩` from `RowsCompactSum.r_le hD hK hk g`. Establish `hDt` using `(hD E k).1 g`. Establish `hd` using `(hK E k hk).2.1 g`. Establish `hp : 0 < Dt g ^ ((k : ℝ)⁻¹)` using `Real.rpow_pos_of_pos hDt _`.

Establish `hw0 : 0 ≤ wt a g` using `by unfold wt; exact pow_nonneg (le_min zero_le_one hd.le) _`. Establish `hw : wt a g ≤ dmin g ^ a` using `by unfold wt; exact pow_le_pow_left₀ (le_min zero_le_one hd.le) (min_le_right _ _) _`. Combine the equalities or inequalities in the displayed calculation. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `he : Dt g ^ (-(a : ℝ) / k) = ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hDt.le, ← Real.rpow_neg hDt.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, mul_pow, mul_inv]`. Establish `hda : 0 < dmin g ^ a` using `pow_pos hd _`.

Establish `hpa : 0 < (Dt g ^ ((k : ℝ)⁻¹)) ^ a` using `pow_pos hp _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rows_compact_of_bound : D0 → N0 → H0 → ThetaSeriesBound → K1 → RowsInCompactSet := by
  intro hD hN _ hG3 hK E _ _ _ k hk C₀ hC₀
  refine ⟨fun g => ?_, fun a ha => ?_⟩
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ k le_rfl
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hfin := h g _ hr hrh
    have hne : ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
    refine (ENNReal.finite_const_le_of_tsum_ne_top hne one_ne_zero).subset fun ξ hξ => ?_
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rw [Set.indicator_of_mem hξ]
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ a ha
    refine ⟨B * C, fun g => ?_⟩
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hDt := (hD E k).1 g
    have hd := (hK E k hk).2.1 g
    have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hw0 : 0 ≤ wt a g := by unfold wt; exact pow_nonneg (le_min zero_le_one hd.le) _
    have hw : wt a g ≤ dmin g ^ a := by unfold wt; exact pow_le_pow_left₀ (le_min zero_le_one hd.le) (min_le_right _ _) _
    calc (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) *
          ENNReal.ofReal (wt a g)
        ≤ ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * ENNReal.ofReal (wt a g) := by
          gcongr; exact h g _ hr hrh
      _ = ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹) * wt a g) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (B * C * Dt g ^ (-(a : ℝ) / k)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : Dt g ^ (-(a : ℝ) / k) = ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hDt.le, ← Real.rpow_neg hDt.le]
            congr 1; ring
          rw [he, mul_pow, mul_inv]
          have hda : 0 < dmin g ^ a := pow_pos hd _
          have hpa : 0 < (Dt g ^ ((k : ℝ)⁻¹)) ^ a := pow_pos hp _
          calc B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * wt a g
              ≤ B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * dmin g ^ a := by
                gcongr
            _ = B * C * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by field_simp

end PositivityTheory.AdelicQuotientData

end
