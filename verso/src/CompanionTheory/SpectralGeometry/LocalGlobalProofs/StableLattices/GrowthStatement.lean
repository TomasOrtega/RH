import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.PathGrowth

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def Lev (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  (Continuous fun g : S7.UJ ε => f (S7.toM g)) ∧ LevelF ε f (-(m : ℝ))

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity`.
-/
theorem hs_nonneg (h : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/- English proof (translation)
The claim follows from `Finset.single_le_sum (f := fun a => ∑ i, ‖h a i‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)`.
-/
theorem row_le_hs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ∑ i, ‖h j i‖ ^ 2 ≤ Formalism.REAL.hs h :=
  Finset.single_le_sum (f := fun a => ∑ i, ‖h a i‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

/- English proof (translation)
Establish `h1 : ‖∑ i, h j i * a i‖ ≤ ∑ i, ‖h j i‖ * ‖a i‖` using `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))`. Establish `h2 : (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2` using `Finset.sum_mul_sq_le_sq_mul_sq _ _ _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem row_cs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) :
    ‖∑ i, h j i * a i‖ ^ 2 ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, h j i * a i‖ ≤ ∑ i, ‖h j i‖ * ‖a i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
  have h2 : (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖∑ i, h j i * a i‖ ^ 2 ≤ (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 := h2
    _ ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (row_le_hs h j) (Finset.sum_nonneg fun _ _ => by positivity)

/- English proof (translation)
Establish `hs0` using `hs_nonneg h`. Establish `hT : 0 ≤ ∑ i, ‖a i‖ ^ 2` using `Finset.sum_nonneg fun _ _ => by positivity`. Establish `hcs` using `row_cs h j a`. Rewrite using `[← Finset.sum_mul]`. Break down `hs0.eq_or_lt with h0 | hpos` into its components or cases.

Rewrite `hcs` using `[← h0, zero_mul]`. Establish `hz : ‖∑ i, h j i * a i‖ ^ 2 = 0` using `le_antisymm hcs (by positivity)`. Rewrite using `[hz, zero_mul]`. Conclude with `mul_nonneg hT (Real.rpow_nonneg hs0 _)`. Establish `e : Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) = Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹`.

Rewrite using `[Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add hpos, Real.rpow_neg_one]`. Establish `hr` using `Real.rpow_nonneg hs0 (-(m : ℝ))`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem row_bound (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) (m : ℕ) :
    ‖∑ i, h j i * a i‖ ^ 2 * Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) ≤
      ∑ i, ‖a i‖ ^ 2 * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
  have hs0 := hs_nonneg h
  have hT : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hcs := row_cs h j a
  rw [← Finset.sum_mul]
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul] at hcs
    have hz : ‖∑ i, h j i * a i‖ ^ 2 = 0 := le_antisymm hcs (by positivity)
    rw [hz, zero_mul]
    exact mul_nonneg hT (Real.rpow_nonneg hs0 _)
  · have e : Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) = Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹ := by
      rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add hpos, Real.rpow_neg_one]
    have hr := Real.rpow_nonneg hs0 (-(m : ℝ))
    rw [e]
    calc ‖∑ i, h j i * a i‖ ^ 2 * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹)
        ≤ (Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2) * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹) :=
          mul_le_mul_of_nonneg_right hcs (by positivity)
      _ = (∑ i, ‖a i‖ ^ 2) * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
          field_simp

/- English proof (translation)
Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`.
-/
theorem enorm_sq_mul (x : ℂ) (r : ℝ) :
    ‖x‖ₑ ^ 2 * ENNReal.ofReal r = ENNReal.ofReal (‖x‖ ^ 2 * r) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/- English proof (translation)
Unfold `Formalism.REAL.hs`. Use `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(((S7.continuous_toM ε).matrix_elem i j).norm).pow 2`.
-/
theorem continuous_hs (ε : Fin n → Bool) : Continuous fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) := by
  unfold Formalism.REAL.hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((S7.continuous_toM ε).matrix_elem i j).norm).pow 2

/- English proof (translation)
The claim follows from `(hf.measurable.enorm.pow_const 2).mul (ENNReal.measurable_ofReal.comp ((continuous_hs ε).measurable.pow_const s))`.
-/
theorem measurable_term (ε : Fin n → Bool) {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (s : ℝ)
    (hf : Continuous fun g : S7.UJ ε => f (S7.toM g)) :
    Measurable fun g : S7.UJ ε => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) :=
  (hf.measurable.enorm.pow_const 2).mul
    (ENNReal.measurable_ofReal.comp ((continuous_hs ε).measurable.pow_const s))

/- English proof (translation)
Use `⟨continuous_finsetSum _ fun i _ => ((S7.continuous_toM ε).matrix_elem j i).mul (hf i).1, ?_⟩` and prove the remaining obligations. Unfold `LevelF`. Use `lt_of_le_of_lt (lintegral_mono fun g => ?_) (b := ∫⁻ g : S7.UJ ε, ∑ i, ‖f i (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-(m : ℝ))) ∂Measure.haar) ?_` and prove the remaining obligations. Establish `hr` using `fun k : ℝ => Real.rpow_nonneg (hs_nonneg (S7.toM g)) k`. Simplify using `only [enorm_sq_mul]`.

Rewrite using `[← ENNReal.ofReal_sum_of_nonneg fun _ _ => mul_nonneg (by positivity) (hr _)]`. Conclude with `ENNReal.ofReal_le_ofReal (row_bound _ j _ m)`. Rewrite using `[lintegral_finsetSum _ fun i _ => measurable_term ε _ (hf i).1]`. Conclude with `ENNReal.sum_lt_top.2 fun i _ => (hf i).2`.
-/
theorem lev_row (ε : Fin n → Bool) (m : ℕ) (f : Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : ∀ i, Lev ε m (f i)) (j : Fin n) : Lev ε (m + 1) fun g => ∑ i, g j i * f i g := by
  refine ⟨continuous_finsetSum _ fun i _ =>
    ((S7.continuous_toM ε).matrix_elem j i).mul (hf i).1, ?_⟩
  unfold LevelF
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (b := ∫⁻ g : S7.UJ ε, ∑ i,
    ‖f i (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-(m : ℝ))) ∂Measure.haar) ?_
  · have hr := fun k : ℝ => Real.rpow_nonneg (hs_nonneg (S7.toM g)) k
    simp only [enorm_sq_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => mul_nonneg (by positivity) (hr _)]
    exact ENNReal.ofReal_le_ofReal (row_bound _ j _ m)
  · rw [lintegral_finsetSum _ fun i _ => measurable_term ε _ (hf i).1]
    exact ENNReal.sum_lt_top.2 fun i _ => (hf i).2

/- English proof (translation)
Set `μ : Measure (S7.UJ ε)` to `Formalism.REAL.muG ε`. Use `haveI : μ.IsHaarMeasure := Formalism.REAL.instIsHaarMuG n ε`. Establish `h' : MemLp (fun g : S7.UJ ε => F (S7.toM g)) 2 μ` using `h`. Establish `h2 : ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂μ < ⊤`. Use `lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top h'.2` as an intermediate fact.

Simplify using `using this`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure (S7.UJ ε)) μ, lintegral_smul_measure]`. Conclude with `ENNReal.mul_lt_top (by simp) h2`.
-/
theorem level_zero_of_memLp (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂Measure.haar < ⊤ := by
  let μ : Measure (S7.UJ ε) := Formalism.REAL.muG ε
  haveI : μ.IsHaarMeasure := Formalism.REAL.instIsHaarMuG n ε
  have h' : MemLp (fun g : S7.UJ ε => F (S7.toM g)) 2 μ := h
  have h2 : ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂μ < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top h'.2
    simpa using this
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure (S7.UJ ε)) μ, lintegral_smul_measure]
  exact ENNReal.mul_lt_top (by simp) h2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h1 : Continuous fun g : S7.UJ ε => σ (S7.toM g) (u : H)` using `(hσ.2.2 (u : H)).comp_continuous (S7.continuous_toM ε) fun g => g.2`. Conclude with `continuous_const.inner h1`. Unfold `LevelF`. Use `level_zero_of_memLp ε (baseCoef σ D ξ u) (hsq (u : H) ξ)` as an intermediate fact.

Simplify using `using this`.
-/
theorem lev_base (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (ξ : H)
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hsq : Formalism.MainNotions.S.IsSqIntOn ε σ) (u : D) :
    Lev ε 0 (baseCoef σ D ξ u) := by
  constructor
  · have h1 : Continuous fun g : S7.UJ ε => σ (S7.toM g) (u : H) :=
      (hσ.2.2 (u : H)).comp_continuous (S7.continuous_toM ε) fun g => g.2
    exact continuous_const.inner h1
  · unfold LevelF
    have := level_zero_of_memLp ε (baseCoef σ D ξ u) (hsq (u : H) ξ)
    simpa using this

/- English proof (translation)
The claim follows from `| [], _, _, _, _, _, h, u => h u | s :: ss, X, c, χ, js, m, h, u => by have key := lev_path ε ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail (m + 1) (fun w => lev_row ε m (fun i => c ((show stepSub X (χ s) from w).1 i)) (fun i => h _) (js.headD s) …`.
-/
theorem lev_path (ε : Fin n → Bool) : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)) (m : ℕ),
    (∀ u, Lev ε m (c u)) → ∀ u, Lev ε (m + ss.length) (pathCoef X c χ ss js u)
  | [], _, _, _, _, _, h, u => h u
  | s :: ss, X, c, χ, js, m, h, u => by
    have key := lev_path ε ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail (m + 1)
      (fun w => lev_row ε m (fun i => c ((show stepSub X (χ s) from w).1 i)) (fun i => h _) (js.headD s)) u
    rw [show m + (s :: ss).length = m + 1 + ss.length by simp only [List.length_cons]; omega]
    exact key

/- English proof (translation)
Introduce `n ε H _ _ _ σ D E hK χ ss hσ hsq`. Use `⟨(ss.length : ℝ), fun i u => ?_⟩` and prove the remaining obligations. Establish `key` using `lev_path ε ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 0 (fun u => lev_base ε σ D _ hσ hsq u) u`. Rewrite `key` using `[zero_add]`. Conclude with `key.2`.
-/
theorem growth : Growth := by
  intro n ε H _ _ _ σ D E hK χ ss hσ hsq
  refine ⟨(ss.length : ℝ), fun i u => ?_⟩
  have key := lev_path ε ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 0
    (fun u => lev_base ε σ D _ hσ hsq u) u
  rw [zero_add] at key
  exact key.2

end GlobalTheory.CompanionTheory.PathGrowth
