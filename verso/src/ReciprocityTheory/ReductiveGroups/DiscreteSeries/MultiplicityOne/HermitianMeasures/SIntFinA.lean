import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.NIntAtZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.HaarUp

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/- English proof (translation)
Rewrite using `[frobenius_norm_def, gN, Real.sqrt_eq_rpow]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_norm_sq, Real.rpow_two]`.
-/
theorem sfa_gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  rw [frobenius_norm_def, gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

/- English proof (translation)
Rewrite using `[sfa_gN_eq_frob, sfa_gN_eq_frob, sfa_gN_eq_frob]`. Conclude with `frobenius_norm_mul A B`.
-/
theorem sfa_gN_mul_le {k r : ℕ} (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  rw [sfa_gN_eq_frob, sfa_gN_eq_frob, sfa_gN_eq_frob]
  exact frobenius_norm_mul A B

/- English proof (translation)
Establish `: (fun g : Mat k r => gN g) = fun g => ‖g‖` using `funext sfa_gN_eq_frob`. Rewrite using `[this]`. Conclude with `continuous_norm`.
-/
theorem sfa_continuous_gN {k r : ℕ} : Continuous (fun g : Mat k r => gN g) := by
  have : (fun g : Mat k r => gN g) = fun g => ‖g‖ := funext sfa_gN_eq_frob
  rw [this]; exact continuous_norm

end frob

/- English proof (translation)
Establish `hx0 : 0 < x` using `lt_of_lt_of_le one_pos hx`. Establish `h1 : x / C ≤ y` using `by rw [div_le_iff₀ hC]; linarith`. Establish `h2 : 0 < x / C` using `div_pos hx0 hC`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.div_rpow hx0.le hC.le, Real.rpow_neg hC.le b, div_inv_eq_mul, mul_comm]`.
-/
theorem sfa_rpow_bound {x y C b : ℝ} (hx : 1 ≤ x) (hC : 0 < C) (hb : 0 ≤ b) (h : x ≤ C * y) :
    y ^ (-b) ≤ C ^ b * x ^ (-b) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 : x / C ≤ y := by rw [div_le_iff₀ hC]; linarith
  have h2 : 0 < x / C := div_pos hx0 hC
  calc y ^ (-b) ≤ (x / C) ^ (-b) := Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)
    _ = C ^ b * x ^ (-b) := by
      rw [Real.div_rpow hx0.le hC.le, Real.rpow_neg hC.le b, div_inv_eq_mul, mul_comm]

/- English proof (translation)
Take `⟨C, hC⟩` from `(hCpW k r z hz hT).exists_bound_of_continuousOn (sfa_continuous_gN (k := k) (r := r)).continuousOn`. Use `⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun h hh => ?_⟩` and prove the remaining obligations. Establish `hi : h⁻¹ ∈ UWset k r z` using `(hCW k r z).inv_mem h hh`. Use `hC _ hi` as an intermediate fact. Conclude with `le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using this) (le_max_left _ _))`.
-/
theorem gN_inv_bounded_on_UWset (hCW : ClosedW) (hCpW : CompactW) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) : ∃ C : ℝ, 0 < C ∧ ∀ h ∈ UWset k r z, gN h⁻¹ ≤ C := by
  obtain ⟨C, hC⟩ := (hCpW k r z hz hT).exists_bound_of_continuousOn
    (sfa_continuous_gN (k := k) (r := r)).continuousOn
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun h hh => ?_⟩
  have hi : h⁻¹ ∈ UWset k r z := (hCW k r z).inv_mem h hh
  have := hC _ hi
  exact le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using this) (le_max_left _ _))

/- English proof (translation)
Use `lt_of_le_of_lt ?_ hb` and prove the remaining obligations. Unfold `bS`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Simplify using `[dimN]`.

Establish `h1 : (1 : ℝ) ≤ ((2 * r + k : ℕ) : ℝ)`. Establish `: 1 ≤ 2 * r + k` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `h2 : (0 : ℝ) ≤ (dimN k r : ℝ)` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dimN_lt_of_bS_lt {k r : ℕ} {b : ℝ} (hb : bS k r < b) : (dimN k r : ℝ) < b := by
  refine lt_of_le_of_lt ?_ hb
  unfold bS
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [dimN]
  · have h1 : (1 : ℝ) ≤ ((2 * r + k : ℕ) : ℝ) := by
      have : 1 ≤ 2 * r + k := by omega
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ (dimN k r : ℝ) := Nat.cast_nonneg _
    nlinarith

/- English proof (translation)
Introduce `k r z μW μN hz hT hW hN b hb`. Establish `hbS : 0 ≤ bS k r` using `by unfold bS; positivity`. Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hWH` using `isHaarOn_fourier_of_isHaarOn_main hSF hCW hHW hz hT hW`. Establish `hNH` using `haarUp_N hSF hCN hHN hN`.

Establish `: SigmaFinite μW` using `hW.1`. Establish `: SigmaFinite μN` using `hN.1`. Take `⟨C, hC0, hC⟩` from `gN_inv_bounded_on_UWset hCW hCpW hz hT`. Establish `hfin` using `hNI k r μN hNH b (dimN_lt_of_bS_lt hb)`. Establish `hWfin` using `haar_measure_univ_lt_infinity_of_compactW hCpW hz hT hWH`.

Use `set g : Mt k r → ℝ≥0∞ := fun x => ENNReal.ofReal (gN (Matrix.of x) ^ (-b)) with hg`. Establish `hc : Continuous (fun x : Mt k r => gN (Matrix.of x))` using `sfa_continuous_gN`. Establish `hgm : Measurable g` using `ENNReal.measurable_ofReal.comp (hc.measurable.pow_const _)`. Establish `hWae : ∀ᵐ x : Mt k r ∂μW, x ∈ (UWset k r z : Set (Mt k r))` using `by rw [ae_iff]; exact hWH.conc`. Establish `hNae : ∀ᵐ x : Mt k r ∂μN, x ∈ (Nset k r : Set (Mt k r))` using `by rw [ae_iff]; exact hNH.conc`.

Establish `hP : ∀ᵐ p : Mt k r × Mt k r ∂(μW.prod μN), p.1 ∈ (UWset k r z : Set (Mt k r)) ∧ p.2 ∈ (Nset k r : Set (Mt k r))` using `(Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)`. Establish `main : ∀ F : Mt k r × Mt k r → ℝ≥0∞, (∀ᵐ p ∂(μW.prod μN), F p ≤ (fun _ : Mt k r => ENNReal.ofReal (C ^ b)) p.1 * g p.2) → ∫⁻ p, F p ∂(μW.prod μN) < ∞`. Introduce `F hF`. Use `lt_of_le_of_lt (lintegral_mono_ae hF) ?_` and prove the remaining obligations. Rewrite using `[lintegral_prod_mul aemeasurable_const hgm.aemeasurable, lintegral_const]`.

Conclude with `ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin) hfin`. Establish `hm1 : ∀ m : Mt k r, m ∈ Nset k r → 1 ≤ gN (Matrix.of m)` using `fun m hm => hGL k r _ hm.1`. Use `⟨main _ ?_, main _ ?_⟩` and prove the remaining obligations. Use `filter_upwards [hP] with p hp`. Establish `hu : IsUnit (Matrix.of p.1 : Mat k r).det` using `(hCW k r z).unit _ hp.1`.

Establish `hle : gN (Matrix.of p.2) ≤ C * gN (Matrix.of p.1 * Matrix.of p.2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ hu]`. Use `_ ≤ gN (Matrix.of p.1)⁻¹ * gN (Matrix.of p.1 * Matrix.of p.2) := sfa_gN_mul_le _ _`. Use `_ ≤ C * gN (Matrix.of p.1 * Matrix.of p.2) := mul_le_mul_of_nonneg_right (hC _ hp.1) (Real.sqrt_nonneg _)`.

Use `sfa_rpow_bound (hm1 _ hp.2) hC0 hb0 hle` as an intermediate fact. Simplify using `only [hg]`. Rewrite using `[← ENNReal.ofReal_mul (Real.rpow_nonneg hC0.le _)]`. Conclude with `ENNReal.ofReal_le_ofReal this`. Use `filter_upwards [hP] with p hp`.

Establish `hu : IsUnit (Matrix.of p.1 : Mat k r).det` using `(hCW k r z).unit _ hp.1`. Establish `hle : gN (Matrix.of p.2) ≤ C * gN (Matrix.of p.2 * Matrix.of p.1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ hu]`. Use `_ ≤ gN (Matrix.of p.2 * Matrix.of p.1) * gN (Matrix.of p.1)⁻¹ := sfa_gN_mul_le _ _`.

Use `_ ≤ gN (Matrix.of p.2 * Matrix.of p.1) * C := mul_le_mul_of_nonneg_left (hC _ hp.1) (Real.sqrt_nonneg _)`. Use `_ = C * gN (Matrix.of p.2 * Matrix.of p.1) := mul_comm _ _`. Use `sfa_rpow_bound (hm1 _ hp.2) hC0 hb0 hle` as an intermediate fact. Simplify using `only [hg]`. Rewrite using `[← ENNReal.ofReal_mul (Real.rpow_nonneg hC0.le _)]`.

Conclude with `ENNReal.ofReal_le_ofReal this`.
-/
theorem sIntFin_of (hSF : HaarUniqueSF) (hCW : ClosedW) (hCpW : CompactW) (hHW : HaarWExists) (hCN : ClosedN)
    (hHN : HaarNExists) (hGL : GNLower) (hNI : ∀ k r, NIntAt k r) : SIntFin := by
  intro k r z μW μN hz hT hW hN b hb
  have hbS : 0 ≤ bS k r := by unfold bS; positivity
  have hb0 : 0 ≤ b := by linarith
  have hWH := isHaarOn_fourier_of_isHaarOn_main hSF hCW hHW hz hT hW
  have hNH := haarUp_N hSF hCN hHN hN
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  obtain ⟨C, hC0, hC⟩ := gN_inv_bounded_on_UWset hCW hCpW hz hT
  have hfin := hNI k r μN hNH b (dimN_lt_of_bS_lt hb)
  have hWfin := haar_measure_univ_lt_infinity_of_compactW hCpW hz hT hWH
  set g : Mt k r → ℝ≥0∞ := fun x => ENNReal.ofReal (gN (Matrix.of x) ^ (-b)) with hg
  have hc : Continuous (fun x : Mt k r => gN (Matrix.of x)) := sfa_continuous_gN
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (hc.measurable.pow_const _)
  have hWae : ∀ᵐ x : Mt k r ∂μW, x ∈ (UWset k r z : Set (Mt k r)) := by rw [ae_iff]; exact hWH.conc
  have hNae : ∀ᵐ x : Mt k r ∂μN, x ∈ (Nset k r : Set (Mt k r)) := by rw [ae_iff]; exact hNH.conc
  have hP : ∀ᵐ p : Mt k r × Mt k r ∂(μW.prod μN), p.1 ∈ (UWset k r z : Set (Mt k r)) ∧
      p.2 ∈ (Nset k r : Set (Mt k r)) :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have main : ∀ F : Mt k r × Mt k r → ℝ≥0∞,
      (∀ᵐ p ∂(μW.prod μN), F p ≤ (fun _ : Mt k r => ENNReal.ofReal (C ^ b)) p.1 * g p.2) →
      ∫⁻ p, F p ∂(μW.prod μN) < ∞ := by
    intro F hF
    refine lt_of_le_of_lt (lintegral_mono_ae hF) ?_
    rw [lintegral_prod_mul aemeasurable_const hgm.aemeasurable, lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin) hfin
  have hm1 : ∀ m : Mt k r, m ∈ Nset k r → 1 ≤ gN (Matrix.of m) := fun m hm => hGL k r _ hm.1
  refine ⟨main _ ?_, main _ ?_⟩
  · filter_upwards [hP] with p hp
    have hu : IsUnit (Matrix.of p.1 : Mat k r).det := (hCW k r z).unit _ hp.1
    have hle : gN (Matrix.of p.2) ≤ C * gN (Matrix.of p.1 * Matrix.of p.2) := by
      calc gN (Matrix.of p.2) = gN ((Matrix.of p.1)⁻¹ * (Matrix.of p.1 * Matrix.of p.2)) := by
            rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
        _ ≤ gN (Matrix.of p.1)⁻¹ * gN (Matrix.of p.1 * Matrix.of p.2) := sfa_gN_mul_le _ _
        _ ≤ C * gN (Matrix.of p.1 * Matrix.of p.2) :=
            mul_le_mul_of_nonneg_right (hC _ hp.1) (Real.sqrt_nonneg _)
    have := sfa_rpow_bound (hm1 _ hp.2) hC0 hb0 hle
    simp only [hg]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC0.le _)]
    exact ENNReal.ofReal_le_ofReal this
  · filter_upwards [hP] with p hp
    have hu : IsUnit (Matrix.of p.1 : Mat k r).det := (hCW k r z).unit _ hp.1
    have hle : gN (Matrix.of p.2) ≤ C * gN (Matrix.of p.2 * Matrix.of p.1) := by
      calc gN (Matrix.of p.2) = gN ((Matrix.of p.2 * Matrix.of p.1) * (Matrix.of p.1)⁻¹) := by
            rw [Matrix.mul_nonsing_inv_cancel_right _ _ hu]
        _ ≤ gN (Matrix.of p.2 * Matrix.of p.1) * gN (Matrix.of p.1)⁻¹ := sfa_gN_mul_le _ _
        _ ≤ gN (Matrix.of p.2 * Matrix.of p.1) * C :=
            mul_le_mul_of_nonneg_left (hC _ hp.1) (Real.sqrt_nonneg _)
        _ = C * gN (Matrix.of p.2 * Matrix.of p.1) := mul_comm _ _
    have := sfa_rpow_bound (hm1 _ hp.2) hC0 hb0 hle
    simp only [hg]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC0.le _)]
    exact ENNReal.ofReal_le_ofReal this

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
