import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PreimageSubsetImage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HuaInvOfTauDeriv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HasFDerivAtTauR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExLHU

noncomputable section

namespace HcHDC

open HcInf HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

/- English proof (translation)
Establish `hW : IsOpen (cayS (D0 P Q))` using `isOpen_cayley_domain (P := P) (Q := Q)`. Establish `h00 : (0 : lieU P Q) ∈ D0 P Q` using `zero_mem_cayley_domain (P := P) (Q := Q)`. Establish `h1W : (1 : UpqT P Q) ∈ cayS (D0 P Q)`. Establish `h` using `cayF_spec (P := P) (Q := Q) 0 h00`. Rewrite `h` using `[cayF_zero (P := P) (Q := Q)]`.

Conclude with `⟨0, h00, h⟩`. Establish `hHua : HuaInv` using `huaInv_of_tauDeriv tau_derivative`. Establish `hinv : ∀ (h : UpqT P Q) (S : Set (UpqT P Q)), MeasurableSet S → S ⊆ cayS (D0 P Q) → (fun g => h * g) '' S ⊆ cayS (D0 P Q) → betaH P Q lam ((fun g => h * g) '' S) = betaH P Q lam S` using `fun h S hS hSW hhSW => hHua P Q lam hlam h S hS hSW hhSW`. Establish `hcpt : ∀ K, IsCompact K → K ⊆ cayS (D0 P Q) → betaH P Q lam K ≠ ⊤`. Introduce `K hK hKW`.

Establish `hKm : MeasurableSet K` using `hK.isClosed.measurableSet`. Establish `hCc : IsCompact (insert (0 : lieU P Q) (cayInv P Q '' K))` using `(hK.image_of_continuousOn ((continuousOn_cayInv (P := P) (Q := Q)).mono hKW)).insert 0`. Establish `hC0 : insert (0 : lieU P Q) (cayInv P Q '' K) ⊆ D0 P Q`. Introduce and unpack `X (rfl | ⟨g, hg, rfl⟩)`. Conclude with `h00`.

Take `⟨Y, hY, hrel⟩` from `hKW hg`. Rewrite using `[cayley_inverse_iff P Q g Y hrel]`. Conclude with `hY`. Take `⟨x0, -, hmax⟩` from `hCc.exists_isMaxOn ⟨0, Set.mem_insert _ _⟩ (fun x hx => (continuousAt_rhoH (P := P) (Q := Q) x (hC0 hx)).continuousWithinAt)`. Establish `hS'm : MeasurableSet (cayF P Q ⁻¹' K ∩ D0 P Q)` using `(measurable_cayF (P := P) (Q := Q) hKm).inter (isOpen_cell_domain (P := P) (Q := Q)).measurableSet`.

Establish `hS'C : cayF P Q ⁻¹' K ∩ D0 P Q ⊆ insert (0 : lieU P Q) (cayInv P Q '' K)` using `fun X hX => Set.mem_insert_of_mem _ (preimage_subset_image (P := P) (Q := Q) K hX)`. Rewrite using `[betaH_apply (P := P) (Q := Q) lam K hKm]`. Apply `ne_of_lt` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Apply `lintegral_mono_ae` to reduce the goal to its premises.

Use `filter_upwards [ae_restrict_mem hS'm] with X hX`. Conclude with `isMaxOn_iff.1 hmax X (hS'C hX)`. Use `_ = rhoH P Q x0 * lam (cayF P Q ⁻¹' K ∩ D0 P Q) := setLIntegral_const _ _`. Use `_ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 ENNReal.ofReal_ne_top) ((measure_mono hS'C).trans_lt hCc.measure_lt_top)`. Establish `hne : betaH P Q lam (cayS (D0 P Q)) ≠ 0`.

Rewrite using `[betaH_apply (P := P) (Q := Q) lam _ hW.measurableSet]`. Establish `hpre : cayF P Q ⁻¹' cayS (D0 P Q) ∩ D0 P Q = D0 P Q` using `Set.inter_eq_right.2 (fun X hX => ⟨X, hX, cayF_spec (P := P) (Q := Q) X hX⟩)`. Rewrite using `[hpre]`. Establish `hpos : 0 < lam (D0 P Q)` using `(isOpen_cell_domain (P := P) (Q := Q)).measure_pos lam ⟨0, h00⟩`. Introduce `h0`.

Rewrite `h0` using `[lintegral_eq_zero_iff (measurable_rhoH (P := P) (Q := Q))]`. Establish `hF : ∀ᵐ x ∂(lam.restrict (D0 P Q)), False` using `by filter_upwards [h0, ae_restrict_mem (isOpen_cell_domain (P := P) (Q := Q)).measurableSet] with x hx hxD`. Conclude with `rhoH_pos (P := P) (Q := Q) x hxD hx`. Rewrite `hF` using `[ae_iff]`. Simplify using `only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply_univ] at hF`.

Conclude with `hpos.ne' hF`. Take `⟨t, ht0, httop, W', hW'1, hW'W, hβW'⟩` from `local_haar_unique (UpqT P Q) m hm (betaH P Q lam) (cayS (D0 P Q)) hW h1W hinv hcpt hne`. Take `⟨V, hVW', hVo, h1V⟩` from `mem_nhds_iff.1 hW'1`. Establish `hβV : (betaH P Q lam).restrict V = t • m.restrict V`. Establish `h` using `congrArg (fun μ : Measure (UpqT P Q) => μ.restrict V) hβW'`.

Simplify using `only [Measure.restrict_restrict_of_subset hVW', Measure.restrict_smul] at h`. Conclude with `h`. Establish `key : ∀ S ⊆ V, betaH P Q lam S = t * m S`. Introduce `S hSV`. Establish `h` using `congrArg (fun μ : Measure (UpqT P Q) => μ S) hβV`.

Simplify using `only [Measure.smul_apply, Measure.restrict_apply' hVo.measurableSet, Set.inter_eq_left.2 hSV, smul_eq_mul] at h`. Conclude with `h`. Use `set D : Set (lieU P Q) := D0 P Q ∩ cayF P Q ⁻¹' V with hDdef`. Establish `hDnhds : D ∈ 𝓝 (0 : lieU P Q)`. Establish `hc : ContinuousAt (cayF P Q) 0` using `(continuousOn_cayF (P := P) (Q := Q)).continuousAt ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00)`.

Establish `hV0 : V ∈ 𝓝 (cayF P Q 0)`. Rewrite using `[cayF_zero (P := P) (Q := Q)]`. Conclude with `hVo.mem_nhds h1V`. Conclude with `Filter.inter_mem ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00) (hc.preimage_mem_nhds hV0)`. Establish `hDmeas : MeasurableSet D` using `(isOpen_cell_domain (P := P) (Q := Q)).measurableSet.inter (measurable_cayF (P := P) (Q := Q) hVo.measurableSet)`.

Establish `hcayS : cayS D = cayS (D0 P Q) ∩ cayInv P Q ⁻¹' D`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X, hXD, hrel⟩`. Use `⟨⟨X, hXD.1, hrel⟩, ?_⟩` and prove the remaining obligations.

Use `show cayInv P Q g ∈ D`. Rewrite using `[cayley_inverse_iff P Q g X hrel]`. Conclude with `hXD`. Introduce and unpack `⟨⟨X, -, hrel⟩, hgD⟩`. Establish `hgX` using `cayley_inverse_iff P Q g X hrel`.

Use `⟨X, ?_, hrel⟩` and prove the remaining obligations. Rewrite using `[← hgX]`. Conclude with `hgD`. Use `⟨D, hDnhds, hDmeas, fun X => t⁻¹ * rhoH P Q X, (measurable_rhoH (P := P) (Q := Q)).const_mul _, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(ENNReal.continuous_const_mul (ENNReal.inv_ne_top.2 ht0)).continuousAt.comp (continuousAt_rhoH (P := P) (Q := Q) 0 h00)`.

Conclude with `mul_ne_zero (ENNReal.inv_ne_zero.2 httop) (rhoH_pos (P := P) (Q := Q) 0 h00)`. Conclude with `ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ht0) ENNReal.ofReal_ne_top`. Use extensionality with `A hA`. Establish `hSV : cayInv P Q ⁻¹' A ∩ cayS D ⊆ V`. Introduce and unpack `g ⟨-, X, hXD, hrel⟩`.

Rewrite using `[← cayF_eq_of (P := P) (Q := Q) g X hrel]`. Conclude with `hXD.2`. Establish `hSmeas : MeasurableSet (cayInv P Q ⁻¹' A ∩ cayS D)`. Rewrite using `[hcayS]`. Conclude with `(cayley_inverse_measurable P Q hA).inter (hW.measurableSet.inter (cayley_inverse_measurable P Q hDmeas))`.

Establish `hpre : cayF P Q ⁻¹' (cayInv P Q ⁻¹' A ∩ cayS D) ∩ D0 P Q = A ∩ D`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hXA, Y, hYD, hrel⟩, hX0⟩`. Establish `h1 : cayInv P Q (cayF P Q X) = X` using `cayInv_cayF (P := P) (Q := Q) X hX0`.

Establish `h2 : cayInv P Q (cayF P Q X) = Y` using `cayley_inverse_iff P Q _ Y hrel`. Establish `hXY : X = Y` using `h1.symm.trans h2`. Use `⟨?_, by rw [hXY]; exact hYD⟩` and prove the remaining obligations. Establish `hA' : cayInv P Q (cayF P Q X) ∈ A` using `hXA`. Rewrite `hA'` using `[h1]`. Then use the resulting hypothesis.

Introduce and unpack `⟨hXA, hXD⟩`. Use `⟨⟨?_, X, hXD, cayF_spec (P := P) (Q := Q) X hXD.1⟩, hXD.1⟩` and prove the remaining obligations. Use `show cayInv P Q (cayF P Q X) ∈ A`. Rewrite using `[cayInv_cayF (P := P) (Q := Q) X hXD.1]`. Conclude with `hXA`.

Establish `hβS : betaH P Q lam (cayInv P Q ⁻¹' A ∩ cayS D) = ∫⁻ X in A ∩ D, rhoH P Q X ∂lam`. Rewrite using `[betaH_apply (P := P) (Q := Q) lam _ hSmeas, hpre]`. Rewrite using `[Measure.map_apply (cayley_inverse_measurable P Q) hA, Measure.restrict_apply (cayley_inverse_measurable P Q hA), withDensity_apply _ hA, Measure.restrict_restrict hA]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]`.

Use `_ = t⁻¹ * ∫⁻ X in A ∩ D, rhoH P Q X ∂lam := by rw [← key _ hSV, hβS]`. Use `_ = ∫⁻ X in A ∩ D, t⁻¹ * rhoH P Q X ∂lam := (lintegral_const_mul _ (measurable_rhoH (P := P) (Q := Q))).symm`.
-/
theorem cayDensU (P Q : ℕ) (m : Measure (UpqT P Q)) [hm : m.IsHaarMeasure] (lam : Measure (lieU P Q))
    [hlam : lam.IsAddHaarMeasure] :
    ∃ D ∈ 𝓝 (0 : lieU P Q), MeasurableSet D ∧ ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧ ContinuousAt f 0 ∧
      f 0 ≠ 0 ∧ f 0 ≠ ⊤ ∧ (m.restrict (cayS D)).map (cayInv P Q) = (lam.restrict D).withDensity f := by

  have hW : IsOpen (cayS (D0 P Q)) := isOpen_cayley_domain (P := P) (Q := Q)
  have h00 : (0 : lieU P Q) ∈ D0 P Q := zero_mem_cayley_domain (P := P) (Q := Q)
  have h1W : (1 : UpqT P Q) ∈ cayS (D0 P Q) := by
    have h := cayF_spec (P := P) (Q := Q) 0 h00
    rw [cayF_zero (P := P) (Q := Q)] at h
    exact ⟨0, h00, h⟩
  have hHua : HuaInv := huaInv_of_tauDeriv tau_derivative
  have hinv : ∀ (h : UpqT P Q) (S : Set (UpqT P Q)), MeasurableSet S → S ⊆ cayS (D0 P Q) →
      (fun g => h * g) '' S ⊆ cayS (D0 P Q) →
      betaH P Q lam ((fun g => h * g) '' S) = betaH P Q lam S :=
    fun h S hS hSW hhSW => hHua P Q lam hlam h S hS hSW hhSW

  have hcpt : ∀ K, IsCompact K → K ⊆ cayS (D0 P Q) → betaH P Q lam K ≠ ⊤ := by
    intro K hK hKW
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hCc : IsCompact (insert (0 : lieU P Q) (cayInv P Q '' K)) :=
      (hK.image_of_continuousOn ((continuousOn_cayInv (P := P) (Q := Q)).mono hKW)).insert 0
    have hC0 : insert (0 : lieU P Q) (cayInv P Q '' K) ⊆ D0 P Q := by
      rintro X (rfl | ⟨g, hg, rfl⟩)
      · exact h00
      · obtain ⟨Y, hY, hrel⟩ := hKW hg
        rw [cayley_inverse_iff P Q g Y hrel]
        exact hY
    obtain ⟨x0, -, hmax⟩ := hCc.exists_isMaxOn ⟨0, Set.mem_insert _ _⟩
      (fun x hx => (continuousAt_rhoH (P := P) (Q := Q) x (hC0 hx)).continuousWithinAt)
    have hS'm : MeasurableSet (cayF P Q ⁻¹' K ∩ D0 P Q) :=
      (measurable_cayF (P := P) (Q := Q) hKm).inter (isOpen_cell_domain (P := P) (Q := Q)).measurableSet
    have hS'C : cayF P Q ⁻¹' K ∩ D0 P Q ⊆ insert (0 : lieU P Q) (cayInv P Q '' K) :=
      fun X hX => Set.mem_insert_of_mem _ (preimage_subset_image (P := P) (Q := Q) K hX)
    rw [betaH_apply (P := P) (Q := Q) lam K hKm]
    apply ne_of_lt
    calc ∫⁻ X in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q X ∂lam
        ≤ ∫⁻ _ in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q x0 ∂lam := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hS'm] with X hX
          exact isMaxOn_iff.1 hmax X (hS'C hX)
      _ = rhoH P Q x0 * lam (cayF P Q ⁻¹' K ∩ D0 P Q) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 ENNReal.ofReal_ne_top)
          ((measure_mono hS'C).trans_lt hCc.measure_lt_top)

  have hne : betaH P Q lam (cayS (D0 P Q)) ≠ 0 := by
    rw [betaH_apply (P := P) (Q := Q) lam _ hW.measurableSet]
    have hpre : cayF P Q ⁻¹' cayS (D0 P Q) ∩ D0 P Q = D0 P Q :=
      Set.inter_eq_right.2 (fun X hX => ⟨X, hX, cayF_spec (P := P) (Q := Q) X hX⟩)
    rw [hpre]
    have hpos : 0 < lam (D0 P Q) := (isOpen_cell_domain (P := P) (Q := Q)).measure_pos lam ⟨0, h00⟩
    intro h0
    rw [lintegral_eq_zero_iff (measurable_rhoH (P := P) (Q := Q))] at h0
    have hF : ∀ᵐ x ∂(lam.restrict (D0 P Q)), False := by
      filter_upwards [h0, ae_restrict_mem (isOpen_cell_domain (P := P) (Q := Q)).measurableSet]
        with x hx hxD
      exact rhoH_pos (P := P) (Q := Q) x hxD hx
    rw [ae_iff] at hF
    simp only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply_univ] at hF
    exact hpos.ne' hF
  obtain ⟨t, ht0, httop, W', hW'1, hW'W, hβW'⟩ :=
    local_haar_unique (UpqT P Q) m hm (betaH P Q lam) (cayS (D0 P Q)) hW h1W hinv hcpt hne
  obtain ⟨V, hVW', hVo, h1V⟩ := mem_nhds_iff.1 hW'1
  have hβV : (betaH P Q lam).restrict V = t • m.restrict V := by
    have h := congrArg (fun μ : Measure (UpqT P Q) => μ.restrict V) hβW'
    simp only [Measure.restrict_restrict_of_subset hVW', Measure.restrict_smul] at h
    exact h
  have key : ∀ S ⊆ V, betaH P Q lam S = t * m S := by
    intro S hSV
    have h := congrArg (fun μ : Measure (UpqT P Q) => μ S) hβV
    simp only [Measure.smul_apply, Measure.restrict_apply' hVo.measurableSet,
      Set.inter_eq_left.2 hSV, smul_eq_mul] at h
    exact h

  set D : Set (lieU P Q) := D0 P Q ∩ cayF P Q ⁻¹' V with hDdef
  have hDnhds : D ∈ 𝓝 (0 : lieU P Q) := by
    have hc : ContinuousAt (cayF P Q) 0 :=
      (continuousOn_cayF (P := P) (Q := Q)).continuousAt
        ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00)
    have hV0 : V ∈ 𝓝 (cayF P Q 0) := by
      rw [cayF_zero (P := P) (Q := Q)]
      exact hVo.mem_nhds h1V
    exact Filter.inter_mem ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00) (hc.preimage_mem_nhds hV0)
  have hDmeas : MeasurableSet D :=
    (isOpen_cell_domain (P := P) (Q := Q)).measurableSet.inter
      (measurable_cayF (P := P) (Q := Q) hVo.measurableSet)
  have hcayS : cayS D = cayS (D0 P Q) ∩ cayInv P Q ⁻¹' D := by
    ext g
    constructor
    · rintro ⟨X, hXD, hrel⟩
      refine ⟨⟨X, hXD.1, hrel⟩, ?_⟩
      show cayInv P Q g ∈ D
      rw [cayley_inverse_iff P Q g X hrel]
      exact hXD
    · rintro ⟨⟨X, -, hrel⟩, hgD⟩
      have hgX := cayley_inverse_iff P Q g X hrel
      refine ⟨X, ?_, hrel⟩
      rw [← hgX]
      exact hgD
  refine ⟨D, hDnhds, hDmeas, fun X => t⁻¹ * rhoH P Q X,
    (measurable_rhoH (P := P) (Q := Q)).const_mul _, ?_, ?_, ?_, ?_⟩
  · exact (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.2 ht0)).continuousAt.comp
      (continuousAt_rhoH (P := P) (Q := Q) 0 h00)
  · exact mul_ne_zero (ENNReal.inv_ne_zero.2 httop) (rhoH_pos (P := P) (Q := Q) 0 h00)
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ht0) ENNReal.ofReal_ne_top
  · ext A hA
    have hSV : cayInv P Q ⁻¹' A ∩ cayS D ⊆ V := by
      rintro g ⟨-, X, hXD, hrel⟩
      rw [← cayF_eq_of (P := P) (Q := Q) g X hrel]
      exact hXD.2
    have hSmeas : MeasurableSet (cayInv P Q ⁻¹' A ∩ cayS D) := by
      rw [hcayS]
      exact (cayley_inverse_measurable P Q hA).inter (hW.measurableSet.inter (cayley_inverse_measurable P Q hDmeas))
    have hpre : cayF P Q ⁻¹' (cayInv P Q ⁻¹' A ∩ cayS D) ∩ D0 P Q = A ∩ D := by
      ext X
      constructor
      · rintro ⟨⟨hXA, Y, hYD, hrel⟩, hX0⟩
        have h1 : cayInv P Q (cayF P Q X) = X := cayInv_cayF (P := P) (Q := Q) X hX0
        have h2 : cayInv P Q (cayF P Q X) = Y := cayley_inverse_iff P Q _ Y hrel
        have hXY : X = Y := h1.symm.trans h2
        refine ⟨?_, by rw [hXY]; exact hYD⟩
        have hA' : cayInv P Q (cayF P Q X) ∈ A := hXA
        rwa [h1] at hA'
      · rintro ⟨hXA, hXD⟩
        refine ⟨⟨?_, X, hXD, cayF_spec (P := P) (Q := Q) X hXD.1⟩, hXD.1⟩
        show cayInv P Q (cayF P Q X) ∈ A
        rw [cayInv_cayF (P := P) (Q := Q) X hXD.1]
        exact hXA
    have hβS : betaH P Q lam (cayInv P Q ⁻¹' A ∩ cayS D) = ∫⁻ X in A ∩ D, rhoH P Q X ∂lam := by
      rw [betaH_apply (P := P) (Q := Q) lam _ hSmeas, hpre]
    rw [Measure.map_apply (cayley_inverse_measurable P Q) hA, Measure.restrict_apply (cayley_inverse_measurable P Q hA),
      withDensity_apply _ hA, Measure.restrict_restrict hA]
    calc m (cayInv P Q ⁻¹' A ∩ cayS D)
        = t⁻¹ * (t * m (cayInv P Q ⁻¹' A ∩ cayS D)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]
      _ = t⁻¹ * ∫⁻ X in A ∩ D, rhoH P Q X ∂lam := by rw [← key _ hSV, hβS]
      _ = ∫⁻ X in A ∩ D, t⁻¹ * rhoH P Q X ∂lam :=
          (lintegral_const_mul _ (measurable_rhoH (P := P) (Q := Q))).symm

end HcHDC
