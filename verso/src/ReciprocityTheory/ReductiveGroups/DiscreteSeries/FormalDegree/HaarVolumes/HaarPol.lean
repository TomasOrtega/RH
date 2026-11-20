import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPolB

noncomputable section

open Finset Matrix MeasureTheory Metric

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HPol

variable {n : ℕ}

/- English proof (translation)
Introduce `η hη`. Use `set η' : ℝ := min (η / 3) (1 / 2) with hη'def`. Establish `hη'0 : 0 < η'` using `lt_min (by positivity) (by norm_num)`. Establish `hη'1 : η' ≤ 1 / 2` using `min_le_right _ _`. Establish `hη'3 : η' ≤ η / 3` using `min_le_left _ _`.

Take `⟨δ1, hδ1, hE⟩` from `h η' hη'0`. Take `⟨δ4, hδ4, hE2⟩` from `h 2 (by norm_num)`. Take `⟨δ2, hδ2, hI⟩` from `HPol.image_est ε hη'0`. Take `⟨δ3, hδ3, hP⟩` from `HPol.polSet_eq_expSet ε`. Use `⟨min (min δ2 δ3) (min (δ1 / 2) (δ4 / 2)), lt_min (lt_min hδ2 hδ3) (lt_min (by positivity) (by positivity)), fun S hS hsmall => ?_⟩` and prove the remaining obligations.

Establish `hs2 : ∀ s ∈ S, ‖s‖ < δ2` using `fun s hs => lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_left _ _))`. Establish `hs3 : ∀ s ∈ S, ‖s‖ < δ3` using `fun s hs => lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_right _ _))`. Establish `hs1 : ∀ s ∈ S, ‖s‖ < δ1 / 2` using `fun s hs => lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_left _ _))`. Establish `hs4 : ∀ s ∈ S, ‖s‖ < δ4 / 2` using `fun s hs => lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_right _ _))`. Take `⟨hmeas, hnorm, hup, hlo⟩` from `hI S hS hs2`.

Establish `hsm1 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ1`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Use `hs1 s hs` as an intermediate fact. Combine the linear relations using `[hnorm s hs]`. Establish `hsm4 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ4`.

Introduce and unpack `_ ⟨s, hs, rfl⟩`. Use `hs4 s hs` as an intermediate fact. Combine the linear relations using `[hnorm s hs]`. Take `⟨hEu, hEl⟩` from `hE _ hmeas hsm1`. Use `beta_reduce at hEu hEl ⊢`.

Rewrite using `[hP S hs3]`. Establish `hsq1 : (1 + η') * (1 + η') ≤ 1 + η` using `by nlinarith`. Establish `hsq2 : 1 - η ≤ (1 - η') * (1 - η')` using `by nlinarith`. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc]`. Use `_ ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by gcongr`. Break down `le_or_gt 0 d with hd | hd` into its components or cases. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_of_nonpos (by nlinarith), zero_mul]`. Conclude with `zero_le`. Break down `le_or_gt 0 d with hd | hd` into its components or cases. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← ENNReal.ofReal_mul (mul_nonneg (by linarith) hd)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `_ = ENNReal.ofReal ((1 - η') * d) * (ENNReal.ofReal (1 - η') * volume S) := by`. Rewrite using `[mul_assoc]`.

Use `_ ≤ ENNReal.ofReal ((1 - η') * d) * volume (HPol.Lm '' S) := by gcongr`. Use `_ ≤ μ (expSet (HPol.Lm '' S)) := hEl`. Take `⟨hE2u, hE2l⟩` from `hE2 _ hmeas hsm4`. Use `beta_reduce at hE2u hE2l`. Establish `h3 : ENNReal.ofReal ((1 + 2) * d) = 0` using `ENNReal.ofReal_of_nonpos (by linarith)`.

Rewrite `hE2u` using `[h3, zero_mul]`. Establish `h0 : ENNReal.ofReal ((1 - 2) * d) * volume (HPol.Lm '' S) = 0` using `le_antisymm (hE2l.trans hE2u) (zero_le)`. Establish `hpos : ENNReal.ofReal ((1 - 2) * d) ≠ 0`. Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hvL : volume (HPol.Lm '' S) = 0` using `(mul_eq_zero.mp h0).resolve_left hpos`. Rewrite `hlo` using `[hvL]`. Establish `hpos' : ENNReal.ofReal (1 - η') ≠ 0`. Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hvS : volume S = 0` using `(mul_eq_zero.mp (le_antisymm hlo (zero_le))).resolve_left hpos'`. Rewrite using `[hvS, mul_zero]`. Conclude with `zero_le`.
-/
theorem haar_pol_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (d : ℝ)
    (h : DensOn (fun S => μ (expSet S)) d) : DensOn (fun S => μ (polSet S)) d := by
  intro η hη
  set η' : ℝ := min (η / 3) (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hη'3 : η' ≤ η / 3 := min_le_left _ _
  obtain ⟨δ1, hδ1, hE⟩ := h η' hη'0
  obtain ⟨δ4, hδ4, hE2⟩ := h 2 (by norm_num)
  obtain ⟨δ2, hδ2, hI⟩ := HPol.image_est ε hη'0
  obtain ⟨δ3, hδ3, hP⟩ := HPol.polSet_eq_expSet ε
  refine ⟨min (min δ2 δ3) (min (δ1 / 2) (δ4 / 2)),
    lt_min (lt_min hδ2 hδ3) (lt_min (by positivity) (by positivity)), fun S hS hsmall => ?_⟩
  have hs2 : ∀ s ∈ S, ‖s‖ < δ2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_left _ _))
  have hs3 : ∀ s ∈ S, ‖s‖ < δ3 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : ∀ s ∈ S, ‖s‖ < δ1 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : ∀ s ∈ S, ‖s‖ < δ4 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hmeas, hnorm, hup, hlo⟩ := hI S hS hs2
  have hsm1 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ1 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs1 s hs
    linarith [hnorm s hs]
  have hsm4 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ4 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs4 s hs
    linarith [hnorm s hs]
  obtain ⟨hEu, hEl⟩ := hE _ hmeas hsm1
  beta_reduce at hEu hEl ⊢
  rw [hP S hs3]
  have hsq1 : (1 + η') * (1 + η') ≤ 1 + η := by nlinarith
  have hsq2 : 1 - η ≤ (1 - η') * (1 - η') := by nlinarith
  constructor
  · calc μ (expSet (HPol.Lm '' S)) ≤ ENNReal.ofReal ((1 + η') * d) * volume (HPol.Lm '' S) := hEu
      _ ≤ ENNReal.ofReal ((1 + η') * d) * (ENNReal.ofReal (1 + η') * volume S) := by gcongr
      _ = (ENNReal.ofReal ((1 + η') * d) * ENNReal.ofReal (1 + η')) * volume S := by
        rw [mul_assoc]
      _ ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
        gcongr
        rcases le_or_gt 0 d with hd | hd
        · rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc (1 + η') * d * (1 + η') = ((1 + η') * (1 + η')) * d := by ring
            _ ≤ (1 + η) * d := mul_le_mul_of_nonneg_right hsq1 hd
        · rw [ENNReal.ofReal_of_nonpos (by nlinarith), zero_mul]
          exact zero_le
  · rcases le_or_gt 0 d with hd | hd
    · calc ENNReal.ofReal ((1 - η) * d) * volume S
          ≤ (ENNReal.ofReal ((1 - η') * d) * ENNReal.ofReal (1 - η')) * volume S := by
            gcongr
            rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) hd)]
            apply ENNReal.ofReal_le_ofReal
            calc (1 - η) * d ≤ ((1 - η') * (1 - η')) * d := mul_le_mul_of_nonneg_right hsq2 hd
              _ = (1 - η') * d * (1 - η') := by ring
        _ = ENNReal.ofReal ((1 - η') * d) * (ENNReal.ofReal (1 - η') * volume S) := by
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal ((1 - η') * d) * volume (HPol.Lm '' S) := by gcongr
        _ ≤ μ (expSet (HPol.Lm '' S)) := hEl
    ·
      obtain ⟨hE2u, hE2l⟩ := hE2 _ hmeas hsm4
      beta_reduce at hE2u hE2l
      have h3 : ENNReal.ofReal ((1 + 2) * d) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
      rw [h3, zero_mul] at hE2u
      have h0 : ENNReal.ofReal ((1 - 2) * d) * volume (HPol.Lm '' S) = 0 :=
        le_antisymm (hE2l.trans hE2u) (zero_le)
      have hpos : ENNReal.ofReal ((1 - 2) * d) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvL : volume (HPol.Lm '' S) = 0 := (mul_eq_zero.mp h0).resolve_left hpos
      rw [hvL] at hlo
      have hpos' : ENNReal.ofReal (1 - η') ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvS : volume S = 0 :=
        (mul_eq_zero.mp (le_antisymm hlo (zero_le))).resolve_left hpos'
      rw [hvS, mul_zero]
      exact zero_le

end ReciprocityTheory.ChartRestriction.DS
