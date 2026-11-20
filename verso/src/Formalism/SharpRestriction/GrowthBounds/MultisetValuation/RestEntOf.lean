import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelProductForm
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExpansionAllPlacesOfPlace

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

/- English proof (translation)
Unfold `Pend.PhAt`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ (th_be_const hbe)`.
-/
theorem en_PhAt_const (hbe : BeProp p Y.be) (j : ℕ) (v : X.Pl) : MvPowerSeries.constantCoeff (Y.PhAt j v) = 0 := by
  unfold Pend.PhAt
  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ (th_be_const hbe)

/- English proof (translation)
Introduce `hA j hj La La' h1 h2 φ`. Take `⟨Ph, U0, hTh, hU0, _, hbe, hPh⟩` from `hA.2.2.1 j hj La La' h1 h2 φ`. Establish `hcz` using `charZero_K' p (K0 p)`. Establish `hΨ : (∑ e : X.EA j, sub2 p Y.be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) = ∑ v, Y.PhAt j v`. Unfold `Pend.PhAt`.

Conclude with `Fintype.sum_sigma _`. Rewrite `hPh` using `[hΨ]`. Take `⟨hc0, h, hh0, hE⟩` from `hPh`. Establish `hE0 : E0 p (inParam p (Ph - ∑ v, Y.PhAt j v))` using `⟨th_inParam_const p hc0, h, hh0, hE⟩`. Take `⟨w, hw⟩` from `exp_neg_integral p hE0`.

Use `⟨MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-(Ph - ∑ v, Y.PhAt j v))) * U0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[en_inParamK_mul]`. Use `en_IntR_mul ?_ hU0` and prove the remaining obligations. Establish `e1 : inParam p (expS p (-(Ph - ∑ v, Y.PhAt j v))) = expK (inParam p (-(Ph - ∑ v, Y.PhAt j v)))`. Unfold `inParam`.

Conclude with `th_subst_expK _ (fun i => by`. Use `th_lX_const p (K0 p) i` as an intermediate fact. Rewrite using `[Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hc0, neg_zero])` and apply the resulting hypothesis. Rewrite using `[th_inParamK_map p (K0 p) Y.Kc, ← th_inParam_eq, e1, th_inParam_neg, hw]`. Introduce `n`.

Rewrite using `[MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]`. Conclude with `Y.witt_mem_integers_Cp _`. Establish `e2 : -Ph = ∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v)`. Rewrite using `[Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e3 : expS p (-Ph) = (∏ v, expS p (-Y.PhAt j v)) * expS p (-(Ph - ∑ v, Y.PhAt j v))`. Establish `a1 : expK (∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v)) = expK (∑ v, (-Y.PhAt j v)) * expK (-(Ph - ∑ v, Y.PhAt j v))` using `expK_add (by`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero])`. Use the proof step `(by rw [map_neg, hc0, neg_zero])`.

Establish `a2 : expK (∑ v, (-Y.PhAt j v)) = ∏ v, expK (-Y.PhAt j v)` using `th_expK_sum _ _ fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero]`. Rewrite using `[e2]`. Conclude with `a1.trans (by rw [a2]; rfl)`. Rewrite using `[hTh, e3, map_mul, map_prod, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem kernel_product_form (D : Formalism.BasicNotions.D7) : KernelProductForm X Y D := by
  intro hA j hj La La' h1 h2 φ
  obtain ⟨Ph, U0, hTh, hU0, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  have hcz := charZero_K' p (K0 p)
  have hΨ : (∑ e : X.EA j, sub2 p Y.be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
      MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) = ∑ v, Y.PhAt j v := by
    unfold Pend.PhAt
    exact Fintype.sum_sigma _
  rw [hΨ] at hPh
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hE0 : E0 p (inParam p (Ph - ∑ v, Y.PhAt j v)) := ⟨th_inParam_const p hc0, h, hh0, hE⟩
  obtain ⟨w, hw⟩ := exp_neg_integral p hE0
  refine ⟨MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-(Ph - ∑ v, Y.PhAt j v))) * U0, ?_, ?_⟩
  · rw [en_inParamK_mul]
    refine en_IntR_mul ?_ hU0
    have e1 : inParam p (expS p (-(Ph - ∑ v, Y.PhAt j v))) = expK (inParam p (-(Ph - ∑ v, Y.PhAt j v))) := by
      unfold inParam
      exact th_subst_expK _ (fun i => by
        have := th_lX_const p (K0 p) i
        rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hc0, neg_zero])
    rw [th_inParamK_map p (K0 p) Y.Kc, ← th_inParam_eq, e1, th_inParam_neg, hw]
    intro n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    exact Y.witt_mem_integers_Cp _
  · have e2 : -Ph = ∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v) := by
      rw [Finset.sum_neg_distrib]; ring
    have e3 : expS p (-Ph) = (∏ v, expS p (-Y.PhAt j v)) * expS p (-(Ph - ∑ v, Y.PhAt j v)) := by
      have a1 : expK (∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v)) =
          expK (∑ v, (-Y.PhAt j v)) * expK (-(Ph - ∑ v, Y.PhAt j v)) :=
        expK_add (by
          rw [map_sum]
          exact Finset.sum_eq_zero fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero])
          (by rw [map_neg, hc0, neg_zero])
      have a2 : expK (∑ v, (-Y.PhAt j v)) = ∏ v, expK (-Y.PhAt j v) :=
        th_expK_sum _ _ fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero]
      rw [e2]
      exact a1.trans (by rw [a2]; rfl)
    rw [hTh, e3, map_mul, map_prod, mul_assoc]
    rfl

/- English proof (translation)
The claim follows from `restPlaces_of D (kernel_product_form X Y D)`.
-/
theorem restPlaces (D : Formalism.BasicNotions.D7) : RestPlaces X Y D := restPlaces_of D (kernel_product_form X Y D)

/- English proof (translation)
The claim follows from `restEnt_of_rest D (restPlaces X Y D) h2 hB hA`.
-/
theorem restEnt_of (D : Formalism.BasicNotions.D7) (h2 : PlacewiseLowerBoundEvenShift X Y D) (hB : RestBU X Y D) (hA : admitted D X Y) : EntCondition X Y :=
  restEnt_of_rest D (restPlaces X Y D) h2 hB hA

end Formalism.MainNotions.FormalGroupSystem.Pf
