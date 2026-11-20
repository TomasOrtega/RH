import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace GlobalTheory.TorsionForm.FlatAcyc

/- English proof (translation)
Establish `e1 : ∫ x in D, h (x + t) = ∫ x in (fun x => t + x) '' D, h x`. Rewrite using `[(measurePreserving_add_left volume t).setIntegral_image_emb (measurableEmbedding_addLeft t) h D]`. Simplify using `only [add_comm]`. Establish `e2 : (fun x => t + x) '' D = t +ᵥ D` using `rfl`. Rewrite using `[e1, e2]`.

Use `(hD.vadd_of_comm t).setIntegral_eq hD (fun l x => ?_)` and prove the remaining obligations. Rewrite using `[AddSubgroup.vadd_def, vadd_eq_add, add_comm]`. Conclude with `hper l l.2 x`.
-/
theorem setIntegral_add_right_of_periodic {g : ℕ} (M : Submodule ℤ (Fl g)) [Countable M.toAddSubgroup]
    {D : Set (Fl g)} (hD : IsAddFundamentalDomain M.toAddSubgroup D volume) (h : Fl g → ℂ)
    (hper : ∀ l ∈ M, ∀ x, h (x + l) = h x) (t : Fl g) :
    ∫ x in D, h (x + t) = ∫ x in D, h x := by
  have e1 : ∫ x in D, h (x + t) = ∫ x in (fun x => t + x) '' D, h x := by
    rw [(measurePreserving_add_left volume t).setIntegral_image_emb
      (measurableEmbedding_addLeft t) h D]
    simp only [add_comm]
  have e2 : (fun x => t + x) '' D = t +ᵥ D := rfl
  rw [e1, e2]
  refine (hD.vadd_of_comm t).setIntegral_eq hD (fun l x => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hper l l.2 x

/- English proof (translation)
Introduce `g M D hDm hDb hD F hF hper y`. Distinguish the cases in `hc : Countable M.toAddSubgroup`. Use `swap`. Establish `h0 : volume D = 0`. Assume the negation of the conclusion as `hne`.

Use `Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := volume) (As := fun l : M.toAddSubgroup => l +ᵥ D) (fun l => hD.nullMeasurableSet_vadd l) hD.aedisjoint` as an intermediate fact. Apply `hc` to reduce the goal to its premises. Establish `hu : {l : M.toAddSubgroup | 0 < volume (l +ᵥ D)} = Set.univ`. Use extensionality with `l`. Simplify using `only [Set.mem_setOf_eq, Set.mem_univ, iff_true, measure_vadd]`.

Conclude with `pos_iff_ne_zero.mpr hne`. Rewrite `this` using `[hu]`. Conclude with `Set.countable_univ_iff.mp this`. Conclude with `setIntegral_measure_zero _ h0`. Use `set f : Fl g → ℂ := fun x => fderiv ℝ F x y with hfdef`.

Establish `hdiff : Differentiable ℝ F` using `hF.differentiable one_ne_zero`. Establish `hfc : Continuous f` using `(hF.continuous_fderiv one_ne_zero).clm_apply continuous_const`. Establish `hfper : ∀ l ∈ M, ∀ x, f (x + l) = f x`. Introduce `l hl x`. Establish `e : (fun z => F (z + l)) = F` using `funext fun z => hper l hl z`.

Simplify using `only [hfdef]`. Rewrite using `[← fderiv_comp_add_right, e]`. Establish `hint : ∀ h : Fl g → ℂ, Continuous h → IntegrableOn h D volume` using `fun h hh => (hh.continuousOn.integrableOn_compact hDb.isCompact_closure).mono_set subset_closure`. Establish `hftc : ∀ x, F (x + y) - F x = ∫ s in (0:ℝ)..1, f (x + s • y)`. Introduce `x`.

Establish `hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => F (x + s • y)) (f (x + s • y)) s`. Introduce `s`. Establish `h1 : HasDerivAt (fun s : ℝ => x + s • y) y s`. Simplify using `using ((hasDerivAt_id s).smul_const y).const_add x`. Conclude with `(hdiff (x + s • y)).hasFDerivAt.comp_hasDerivAt s h1`.

Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) ((hfc.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _)]`. Simplify using the standard rewrite rules. Establish `hcont2 : Continuous (Function.uncurry fun (x : Fl g) (s : ℝ) => f (x + s • y))` using `hfc.comp (continuous_fst.add (continuous_snd.smul continuous_const))`. Establish `hint2 : Integrable (Function.uncurry fun (x : Fl g) (s : ℝ) => f (x + s • y)) ((volume.restrict D).prod (volume.restrict (Set.Ioc (0:ℝ) 1)))`. Rewrite using `[Measure.prod_restrict]`.

Use `(hcont2.continuousOn.integrableOn_compact (hDb.isCompact_closure.prod (isCompact_Icc (a := (0:ℝ)) (b := 1)))).mono_set ?_` and prove the remaining obligations. Conclude with `Set.prod_mono subset_closure Set.Ioc_subset_Icc_self`. Establish `hFc : Continuous F` using `hF.continuous`. Establish `key : ∫ x in D, (F (x + y) - F x) = ∫ x in D, f x`. Combine the equalities or inequalities in the displayed calculation.

Use `setIntegral_congr_fun hDm (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[hftc x, intervalIntegral.integral_of_le zero_le_one]`. Use `_ = ∫ s in Set.Ioc (0:ℝ) 1, ∫ x in D, f (x + s • y) := integral_integral_swap hint2`. Use `_ = ∫ s in Set.Ioc (0:ℝ) 1, ∫ x in D, f x := by`. Use `setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)` and prove the remaining obligations.

Conclude with `setIntegral_add_right_of_periodic M hD f hfper (s • y)`. Use `_ = ∫ x in D, f x := by simp`. Establish `hzero : ∫ x in D, (F (x + y) - F x) = 0`. Rewrite using `[integral_sub (hint (fun x => F (x + y)) (hFc.comp (continuous_id.add continuous_const))) (hint _ hFc), setIntegral_add_right_of_periodic M hD F hper y, sub_self]`. Rewrite using `[← key, hzero]`.
-/
theorem setIntegral_fderiv_apply_eq_zero_of_periodic :
    ∀ {g : ℕ} (M : Submodule ℤ (Fl g)) (D : Set (Fl g)), MeasurableSet D → Bornology.IsBounded D →
      IsAddFundamentalDomain M.toAddSubgroup D volume → ∀ (F : Fl g → ℂ), ContDiff ℝ 1 F →
      (∀ l ∈ M, ∀ x, F (x + l) = F x) → ∀ y : Fl g, ∫ x in D, fderiv ℝ F x y = 0 := by
  intro g M D hDm hDb hD F hF hper y
  by_cases hc : Countable M.toAddSubgroup
  swap
  · have h0 : volume D = 0 := by
      by_contra hne
      have := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := volume)
        (As := fun l : M.toAddSubgroup => l +ᵥ D) (fun l => hD.nullMeasurableSet_vadd l) hD.aedisjoint
      apply hc
      have hu : {l : M.toAddSubgroup | 0 < volume (l +ᵥ D)} = Set.univ := by
        ext l
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, measure_vadd]
        exact pos_iff_ne_zero.mpr hne
      rw [hu] at this
      exact Set.countable_univ_iff.mp this
    exact setIntegral_measure_zero _ h0
  set f : Fl g → ℂ := fun x => fderiv ℝ F x y with hfdef
  have hdiff : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hfc : Continuous f := (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfper : ∀ l ∈ M, ∀ x, f (x + l) = f x := by
    intro l hl x
    have e : (fun z => F (z + l)) = F := funext fun z => hper l hl z
    simp only [hfdef]
    rw [← fderiv_comp_add_right, e]
  have hint : ∀ h : Fl g → ℂ, Continuous h → IntegrableOn h D volume := fun h hh =>
    (hh.continuousOn.integrableOn_compact hDb.isCompact_closure).mono_set subset_closure

  have hftc : ∀ x, F (x + y) - F x = ∫ s in (0:ℝ)..1, f (x + s • y) := by
    intro x
    have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => F (x + s • y)) (f (x + s • y)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => x + s • y) y s := by
        simpa using ((hasDerivAt_id s).smul_const y).const_add x
      exact (hdiff (x + s • y)).hasFDerivAt.comp_hasDerivAt s h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      ((hfc.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _)]
    simp

  have hcont2 : Continuous (Function.uncurry fun (x : Fl g) (s : ℝ) => f (x + s • y)) :=
    hfc.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hint2 : Integrable (Function.uncurry fun (x : Fl g) (s : ℝ) => f (x + s • y))
      ((volume.restrict D).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    refine (hcont2.continuousOn.integrableOn_compact
      (hDb.isCompact_closure.prod (isCompact_Icc (a := (0:ℝ)) (b := 1)))).mono_set ?_
    exact Set.prod_mono subset_closure Set.Ioc_subset_Icc_self
  have hFc : Continuous F := hF.continuous
  have key : ∫ x in D, (F (x + y) - F x) = ∫ x in D, f x := by
    calc ∫ x in D, (F (x + y) - F x) = ∫ x in D, ∫ s in Set.Ioc (0:ℝ) 1, f (x + s • y) := by
          refine setIntegral_congr_fun hDm (fun x _ => ?_)
          rw [hftc x, intervalIntegral.integral_of_le zero_le_one]
      _ = ∫ s in Set.Ioc (0:ℝ) 1, ∫ x in D, f (x + s • y) := integral_integral_swap hint2
      _ = ∫ s in Set.Ioc (0:ℝ) 1, ∫ x in D, f x := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
          exact setIntegral_add_right_of_periodic M hD f hfper (s • y)
      _ = ∫ x in D, f x := by simp
  have hzero : ∫ x in D, (F (x + y) - F x) = 0 := by
    rw [integral_sub (hint (fun x => F (x + y)) (hFc.comp (continuous_id.add continuous_const))) (hint _ hFc),
      setIntegral_add_right_of_periodic M hD F hper y, sub_self]
  rw [← key, hzero]

end GlobalTheory.TorsionForm.FlatAcyc
