import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.NearOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k)` using `(IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨1, one_ne_zero, subset_rfl⟩`. Establish `hc : Filter.Tendsto (fun x : k => x - a) (nhds a) (nhds 0)`. Establish `: Continuous (fun x : k => x - a)` using `by fun_prop`. Simplify using `using this.tendsto a`. Conclude with `hc h0`.
-/
theorem eventually_valuation_sub_lt_one (a : k) : ∀ᶠ x in nhds a, valuation k (x - a) < 1 := by
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨1, one_ne_zero, subset_rfl⟩
  have hc : Filter.Tendsto (fun x : k => x - a) (nhds a) (nhds 0) := by
    have : Continuous (fun x : k => x - a) := by fun_prop
    simpa using this.tendsto a
  exact hc h0

/- English proof (translation)
Establish `hk : ∀ s ∈ nhds (0 : k), ∀ᶠ d in nhds (0 : k), {x : k | valuation k x ≤ valuation k d} ⊆ s`. Introduce `s hs`. Take `⟨r, hr, hrs⟩` from `(IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs`. Establish `h0 : {x : k | valuation k x < r} ∈ nhds (0 : k)` using `(IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨r, hr, subset_rfl⟩`. Use `filter_upwards [h0] with d hd x hx`.

Conclude with `hrs (lt_of_le_of_lt hx hd)`. Establish `hS' : {x : Fin p → Fin q → k | Matrix.of x ∈ S} ∈ nhds (0 : Fin p → Fin q → k)` using `hS`. Rewrite `hS'` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, t, ht, hI⟩` from `hS'`. Establish `ht' : ∀ i, ∃ u : Fin q → Set k, (∀ j, u j ∈ nhds (0 : k)) ∧ Set.univ.pi u ⊆ t i`.

Introduce `i`. Establish `h` using `ht i`. Rewrite `h` using `[nhds_pi, Filter.mem_pi']`. Take `⟨J, u, hu, hJ⟩` from `h`. Conclude with `⟨u, hu, fun x hx => hJ fun j _ => hx j trivial⟩`.

Use `choose u hu hut using ht'`. Establish `hev : ∀ᶠ d in nhds (0 : k), valuation k (d - 0) < 1 ∧ ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j` using `(eventually_valuation_sub_lt_one 0).and (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hk _ (hu i j))`. Establish `hne : ∃ d : k, d ≠ 0 ∧ valuation k (d - 0) < 1 ∧ ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j`. Establish `hd : (nhdsWithin (0 : k) {0}ᶜ).NeBot`. Rewrite using `[← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]`.

Introduce `s hs`. Take `⟨r, hr, hrs⟩` from `(IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs`. Take `⟨r', hr', hr1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := valuation k)`. Take `⟨y, rfl⟩` from `ValuativeRel.valuation_surjective r`. Establish `hy : y ≠ 0` using `by simpa using hr`.

Use `⟨r' * y, hrs ?_, mul_ne_zero (by simpa using hr') hy⟩` and prove the remaining obligations. Use `show valuation k (r' * y) < valuation k y`. Rewrite using `[map_mul]`. Conclude with `mul_lt_of_lt_one_left (zero_lt_iff.mpr hr) hr1`. Conclude with `(eventually_mem_nhdsWithin.and (hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)))).exists`.

Take `⟨d, hd0, hd1, hdu⟩` from `hne`. Use `⟨Units.mk0 d hd0, by simpa using hd1.le, fun X hX => hI fun i _ => hut i fun j _ => hdu i j (hX i j)⟩` and prove the remaining obligations.
-/
theorem exists_box_subset_of_mem_nhds_zero {p q : ℕ} {S : Set (Matrix (Fin p) (Fin q) k)} (hS : S ∈ nhds 0) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ box p q d ⊆ S := by
  have hk : ∀ s ∈ nhds (0 : k), ∀ᶠ d in nhds (0 : k), {x : k | valuation k x ≤ valuation k d} ⊆ s := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
    have h0 : {x : k | valuation k x < r} ∈ nhds (0 : k) :=
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨r, hr, subset_rfl⟩
    filter_upwards [h0] with d hd x hx
    exact hrs (lt_of_le_of_lt hx hd)
  have hS' : {x : Fin p → Fin q → k | Matrix.of x ∈ S} ∈ nhds (0 : Fin p → Fin q → k) := hS
  rw [nhds_pi, Filter.mem_pi'] at hS'
  obtain ⟨I, t, ht, hI⟩ := hS'
  have ht' : ∀ i, ∃ u : Fin q → Set k, (∀ j, u j ∈ nhds (0 : k)) ∧ Set.univ.pi u ⊆ t i := by
    intro i
    have h := ht i
    rw [nhds_pi, Filter.mem_pi'] at h
    obtain ⟨J, u, hu, hJ⟩ := h
    exact ⟨u, hu, fun x hx => hJ fun j _ => hx j trivial⟩
  choose u hu hut using ht'
  have hev : ∀ᶠ d in nhds (0 : k), valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j :=
    (eventually_valuation_sub_lt_one 0).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hk _ (hu i j))
  have hne : ∃ d : k, d ≠ 0 ∧ valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j := by
    have hd : (nhdsWithin (0 : k) {0}ᶜ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
      intro s hs
      obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
      obtain ⟨r', hr', hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
      obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective r
      have hy : y ≠ 0 := by simpa using hr
      refine ⟨r' * y, hrs ?_, mul_ne_zero (by simpa using hr') hy⟩
      show valuation k (r' * y) < valuation k y
      rw [map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.mpr hr) hr1
    exact (eventually_mem_nhdsWithin.and (hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)))).exists
  obtain ⟨d, hd0, hd1, hdu⟩ := hne
  refine ⟨Units.mk0 d hd0, by simpa using hd1.le, fun X hX => hI fun i _ => hut i fun j _ => hdu i j (hX i j)⟩

/- English proof (translation)
Establish `hadd : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => 1 + N) (nhds 0) (nhds 1)`. Establish `: Continuous (fun N : Matrix (Fin n) (Fin n) k => 1 + N)` using `by fun_prop`. Simplify using `using this.tendsto 0`. Establish `hdet : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N).det) (nhds 0) (nhds 1)`. Establish `: Continuous (fun M : Matrix (Fin n) (Fin n) k => M.det)` using `continuous_id.matrix_det`.

Establish `h2` using `(this.tendsto 1).comp hadd`. Rewrite `h2` using `[det_one]`. Conclude with `h2`. Establish `hinv : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N)⁻¹) (nhds 0) (nhds 1)`. Establish `: ContinuousAt Inv.inv (1 : Matrix (Fin n) (Fin n) k)`.

Apply `continuousAt_matrix_inv` to reduce the goal to its premises. Rewrite using `[det_one, Ring.inverse_eq_inv']`. Conclude with `continuousAt_inv₀ one_ne_zero`. Establish `h2` using `this.tendsto.comp hadd`. Rewrite `h2` using `[inv_one]`.

Conclude with `h2`. Establish `hv : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, valuation k (1 + N).det = 1` using `by filter_upwards [hdet (eventually_valuation_sub_lt_one 1)] with N hN`. Establish `hN' : valuation k ((1 + N).det - 1) < 1` using `hN`. Use `Valuation.map_one_add_of_lt (valuation k) hN'` as an intermediate fact. Simplify using `using this`.

Establish `hb : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, ∀ i j, valuation k ((1 + N)⁻¹ i j) ≤ 1`. Use `Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_` and prove the remaining obligations. Establish `hc : Continuous (fun M : Matrix (Fin n) (Fin n) k => M i j)` using `continuous_id.matrix_elem i j`. Use `filter_upwards [((hc.tendsto 1).comp hinv) (eventually_valuation_sub_lt_one _)] with N hN`. Establish `hN' : valuation k ((1 + N)⁻¹ i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1` using `hN`.

Establish `h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1`. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `Valuation.map_add_le (valuation k) hN'.le h1` as an intermediate fact. Simplify using `using this`.

Establish `hval : ∀ N : Matrix (Fin n) (Fin n) k, valuation k (1 + N).det = 1 → (toGL (1 + N)).val = 1 + N`. Introduce `N hN`. Establish `hu : IsUnit (1 + N)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Introduce `h`.

Rewrite `hN` using `[h]`. Simplify using `at hN`. Unfold `toGL`. Rewrite using `[dif_pos hu]`. Both sides reduce to the same expression.

Establish `hGL : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => toGL (1 + N)) (nhds 0) (nhds 1)`. Rewrite using `[Units.isInducing_embedProduct.tendsto_nhds_iff]`. Establish `h3` using `hadd.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp hinv)`. Establish `e : (Units.embedProduct _ (1 : GL (Fin n) k)) = (1, MulOpposite.op 1)` using `by simp`. Rewrite using `[e]`.

Use `Filter.Tendsto.congr' ?_ h3` and prove the remaining obligations. Use `filter_upwards [hv] with N hN`. Simplify using `only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, hval N hN]`. Take `⟨d, hd, hS⟩` from `exists_box_subset_of_mem_nhds_zero (hv.and (hb.and (hGL hU)))`. Use `⟨d, hd, fun N hN => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2, h3⟩` from `hS hN`. Use `⟨toGL (1 + N), hval N h1, h3, ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[GeneralLinearGroup.val_det_apply, hval N h1, h1]`. Rewrite using `[Matrix.coe_units_inv, hval N h1]`. Simplify using `using h2 i j`.
-/
theorem one_add_small_near_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ ∀ N ∈ box n n d, ∃ A : GL (Fin n) k, A.val = 1 + N ∧ A ∈ U ∧
      valuation k (GeneralLinearGroup.det A : k) = 1 ∧ A⁻¹.val ∈ box n n 1 := by
  have hadd : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => 1 + N) (nhds 0) (nhds 1) := by
    have : Continuous (fun N : Matrix (Fin n) (Fin n) k => 1 + N) := by fun_prop
    simpa using this.tendsto 0
  have hdet : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N).det) (nhds 0) (nhds 1) := by
    have : Continuous (fun M : Matrix (Fin n) (Fin n) k => M.det) := continuous_id.matrix_det
    have h2 := (this.tendsto 1).comp hadd
    rw [det_one] at h2
    exact h2
  have hinv : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N)⁻¹) (nhds 0) (nhds 1) := by
    have : ContinuousAt Inv.inv (1 : Matrix (Fin n) (Fin n) k) := by
      apply continuousAt_matrix_inv
      rw [det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h2 := this.tendsto.comp hadd
    rw [inv_one] at h2
    exact h2
  have hv : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, valuation k (1 + N).det = 1 := by
    filter_upwards [hdet (eventually_valuation_sub_lt_one 1)] with N hN
    have hN' : valuation k ((1 + N).det - 1) < 1 := hN
    have := Valuation.map_one_add_of_lt (valuation k) hN'
    simpa using this
  have hb : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, ∀ i j, valuation k ((1 + N)⁻¹ i j) ≤ 1 := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have hc : Continuous (fun M : Matrix (Fin n) (Fin n) k => M i j) := continuous_id.matrix_elem i j
    filter_upwards [((hc.tendsto 1).comp hinv) (eventually_valuation_sub_lt_one _)] with N hN
    have hN' : valuation k ((1 + N)⁻¹ i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := hN
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have := Valuation.map_add_le (valuation k) hN'.le h1
    simpa using this
  have hval : ∀ N : Matrix (Fin n) (Fin n) k, valuation k (1 + N).det = 1 → (toGL (1 + N)).val = 1 + N := by
    intro N hN
    have hu : IsUnit (1 + N) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h
      rw [h] at hN
      simp at hN
    unfold toGL
    rw [dif_pos hu]
    rfl
  have hGL : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => toGL (1 + N)) (nhds 0) (nhds 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have h3 := hadd.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp hinv)
    have e : (Units.embedProduct _ (1 : GL (Fin n) k)) = (1, MulOpposite.op 1) := by simp
    rw [e]
    refine Filter.Tendsto.congr' ?_ h3
    filter_upwards [hv] with N hN
    simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, hval N hN]
  obtain ⟨d, hd, hS⟩ := exists_box_subset_of_mem_nhds_zero (hv.and (hb.and (hGL hU)))
  refine ⟨d, hd, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS hN
  refine ⟨toGL (1 + N), hval N h1, h3, ?_, fun i j => ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, hval N h1, h1]
  · rw [Matrix.coe_units_inv, hval N h1]
    simpa using h2 i j

end GlobalTheory.GamMul.NearOne
