import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineMultihomogClassify

namespace ReciprocityTheory.AnForm.R

open MvPolynomial OnePoint

noncomputable section

def projLineAffineCoordinate : Fin 2 → OnePoint ℂ → Fin 1 → ℂ :=
  fun i x _ => if i = 0 then x.elim 0 id else x.elim 0 (fun z => z⁻¹)

def projectiveLineSource : Fin 2 → Set (OnePoint ℂ) :=
  fun i => if i = 0 then Set.range ((↑) : ℂ → OnePoint ℂ) else {x | x ≠ ((0 : ℂ) : OnePoint ℂ)}

def homogeneousLift : Fin 2 → (Σ _ : Unit, Fin 2) → MvPolynomial (Fin 1) ℂ :=
  fun i q => if q.2 = i then 1 else X 0

def p1Bd : Fin 2 → Ideal (MvPolynomial (Fin 1) ℂ) :=
  fun i => if i = 0 then ⊤ else Ideal.span {X 0}

/- English proof (translation)
Use `revert i`. Evaluate the decidable proposition.
-/
theorem finset_fin_two_eq_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

/- English proof (translation)
Simplify using `[p1Bd]`.
-/
theorem projectiveLineBoundary_zero : p1Bd 0 = ⊤ := by
  simp [p1Bd]

/- English proof (translation)
Simplify using `[p1Bd]`.
-/
theorem projectiveLineBoundary_one : p1Bd 1 = Ideal.span {X 0} := by
  simp [p1Bd]

def projectiveLineSncData (i : Fin 2) (y : Fin 1 → ℂ) : SncData (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (p1Bd i) y 1 1 where
  r := fun _ => X 0 - C (y 0)
  J := if i = 1 ∧ y 0 = 0 then {0} else ∅
  h := if i = 0 then 1 else if y 0 = 0 then 1 else X 0
  σ := fun _ => if i = 1 ∧ y 0 = 0 then Option.some 0 else Option.none
  σ_injOn := fun a _ b _ _ => Subsingleton.elim a b
  σ_eq_none := by
    intro l
    have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    by_cases h : i = 1 ∧ y 0 = 0 <;> simp [h]
  span_eq := by
    have hf : (fun l : Fin 1 => algebraMap (MvPolynomial (Fin 1) ℂ) (locRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) y)
        (X 0 - C (y 0))) = (algebraMap (MvPolynomial (Fin 1) ℂ) (locRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) y)) ∘
          (fun l : Fin 1 => X l - C (y l)) := by
      funext l
      rw [Subsingleton.elim l 0]
      rfl
    rw [hf, Set.range_comp, ← Ideal.map_span, ← ptIdeal_eq_span]
  eval_h := by
    by_cases h0 : i = 0 <;> by_cases h1 : y 0 = 0 <;> simp [h0, h1]
  mem_bd := by
    obtain rfl | rfl := finset_fin_two_eq_cases i
    · rw [projectiveLineBoundary_zero]; exact Submodule.mem_top
    · rw [projectiveLineBoundary_one]
      by_cases h1 : y 0 = 0
      · simp [h1]
      · simp [h1]
  le_span := by
    intro g hg
    by_cases hc : i = 1 ∧ y 0 = 0
    · obtain ⟨rfl, h1⟩ := hc
      rw [projectiveLineBoundary_one] at hg
      simpa [h1] using hg
    · simp [hc]

/- English proof (translation)
Simplify using `[projectiveLineSource]`.
-/
theorem projectiveLineSource_zero : projectiveLineSource 0 = Set.range ((↑) : ℂ → OnePoint ℂ) := by
  simp [projectiveLineSource]

/- English proof (translation)
Simplify using `[projectiveLineSource]`.
-/
theorem projectiveLineSource_one : projectiveLineSource 1 = {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} := by
  simp [projectiveLineSource]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[projLineAffineCoordinate]`.
-/
theorem projectiveLineCoord_zero (x : OnePoint ℂ) : projLineAffineCoordinate 0 x = fun _ => x.elim 0 id := by
  funext l
  simp [projLineAffineCoordinate]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[projLineAffineCoordinate]`.
-/
theorem projectiveLineCoord_one (x : OnePoint ℂ) : projLineAffineCoordinate 1 x = fun _ => x.elim 0 (fun z => z⁻¹) := by
  funext l
  simp [projLineAffineCoordinate]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projectiveLineLift_zero (q : Σ _ : Unit, Fin 2) : homogeneousLift 0 q = if q.2 = 0 then 1 else X 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projectiveLineLift_one (q : Σ _ : Unit, Fin 2) : homogeneousLift 1 q = if q.2 = 1 then 1 else X 0 := rfl

/- English proof (translation)
Break down `x with _ | z` into its components or cases. Conclude with `Or.inl rfl`. Conclude with `Or.inr ⟨z, rfl⟩`.
-/
private theorem onePoint_eq_infty_or_exists_coe (x : OnePoint ℂ) : x = ∞ ∨ ∃ z : ℂ, x = (z : OnePoint ℂ) := by
  rcases x with _ | z
  · exact Or.inl rfl
  · exact Or.inr ⟨z, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem onePoint_elim_coe (z a : ℂ) (f : ℂ → ℂ) : (z : OnePoint ℂ).elim a f = f z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem onePoint_elim_infty (a : ℂ) (f : ℂ → ℂ) : (∞ : OnePoint ℂ).elim a f = a := rfl

/- English proof (translation)
Rewrite using `[projectiveLineSource_zero]`. Conclude with `⟨w, rfl⟩`.
-/
private theorem coe_mem_projectiveLineSource_zero (w : ℂ) : (w : OnePoint ℂ) ∈ projectiveLineSource 0 := by
  rw [projectiveLineSource_zero]
  exact ⟨w, rfl⟩

/- English proof (translation)
Rewrite using `[projectiveLineSource_one, Set.mem_setOf_eq]`. Conclude with `fun h => hw (OnePoint.coe_injective h)`.
-/
private theorem coe_mem_projectiveLineSource_one_of_ne_zero {w : ℂ} (hw : w ≠ 0) : (w : OnePoint ℂ) ∈ projectiveLineSource 1 := by
  rw [projectiveLineSource_one, Set.mem_setOf_eq]
  exact fun h => hw (OnePoint.coe_injective h)

/- English proof (translation)
Rewrite using `[projectiveLineSource_one, Set.mem_setOf_eq]`. Conclude with `OnePoint.infty_ne_coe 0`.
-/
private theorem infty_mem_projectiveLineSource_one : (∞ : OnePoint ℂ) ∈ projectiveLineSource 1 := by
  rw [projectiveLineSource_one, Set.mem_setOf_eq]
  exact OnePoint.infty_ne_coe 0

/- English proof (translation)
Rewrite `h` using `[projectiveLineSource_zero, projectiveLineSource_one, Set.mem_inter_iff, Set.mem_setOf_eq]`. Take `⟨⟨z, rfl⟩, h1⟩` from `h`. Conclude with `⟨z, fun hz => h1 (by rw [hz]), rfl⟩`.
-/
theorem projectiveLine_mem_inter {x : OnePoint ℂ} (h : x ∈ projectiveLineSource 0 ∩ projectiveLineSource 1) :
    ∃ z : ℂ, z ≠ 0 ∧ x = (z : OnePoint ℂ) := by
  rw [projectiveLineSource_zero, projectiveLineSource_one, Set.mem_inter_iff, Set.mem_setOf_eq] at h
  obtain ⟨⟨z, rfl⟩, h1⟩ := h
  exact ⟨z, fun hz => h1 (by rw [hz]), rfl⟩

/- English proof (translation)
Rewrite `hx` using `[projectiveLineSource_one, Set.mem_setOf_eq]`. Take `rfl | ⟨z, rfl⟩` from `onePoint_eq_infty_or_exists_coe x`. Both sides reduce to the same expression. It suffices to derive a contradiction. Establish `hz : z⁻¹ = 0` using `h`.

Rewrite `hz` using `[inv_eq_zero]`. Conclude with `hx (by rw [hz])`.
-/
theorem projectiveLine_coord_inf_eq_zero {x : OnePoint ℂ} (hx : x ∈ projectiveLineSource 1)
    (h : x.elim 0 (fun z => z⁻¹) = 0) : x = ∞ := by
  rw [projectiveLineSource_one, Set.mem_setOf_eq] at hx
  obtain rfl | ⟨z, rfl⟩ := onePoint_eq_infty_or_exists_coe x
  · rfl
  · exfalso
    have hz : z⁻¹ = 0 := h
    rw [inv_eq_zero] at hz
    exact hx (by rw [hz])

/- English proof (translation)
Simplify using `only [conePts, Set.mem_setOf_eq]`. Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Consider the cases of `k`. Conclude with `h`. Rewrite `hf` using `[Ideal.mem_bot]`.

Rewrite using `[hf, map_zero]`.
-/
theorem projectiveLine_mem_conePts_bot (z : (Σ _ : Unit, Fin 2) → ℂ) (h : ∃ j, z ⟨(), j⟩ ≠ 0) :
    z ∈ conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)) := by
  simp only [conePts, Set.mem_setOf_eq]
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · cases k
    exact h
  · rw [Ideal.mem_bot] at hf
    rw [hf, map_zero]

/- English proof (translation)
Simplify using `only [conePts, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1 (), ?_⟩` and prove the remaining obligations. Use `h2 _ (Ideal.subset_span (Set.mem_singleton _))` as an intermediate fact.

Simplify using `using this`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Consider the cases of `k`. Conclude with `h1`.

Take `⟨g, rfl⟩` from `Ideal.mem_span_singleton'.mp hf`. Simplify using `[h2]`.
-/
theorem projectiveLine_mem_conePts_span (z : (Σ _ : Unit, Fin 2) → ℂ) :
    z ∈ conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)) ↔
      (∃ j, z ⟨(), j⟩ ≠ 0) ∧ z ⟨(), 0⟩ = 0 := by
  simp only [conePts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 (), ?_⟩
    have := h2 _ (Ideal.subset_span (Set.mem_singleton _))
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · cases k
      exact h1
    · obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      simp [h2]

/- English proof (translation)
Simplify using `only [conePts, Set.mem_setOf_eq]`. Use `⟨fun k => ⟨i, ?_⟩, fun f hf => ?_⟩` and prove the remaining obligations. Simplify using `[homogeneousLift]`. Rewrite `hf` using `[Ideal.mem_bot]`. Rewrite using `[hf, map_zero]`.
-/
theorem projectiveLine_lift_mem_conePts (i : Fin 2) (x : OnePoint ℂ) :
    (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q)) ∈
      conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)) := by
  simp only [conePts, Set.mem_setOf_eq]
  refine ⟨fun k => ⟨i, ?_⟩, fun f hf => ?_⟩
  · simp [homogeneousLift]
  · rw [Ideal.mem_bot] at hf
    rw [hf, map_zero]

/- English proof (translation)
Take `rfl | rfl` from `finset_fin_two_eq_cases i`. Rewrite `hx` using `[projectiveLineSource_zero]`. Take `⟨z, rfl⟩` from `hx`. Simplify using `[homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe]`. Take `rfl | ⟨z, rfl⟩` from `onePoint_eq_infty_or_exists_coe x`.

Conclude with `absurd (by simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_infty]) h0`. Establish `hz : z ≠ 0`. Introduce `hz`. Rewrite `hx` using `[projectiveLineSource_one, Set.mem_setOf_eq]`. Conclude with `hx (by rw [hz])`.

Simplify using `[homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hz]`.
-/
theorem projectiveLine_point_eq_ratio (i : Fin 2) (x : OnePoint ℂ) (hx : x ∈ projectiveLineSource i)
    (h0 : eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨(), 0⟩) ≠ 0) :
    x = ((eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨(), 1⟩) / eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨(), 0⟩) : ℂ) :
      OnePoint ℂ) := by
  obtain rfl | rfl := finset_fin_two_eq_cases i
  · rw [projectiveLineSource_zero] at hx
    obtain ⟨z, rfl⟩ := hx
    simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe]
  · obtain rfl | ⟨z, rfl⟩ := onePoint_eq_infty_or_exists_coe x
    · exact absurd (by simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_infty]) h0
    · have hz : z ≠ 0 := by
        intro hz
        rw [projectiveLineSource_one, Set.mem_setOf_eq] at hx
        exact hx (by rw [hz])
      simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hz]

/- English proof (translation)
Take `rfl | rfl` from `finset_fin_two_eq_cases i`. Rewrite using `[projectiveLineSource_zero]`. Conclude with `OnePoint.isOpen_range_coe`. Rewrite using `[projectiveLineSource_one] first`. Consider the case `exact isOpen_ne`.

Consider the case `exact isOpen_compl_singleton`.
-/
theorem projectiveLine_isOpen_source (i : Fin 2) : IsOpen (projectiveLineSource i) := by
  obtain rfl | rfl := finset_fin_two_eq_cases i
  · rw [projectiveLineSource_zero]
    exact OnePoint.isOpen_range_coe
  · rw [projectiveLineSource_one]
    first
    | exact isOpen_ne
    | exact isOpen_compl_singleton

/- English proof (translation)
Take `rfl | ⟨z, rfl⟩` from `onePoint_eq_infty_or_exists_coe x`. Conclude with `⟨1, infty_mem_projectiveLineSource_one⟩`. Conclude with `⟨0, coe_mem_projectiveLineSource_zero z⟩`.
-/
theorem projectiveLine_cover (x : OnePoint ℂ) : ∃ i, x ∈ projectiveLineSource i := by
  obtain rfl | ⟨z, rfl⟩ := onePoint_eq_infty_or_exists_coe x
  · exact ⟨1, infty_mem_projectiveLineSource_one⟩
  · exact ⟨0, coe_mem_projectiveLineSource_zero z⟩

/- English proof (translation)
Rewrite using `[OnePoint.hasBasis_nhds_infty.tendsto_left_iff]`. Introduce `U hU`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.mp hU`. Use `⟨Metric.closedBall 0 ε⁻¹, ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 _⟩, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Break down `hy with ⟨w, hw, rfl⟩ | hy` into its components or cases. Apply `hball` to reduce the goal to its premises. Rewrite `hw` using `[Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]`. Establish `hpos : 0 < ‖w‖` using `lt_trans (inv_pos.mpr hε) hw`. Simplify using `only [Metric.mem_ball, dist_zero_right, onePoint_elim_coe, norm_inv]`.

Use `first`. Consider the case `exact (inv_lt_comm₀ hε hpos).mp hw`. Consider the case `exact (inv_lt_comm₀ hpos hε).mpr hw`. Consider the case `exact (inv_lt hε hpos).mp hw`. Rewrite `hy` using `[Set.mem_singleton_iff]`.

Substitute `hy` using the available equality. Apply `hball` to reduce the goal to its premises. Simplify using `only [Metric.mem_ball, dist_zero_right, onePoint_elim_infty, norm_zero]`. Conclude with `hε`.
-/
private theorem tendsto_elim_inv_nhds_infty_nhds_zero :
    Filter.Tendsto (fun y : OnePoint ℂ => y.elim 0 (fun z => z⁻¹)) (nhds ∞) (nhds 0) := by
  rw [OnePoint.hasBasis_nhds_infty.tendsto_left_iff]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.closedBall 0 ε⁻¹, ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 _⟩, ?_⟩
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩ | hy
  · apply hball
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
    have hpos : 0 < ‖w‖ := lt_trans (inv_pos.mpr hε) hw
    simp only [Metric.mem_ball, dist_zero_right, onePoint_elim_coe, norm_inv]
    first
    | exact (inv_lt_comm₀ hε hpos).mp hw
    | exact (inv_lt_comm₀ hpos hε).mpr hw
    | exact (inv_lt hε hpos).mp hw
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, onePoint_elim_infty, norm_zero]
    exact hε

/- English proof (translation)
Rewrite using `[OnePoint.hasBasis_nhds_infty.tendsto_right_iff]`. Introduce and unpack `s ⟨-, hs⟩`. Take `⟨R, hR⟩` from `hs.isBounded.subset_closedBall 0`. Establish `hRpos : (0 : ℝ) < |R| + 1` using `by positivity`. Use `filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hRpos)] with u hu`.

Distinguish the cases in `hu0 : u = 0`. Rewrite using `[if_pos hu0]`. Conclude with `Set.mem_union_right _ rfl`. Rewrite using `[if_neg hu0]`. Use `Set.mem_union_left _ (Set.mem_image_of_mem _ (Set.mem_compl fun hmem => ?_))` and prove the remaining obligations.

Establish `h1` using `hR hmem`. Rewrite `h1` using `[Metric.mem_closedBall, dist_zero_right, norm_inv]`. Rewrite `hu` using `[Metric.mem_ball, dist_zero_right]`. Establish `hpos : 0 < ‖u‖` using `norm_pos_iff.mpr hu0`. Establish `h2 : |R| + 1 < ‖u‖⁻¹` using `by first`.

Consider the case `exact (lt_inv_comm₀ hRpos hpos).mpr hu`. Consider the case `exact (lt_inv_comm₀ hpos hRpos).mp hu`. Consider the case `exact (lt_inv hRpos hpos).mpr hu`. Combine the linear relations using `[le_abs_self R]`.
-/
private theorem tendsto_ite_zero_infty_inv_nhds_zero : Filter.Tendsto
    (fun w : ℂ => if w = 0 then (∞ : OnePoint ℂ) else ((w⁻¹ : ℂ) : OnePoint ℂ)) (nhds 0) (nhds ∞) := by
  rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
  rintro s ⟨-, hs⟩
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall 0
  have hRpos : (0 : ℝ) < |R| + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hRpos)] with u hu
  by_cases hu0 : u = 0
  · rw [if_pos hu0]
    exact Set.mem_union_right _ rfl
  · rw [if_neg hu0]
    refine Set.mem_union_left _ (Set.mem_image_of_mem _ (Set.mem_compl fun hmem => ?_))
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_inv] at h1
    rw [Metric.mem_ball, dist_zero_right] at hu
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have h2 : |R| + 1 < ‖u‖⁻¹ := by
      first
      | exact (lt_inv_comm₀ hRpos hpos).mpr hu
      | exact (lt_inv_comm₀ hpos hRpos).mp hu
      | exact (lt_inv hRpos hpos).mpr hu
    linarith [le_abs_self R]

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `w`. Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality. Unfold `ContinuousAt`.

Simplify using `using tendsto_ite_zero_infty_inv_nhds_zero`. Establish `h1 : ContinuousAt (fun v : ℂ => ((v⁻¹ : ℂ) : OnePoint ℂ)) w` using `OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)`. Apply `h1.congr` to reduce the goal to its premises. Use `filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hw)] with v hv`. Rewrite using `[if_neg (Set.mem_compl_singleton_iff.mp hv)]`.
-/
private theorem continuous_ite_zero_infty_inv_coe :
    Continuous (fun w : ℂ => if w = 0 then (∞ : OnePoint ℂ) else ((w⁻¹ : ℂ) : OnePoint ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    unfold ContinuousAt
    simpa using tendsto_ite_zero_infty_inv_nhds_zero
  · have h1 : ContinuousAt (fun v : ℂ => ((v⁻¹ : ℂ) : OnePoint ℂ)) w :=
      OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)
    apply h1.congr
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hw)] with v hv
    rw [if_neg (Set.mem_compl_singleton_iff.mp hv)]

/- English proof (translation)
Distinguish the cases in `hw : w = 0`. Rewrite using `[if_pos hw]`. Conclude with `infty_mem_projectiveLineSource_one`. Rewrite using `[if_neg hw]`. Conclude with `coe_mem_projectiveLineSource_one_of_ne_zero (inv_ne_zero hw)`.
-/
private theorem ite_zero_infty_inv_mem_projectiveLineSource (w : ℂ) :
    (if w = 0 then (∞ : OnePoint ℂ) else ((w⁻¹ : ℂ) : OnePoint ℂ)) ∈ projectiveLineSource 1 := by
  by_cases hw : w = 0
  · rw [if_pos hw]
    exact infty_mem_projectiveLineSource_one
  · rw [if_neg hw]
    exact coe_mem_projectiveLineSource_one_of_ne_zero (inv_ne_zero hw)

/- English proof (translation)
Take `rfl | rfl` from `finset_fin_two_eq_cases i`. Use `Function.LeftInverse.isEmbedding (f := fun v : Fin 1 → ℂ => (⟨((v 0 : ℂ) : OnePoint ℂ), coe_mem_projectiveLineSource_zero (v 0)⟩ : projectiveLineSource 0)) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite `hy` using `[projectiveLineSource_zero]`.

Take `⟨z, rfl⟩` from `hy`. Simplify using `[projLineAffineCoordinate, onePoint_elim_coe]`. Conclude with `(OnePoint.continuous_coe.comp (continuous_apply 0)).subtype_mk _`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `l`.

Establish `hc : Continuous (OnePoint.some ∘ fun y : projectiveLineSource 0 => projLineAffineCoordinate 0 (y : OnePoint ℂ) l)`. Establish `: (OnePoint.some ∘ fun y : projectiveLineSource 0 => projLineAffineCoordinate 0 (y : OnePoint ℂ) l) = Subtype.val`. Use function extensionality and compare the values at `y`. Take `⟨y, hy⟩` from `y`. Rewrite `hy` using `[projectiveLineSource_zero]`.

Take `⟨z, rfl⟩` from `hy`. Simplify using `[projLineAffineCoordinate, onePoint_elim_coe]`. Rewrite using `[this]`. Conclude with `continuous_subtype_val`. Use `first`.

Consider the case `exact (OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuous_iff).mpr hc`. Consider the case `exact (OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuous_iff).mpr hc`. Consider the case `exact (OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff).mpr hc`. Use `Function.LeftInverse.isEmbedding (f := fun v : Fin 1 → ℂ => (⟨if v 0 = 0 then (∞ : OnePoint ℂ) else (((v 0)⁻¹ : ℂ) : OnePoint ℂ), ite_zero_infty_inv_mem_projectiveLineSource (v 0)⟩ : projectiveLineSource 1)) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Take `rfl | ⟨w, rfl⟩` from `onePoint_eq_infty_or_exists_coe y`. Simplify using `[projLineAffineCoordinate, onePoint_elim_infty]`. Establish `hw : w ≠ 0` using `fun h => by`. Rewrite `hy` using `[projectiveLineSource_one, Set.mem_setOf_eq]`.

Conclude with `hy (by rw [h])`. Simplify using `[projLineAffineCoordinate, onePoint_elim_coe, hw]`. Conclude with `(continuous_ite_zero_infty_inv_coe.comp (continuous_apply 0)).subtype_mk _`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `l`.

Establish `: (fun y : projectiveLineSource 1 => projLineAffineCoordinate 1 (y : OnePoint ℂ) l) = (fun y : OnePoint ℂ => y.elim 0 (fun z => z⁻¹)) ∘ Subtype.val`. Use function extensionality and compare the values at `y`. Simplify using `[projLineAffineCoordinate]`. Rewrite using `[this, continuous_iff_continuousAt]`. Introduce and unpack `⟨y, hy⟩`.

Use `ContinuousAt.comp ?_ continuous_subtype_val.continuousAt` and prove the remaining obligations. Take `rfl | ⟨w, rfl⟩` from `onePoint_eq_infty_or_exists_coe y`. Conclude with `tendsto_elim_inv_nhds_infty_nhds_zero`. Establish `hw : w ≠ 0` using `fun h => by`. Rewrite `hy` using `[projectiveLineSource_one, Set.mem_setOf_eq]`.

Conclude with `hy (by rw [h])`. Conclude with `OnePoint.continuousAt_coe.mpr (continuousAt_inv₀ hw)`.
-/
theorem projectiveLine_isEmbedding (i : Fin 2) : Topology.IsEmbedding fun y : projectiveLineSource i => projLineAffineCoordinate i y := by
  obtain rfl | rfl := finset_fin_two_eq_cases i
  · refine Function.LeftInverse.isEmbedding
      (f := fun v : Fin 1 → ℂ => (⟨((v 0 : ℂ) : OnePoint ℂ), coe_mem_projectiveLineSource_zero (v 0)⟩ : projectiveLineSource 0)) ?_ ?_ ?_
    · rintro ⟨y, hy⟩
      apply Subtype.ext
      rw [projectiveLineSource_zero] at hy
      obtain ⟨z, rfl⟩ := hy
      simp [projLineAffineCoordinate, onePoint_elim_coe]
    · exact (OnePoint.continuous_coe.comp (continuous_apply 0)).subtype_mk _
    · apply continuous_pi
      intro l
      have hc : Continuous (OnePoint.some ∘ fun y : projectiveLineSource 0 => projLineAffineCoordinate 0 (y : OnePoint ℂ) l) := by
        have : (OnePoint.some ∘ fun y : projectiveLineSource 0 => projLineAffineCoordinate 0 (y : OnePoint ℂ) l) = Subtype.val := by
          funext y
          obtain ⟨y, hy⟩ := y
          rw [projectiveLineSource_zero] at hy
          obtain ⟨z, rfl⟩ := hy
          simp [projLineAffineCoordinate, onePoint_elim_coe]
        rw [this]
        exact continuous_subtype_val
      first
      | exact (OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuous_iff).mpr hc
      | exact (OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuous_iff).mpr hc
      | exact (OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff).mpr hc
  · refine Function.LeftInverse.isEmbedding
      (f := fun v : Fin 1 → ℂ => (⟨if v 0 = 0 then (∞ : OnePoint ℂ) else (((v 0)⁻¹ : ℂ) : OnePoint ℂ),
        ite_zero_infty_inv_mem_projectiveLineSource (v 0)⟩ : projectiveLineSource 1)) ?_ ?_ ?_
    · rintro ⟨y, hy⟩
      apply Subtype.ext
      obtain rfl | ⟨w, rfl⟩ := onePoint_eq_infty_or_exists_coe y
      · simp [projLineAffineCoordinate, onePoint_elim_infty]
      · have hw : w ≠ 0 := fun h => by
          rw [projectiveLineSource_one, Set.mem_setOf_eq] at hy
          exact hy (by rw [h])
        simp [projLineAffineCoordinate, onePoint_elim_coe, hw]
    · exact (continuous_ite_zero_infty_inv_coe.comp (continuous_apply 0)).subtype_mk _
    · apply continuous_pi
      intro l
      have : (fun y : projectiveLineSource 1 => projLineAffineCoordinate 1 (y : OnePoint ℂ) l) =
          (fun y : OnePoint ℂ => y.elim 0 (fun z => z⁻¹)) ∘ Subtype.val := by
        funext y
        simp [projLineAffineCoordinate]
      rw [this, continuous_iff_continuousAt]
      rintro ⟨y, hy⟩
      refine ContinuousAt.comp ?_ continuous_subtype_val.continuousAt
      obtain rfl | ⟨w, rfl⟩ := onePoint_eq_infty_or_exists_coe y
      · exact tendsto_elim_inv_nhds_infty_nhds_zero
      · have hw : w ≠ 0 := fun h => by
          rw [projectiveLineSource_one, Set.mem_setOf_eq] at hy
          exact hy (by rw [h])
        exact OnePoint.continuousAt_coe.mpr (continuousAt_inv₀ hw)

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `- h hh`. Rewrite `hh` using `[Ideal.mem_bot]`.

Rewrite using `[hh, map_zero]`. Introduce `_`. Take `rfl | rfl` from `finset_fin_two_eq_cases i`. Use `⟨(y 0 : OnePoint ℂ), coe_mem_projectiveLineSource_zero _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`.

Rewrite using `[Subsingleton.elim l 0]`. Simplify using `[projLineAffineCoordinate, onePoint_elim_coe]`. Distinguish the cases in `hy : y 0 = 0`. Use `⟨∞, infty_mem_projectiveLineSource_one, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`.

Rewrite using `[Subsingleton.elim l 0, hy]`. Simplify using `[projLineAffineCoordinate, onePoint_elim_infty]`. Use `⟨((y 0)⁻¹ : ℂ), coe_mem_projectiveLineSource_one_of_ne_zero (inv_ne_zero hy), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Rewrite using `[Subsingleton.elim l 0]`.

Simplify using `[projLineAffineCoordinate, onePoint_elim_coe]`.
-/
theorem projectiveLine_coord_image (i : Fin 2) :
    projLineAffineCoordinate i '' projectiveLineSource i = {y | ∀ h ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)), eval y h = 0} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro - h hh
    rw [Ideal.mem_bot] at hh
    rw [hh, map_zero]
  · intro _
    obtain rfl | rfl := finset_fin_two_eq_cases i
    · refine ⟨(y 0 : OnePoint ℂ), coe_mem_projectiveLineSource_zero _, ?_⟩
      funext l
      rw [Subsingleton.elim l 0]
      simp [projLineAffineCoordinate, onePoint_elim_coe]
    · by_cases hy : y 0 = 0
      · refine ⟨∞, infty_mem_projectiveLineSource_one, ?_⟩
        funext l
        rw [Subsingleton.elim l 0, hy]
        simp [projLineAffineCoordinate, onePoint_elim_infty]
      · refine ⟨((y 0)⁻¹ : ℂ), coe_mem_projectiveLineSource_one_of_ne_zero (inv_ne_zero hy), ?_⟩
        funext l
        rw [Subsingleton.elim l 0]
        simp [projLineAffineCoordinate, onePoint_elim_coe]

/- English proof (translation)
Apply the tactic sequence `obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain rfl | rfl := finset_fin_two_eq_cases j`. Conclude with `absurd rfl hij`. Conclude with `projectiveLine_mem_inter hy`. Conclude with `projectiveLine_mem_inter ⟨hy.2, hy.1⟩`. Conclude with `absurd rfl hij`.
-/
theorem projectiveLine_inter_ne_zero {i j : Fin 2} (hij : i ≠ j) {y : OnePoint ℂ} (hy : y ∈ projectiveLineSource i ∩ projectiveLineSource j) :
    ∃ z : ℂ, z ≠ 0 ∧ y = (z : OnePoint ℂ) := by
  obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain rfl | rfl := finset_fin_two_eq_cases j
  · exact absurd rfl hij
  · exact projectiveLine_mem_inter hy
  · exact projectiveLine_mem_inter ⟨hy.2, hy.1⟩
  · exact absurd rfl hij

/- English proof (translation)
Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `⟨1, fun l => X l, by simp, fun y _ _ l => by simp⟩`. Use `⟨X 0, fun _ => 1, ?_, ?_⟩` and prove the remaining obligations. Take `⟨z, hz, rfl⟩` from `projectiveLine_inter_ne_zero hij hx`.

Apply the tactic sequence `obtain rfl | rfl := finset_fin_two_eq_cases i <;> simp [projLineAffineCoordinate, onePoint_elim_coe, hz]`. Introduce `y hy _ l`. Take `⟨z, hz, rfl⟩` from `projectiveLine_inter_ne_zero hij hy`. Rewrite using `[Subsingleton.elim l 0]`. Apply the tactic sequence `obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain rfl | rfl := finset_fin_two_eq_cases j <;> first`.

Consider the case `exact absurd rfl hij`. Consider the case `simp [projLineAffineCoordinate, onePoint_elim_coe, hz]`.
-/
theorem projectiveLine_transition (i j : Fin 2) (x : OnePoint ℂ) (hx : x ∈ projectiveLineSource i ∩ projectiveLineSource j) :
    ∃ (q : MvPolynomial (Fin 1) ℂ) (F : Fin 1 → MvPolynomial (Fin 1) ℂ), eval (projLineAffineCoordinate i x) q ≠ 0 ∧
      ∀ y ∈ projectiveLineSource i ∩ projectiveLineSource j, eval (projLineAffineCoordinate i y) q ≠ 0 →
        ∀ l, projLineAffineCoordinate j y l * eval (projLineAffineCoordinate i y) q = eval (projLineAffineCoordinate i y) (F l) := by
  by_cases hij : i = j
  · subst hij
    exact ⟨1, fun l => X l, by simp, fun y _ _ l => by simp⟩
  · refine ⟨X 0, fun _ => 1, ?_, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := projectiveLine_inter_ne_zero hij hx
      obtain rfl | rfl := finset_fin_two_eq_cases i <;> simp [projLineAffineCoordinate, onePoint_elim_coe, hz]
    · intro y hy _ l
      obtain ⟨z, hz, rfl⟩ := projectiveLine_inter_ne_zero hij hy
      rw [Subsingleton.elim l 0]
      obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain rfl | rfl := finset_fin_two_eq_cases j <;>
        first
        | exact absurd rfl hij
        | simp [projLineAffineCoordinate, onePoint_elim_coe, hz]

/- English proof (translation)
Unfold `SameOrbit`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `⟨fun _ => 1, fun _ => one_ne_zero, by funext q; simp⟩`. Take `⟨w, hw, rfl⟩` from `projectiveLine_inter_ne_zero hij hx`.

Apply the tactic sequence `obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain rfl | rfl := finset_fin_two_eq_cases j`. Conclude with `absurd rfl hij`. Use `⟨fun _ => w, fun _ => hw, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Take `⟨⟨⟩, k⟩` from `q`.

Apply the tactic sequence `obtain rfl | rfl := finset_fin_two_eq_cases k <;> simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hw]`. Use `⟨fun _ => w⁻¹, fun _ => inv_ne_zero hw, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Take `⟨⟨⟩, k⟩` from `q`. Apply the tactic sequence `obtain rfl | rfl := finset_fin_two_eq_cases k <;> simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hw]`.

Conclude with `absurd rfl hij`.
-/
theorem projLine_isCompatibleChart (i j : Fin 2) (x : OnePoint ℂ) (hx : x ∈ projectiveLineSource i ∩ projectiveLineSource j) :
    SameOrbit (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q)) (fun q => eval (projLineAffineCoordinate j x) (homogeneousLift j q)) := by
  unfold SameOrbit
  by_cases hij : i = j
  · subst hij
    exact ⟨fun _ => 1, fun _ => one_ne_zero, by funext q; simp⟩
  · obtain ⟨w, hw, rfl⟩ := projectiveLine_inter_ne_zero hij hx
    obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain rfl | rfl := finset_fin_two_eq_cases j
    · exact absurd rfl hij
    · refine ⟨fun _ => w, fun _ => hw, ?_⟩
      funext q
      obtain ⟨⟨⟩, k⟩ := q
      obtain rfl | rfl := finset_fin_two_eq_cases k <;> simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hw]
    · refine ⟨fun _ => w⁻¹, fun _ => inv_ne_zero hw, ?_⟩
      funext q
      obtain ⟨⟨⟩, k⟩ := q
      obtain rfl | rfl := finset_fin_two_eq_cases k <;> simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hw]
    · exact absurd rfl hij

/- English proof (translation)
Establish `h1 : ∃ j, z ⟨(), j⟩ ≠ 0`. Simplify using `only [conePts, Set.mem_setOf_eq] at hz`. Conclude with `hz.1 ()`. Establish `h0 : z ⟨(), 0⟩ ≠ 0` using `fun h => hD ((projectiveLine_mem_conePts_span z).mpr ⟨h1, h⟩)`. Use `⟨0, ((z ⟨(), 1⟩ / z ⟨(), 0⟩ : ℂ) : OnePoint ℂ), coe_mem_projectiveLineSource_zero _, ?_⟩` and prove the remaining obligations.

Unfold `SameOrbit`. Use `⟨fun _ => (z ⟨(), 0⟩)⁻¹, fun _ => inv_ne_zero h0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Take `⟨⟨⟩, k⟩` from `q`. Take `rfl | rfl` from `finset_fin_two_eq_cases k`.

Simplify using `[homogeneousLift, h0]`. Apply the tactic sequence `simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe] <;> (try field_simp) <;> (try ring)`.
-/
theorem projection_surjective (z : (Σ _ : Unit, Fin 2) → ℂ)
    (hz : z ∈ conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)))
    (hD : z ∉ conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ))) :
    ∃ i, ∃ x ∈ projectiveLineSource i, SameOrbit (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q)) z := by
  have h1 : ∃ j, z ⟨(), j⟩ ≠ 0 := by
    simp only [conePts, Set.mem_setOf_eq] at hz
    exact hz.1 ()
  have h0 : z ⟨(), 0⟩ ≠ 0 := fun h => hD ((projectiveLine_mem_conePts_span z).mpr ⟨h1, h⟩)
  refine ⟨0, ((z ⟨(), 1⟩ / z ⟨(), 0⟩ : ℂ) : OnePoint ℂ), coe_mem_projectiveLineSource_zero _, ?_⟩
  unfold SameOrbit
  refine ⟨fun _ => (z ⟨(), 0⟩)⁻¹, fun _ => inv_ne_zero h0, ?_⟩
  funext q
  obtain ⟨⟨⟩, k⟩ := q
  obtain rfl | rfl := finset_fin_two_eq_cases k
  · simp [homogeneousLift, h0]
  · simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe] <;> (try field_simp) <;> (try ring)

/- English proof (translation)
Unfold `SameOrbit at ho`. Take `⟨c, hc, hcz⟩` from `ho`. Establish `hz0 : eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨(), 0⟩) ≠ 0`. Introduce `h`. Apply `hD` to reduce the goal to its premises.

Rewrite using `[projectiveLine_mem_conePts_span]`. Conclude with `⟨⟨i, by simp [homogeneousLift]⟩, h⟩`. Establish `e0` using `congrFun hcz ⟨(), 0⟩`. Establish `e1` using `congrFun hcz ⟨(), 1⟩`. Simplify using `only at e0 e1`.

Establish `hz0' : eval (projLineAffineCoordinate j x') (homogeneousLift j ⟨(), 0⟩) ≠ 0`. Introduce `h`. Rewrite `e0` using `[h, mul_zero]`. Conclude with `hz0 e0`. Rewrite using `[projectiveLine_point_eq_ratio i x hx hz0, projectiveLine_point_eq_ratio j x' hx' hz0', e0, e1, mul_div_mul_left _ _ (hc ())]`.
-/
theorem projectiveLine_injective_on_orbits (i j : Fin 2) (x : OnePoint ℂ) (hx : x ∈ projectiveLineSource i) (x' : OnePoint ℂ) (hx' : x' ∈ projectiveLineSource j)
    (hD : (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q)) ∉
      conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)))
    (ho : SameOrbit (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q))
      (fun q => eval (projLineAffineCoordinate j x') (homogeneousLift j q))) : x = x' := by
  unfold SameOrbit at ho
  obtain ⟨c, hc, hcz⟩ := ho
  have hz0 : eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨(), 0⟩) ≠ 0 := by
    intro h
    apply hD
    rw [projectiveLine_mem_conePts_span]
    exact ⟨⟨i, by simp [homogeneousLift]⟩, h⟩
  have e0 := congrFun hcz ⟨(), 0⟩
  have e1 := congrFun hcz ⟨(), 1⟩
  simp only at e0 e1
  have hz0' : eval (projLineAffineCoordinate j x') (homogeneousLift j ⟨(), 0⟩) ≠ 0 := by
    intro h
    rw [h, mul_zero] at e0
    exact hz0 e0
  rw [projectiveLine_point_eq_ratio i x hx hz0, projectiveLine_point_eq_ratio j x' hx' hz0', e0, e1, mul_div_mul_left _ _ (hc ())]

/- English proof (translation)
Establish `hpu : ∀ k, p k = p ()` using `fun k => by cases k; rfl`. Apply the tactic sequence `obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain hj | hj := finset_fin_two_eq_cases (p ())`. Use `⟨projectiveLineSource 0, projectiveLine_isOpen_source 0, hx, subset_rfl, 1, fun _ => X ⟨(), 1⟩, fun y _ => ⟨fun k => ?_, by simp, fun l => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hpu k, hj]`. Simplify using `[homogeneousLift]`.

Rewrite using `[Subsingleton.elim l 0]`. Simplify using `[affCoord, homogeneousLift, hj, projLineAffineCoordinate]`. Rewrite `hx` using `[projectiveLineSource_zero]`. Take `⟨w, rfl⟩` from `hx`. Establish `hw : w ≠ 0`.

Use `hp ()` as an intermediate fact. Rewrite `this` using `[hj]`. Simplify `this` using `[homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe]`. Use `⟨projectiveLineSource 0 ∩ projectiveLineSource 1, (projectiveLine_isOpen_source 0).inter (projectiveLine_isOpen_source 1), ⟨coe_mem_projectiveLineSource_zero w, coe_mem_projectiveLineSource_one_of_ne_zero hw⟩, Set.inter_subset_left, X ⟨(), 0⟩, fun _ => 1, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨v, hv, rfl⟩` from `projectiveLine_mem_inter hy`.

Use `⟨fun k => ?_, ?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[hpu k, hj]`. Simplify using `[homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv]`. Simplify using `[affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]`. Rewrite using `[Subsingleton.elim l 0]`.

Simplify using `[affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]`. Establish `hx0 : ∃ w : ℂ, w ≠ 0 ∧ x = (w : OnePoint ℂ)`. Use `hp ()` as an intermediate fact. Rewrite `this` using `[hj]`. Take `rfl | ⟨w, rfl⟩` from `onePoint_eq_infty_or_exists_coe x`.

Conclude with `absurd (by simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_infty]) this`. Conclude with `⟨w, fun h => this (by simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, h]), rfl⟩`. Take `⟨w, hw, rfl⟩` from `hx0`. Use `⟨projectiveLineSource 0 ∩ projectiveLineSource 1, (projectiveLine_isOpen_source 0).inter (projectiveLine_isOpen_source 1), ⟨coe_mem_projectiveLineSource_zero w, coe_mem_projectiveLineSource_one_of_ne_zero hw⟩, Set.inter_subset_right, X ⟨(), 1⟩, fun _ => 1, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨v, hv, rfl⟩` from `projectiveLine_mem_inter hy`.

Use `⟨fun k => ?_, ?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[hpu k, hj]`. Simplify using `[homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv]`. Simplify using `[affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]`. Rewrite using `[Subsingleton.elim l 0]`.

Simplify using `[affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]`. Use `⟨projectiveLineSource 1, projectiveLine_isOpen_source 1, hx, subset_rfl, 1, fun _ => X ⟨(), 0⟩, fun y _ => ⟨fun k => ?_, by simp, fun l => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hpu k, hj]`. Simplify using `[homogeneousLift]`. Rewrite using `[Subsingleton.elim l 0]`.

Simplify using `[affCoord, homogeneousLift, hj, projLineAffineCoordinate]`.
-/
theorem projectiveLine_local_inverse (i : Fin 2) (x : OnePoint ℂ) (hx : x ∈ projectiveLineSource i)
    (hD : (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q)) ∉
      conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)))
    (p : (k : Unit) → Fin 2) (hp : ∀ k, eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨k, p k⟩) ≠ 0) :
    ∃ O : Set (OnePoint ℂ), IsOpen O ∧ x ∈ O ∧ O ⊆ projectiveLineSource i ∧
      ∃ (q : MvPolynomial (Σ _ : Unit, Fin 2) ℂ) (F : Fin 1 → MvPolynomial (Σ _ : Unit, Fin 2) ℂ),
        ∀ y ∈ O, (∀ k, eval (projLineAffineCoordinate i y) (homogeneousLift i ⟨k, p k⟩) ≠ 0) ∧
          eval (affCoord p fun q => eval (projLineAffineCoordinate i y) (homogeneousLift i q)) q ≠ 0 ∧
          ∀ l, projLineAffineCoordinate i y l * eval (affCoord p fun q => eval (projLineAffineCoordinate i y) (homogeneousLift i q)) q =
            eval (affCoord p fun q => eval (projLineAffineCoordinate i y) (homogeneousLift i q)) (F l) := by
  have hpu : ∀ k, p k = p () := fun k => by cases k; rfl
  obtain rfl | rfl := finset_fin_two_eq_cases i <;> obtain hj | hj := finset_fin_two_eq_cases (p ())
  · refine ⟨projectiveLineSource 0, projectiveLine_isOpen_source 0, hx, subset_rfl, 1, fun _ => X ⟨(), 1⟩,
      fun y _ => ⟨fun k => ?_, by simp, fun l => ?_⟩⟩
    · rw [hpu k, hj]
      simp [homogeneousLift]
    · rw [Subsingleton.elim l 0]
      simp [affCoord, homogeneousLift, hj, projLineAffineCoordinate]
  · rw [projectiveLineSource_zero] at hx
    obtain ⟨w, rfl⟩ := hx
    have hw : w ≠ 0 := by
      have := hp ()
      rw [hj] at this
      simpa [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe] using this
    refine ⟨projectiveLineSource 0 ∩ projectiveLineSource 1, (projectiveLine_isOpen_source 0).inter (projectiveLine_isOpen_source 1),
      ⟨coe_mem_projectiveLineSource_zero w, coe_mem_projectiveLineSource_one_of_ne_zero hw⟩, Set.inter_subset_left, X ⟨(), 0⟩, fun _ => 1,
      fun y hy => ?_⟩
    obtain ⟨v, hv, rfl⟩ := projectiveLine_mem_inter hy
    refine ⟨fun k => ?_, ?_, fun l => ?_⟩
    · rw [hpu k, hj]
      simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv]
    · simp [affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]
    · rw [Subsingleton.elim l 0]
      simp [affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]
  · have hx0 : ∃ w : ℂ, w ≠ 0 ∧ x = (w : OnePoint ℂ) := by
      have := hp ()
      rw [hj] at this
      obtain rfl | ⟨w, rfl⟩ := onePoint_eq_infty_or_exists_coe x
      · exact absurd (by simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_infty]) this
      · exact ⟨w, fun h => this (by simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, h]), rfl⟩
    obtain ⟨w, hw, rfl⟩ := hx0
    refine ⟨projectiveLineSource 0 ∩ projectiveLineSource 1, (projectiveLine_isOpen_source 0).inter (projectiveLine_isOpen_source 1),
      ⟨coe_mem_projectiveLineSource_zero w, coe_mem_projectiveLineSource_one_of_ne_zero hw⟩, Set.inter_subset_right, X ⟨(), 1⟩, fun _ => 1,
      fun y hy => ?_⟩
    obtain ⟨v, hv, rfl⟩ := projectiveLine_mem_inter hy
    refine ⟨fun k => ?_, ?_, fun l => ?_⟩
    · rw [hpu k, hj]
      simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv]
    · simp [affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]
    · rw [Subsingleton.elim l 0]
      simp [affCoord, homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe, hv, hj]
  · refine ⟨projectiveLineSource 1, projectiveLine_isOpen_source 1, hx, subset_rfl, 1, fun _ => X ⟨(), 0⟩,
      fun y _ => ⟨fun k => ?_, by simp, fun l => ?_⟩⟩
    · rw [hpu k, hj]
      simp [homogeneousLift]
    · rw [Subsingleton.elim l 0]
      simp [affCoord, homogeneousLift, hj, projLineAffineCoordinate]

/- English proof (translation)
Rewrite using `[projectiveLine_mem_conePts_span]`. Establish `hex : ∃ j, eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨(), j⟩) ≠ 0` using `⟨i, by simp [homogeneousLift]⟩`. Take `rfl | rfl` from `finset_fin_two_eq_cases i`. Rewrite using `[projectiveLineBoundary_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `h 1 Submodule.mem_top` as an intermediate fact. Simplify using `at this`. Introduce and unpack `⟨-, h⟩`. Simplify using `[homogeneousLift] at h`.

Rewrite using `[projectiveLineBoundary_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨hex, ?_⟩` and prove the remaining obligations. Use `h (X 0) (Ideal.subset_span (Set.mem_singleton _))` as an intermediate fact.

Simplify `this` using `[homogeneousLift]`. Introduce and unpack `⟨-, h⟩ g hg`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hg`. Establish `h' : eval (projLineAffineCoordinate 1 x) (X 0) = 0` using `by simpa [homogeneousLift] using h`. Simplify using `[h']`.
-/
theorem projectiveLine_zero_boundary (i : Fin 2) (x : OnePoint ℂ) (hx : x ∈ projectiveLineSource i) :
    (∀ h ∈ p1Bd i, eval (projLineAffineCoordinate i x) h = 0) ↔ (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q)) ∈
      conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)) := by
  rw [projectiveLine_mem_conePts_span]
  have hex : ∃ j, eval (projLineAffineCoordinate i x) (homogeneousLift i ⟨(), j⟩) ≠ 0 := ⟨i, by simp [homogeneousLift]⟩
  obtain rfl | rfl := finset_fin_two_eq_cases i
  · rw [projectiveLineBoundary_zero]
    constructor
    · intro h
      have := h 1 Submodule.mem_top
      simp at this
    · rintro ⟨-, h⟩
      simp [homogeneousLift] at h
  · rw [projectiveLineBoundary_one]
    constructor
    · intro h
      refine ⟨hex, ?_⟩
      have := h (X 0) (Ideal.subset_span (Set.mem_singleton _))
      simpa [homogeneousLift] using this
    · rintro ⟨-, h⟩ g hg
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
      have h' : eval (projLineAffineCoordinate 1 x) (X 0) = 0 := by simpa [homogeneousLift] using h
      simp [h']

/- English proof (translation)
Take `rfl | rfl` from `finset_fin_two_eq_cases i`. Use `⟨projectiveLineSource 0, projectiveLine_isOpen_source 0, hx, subset_rfl, fun k => ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨rfl, hy⟩`. It suffices to derive a contradiction. Rewrite `hy` using `[projectiveLineSource_zero]`. Take `⟨z, hz⟩` from `hy`. Conclude with `OnePoint.coe_ne_infty z hz`.

Introduce and unpack `⟨-, l, hl, -⟩`. Simplify using `[projectiveLineSncData] at hl`. Distinguish the cases in `h0 : projLineAffineCoordinate 1 x 0 = 0`. Establish `hxinf : x = ∞` using `projectiveLine_coord_inf_eq_zero hx (by simpa [projLineAffineCoordinate] using h0)`. Substitute `hxinf` using the available equality.

Use `⟨projectiveLineSource 1, projectiveLine_isOpen_source 1, hx, subset_rfl, fun k => ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl, hy⟩`.

Use `⟨hy, 0, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[projectiveLineSncData, h0, Subsingleton.elim k 0]`. Simplify using `[projectiveLineSncData]`. Introduce and unpack `⟨hy, l, -, hl⟩`. Use `⟨?_, hy⟩` and prove the remaining obligations.

Apply `projectiveLine_coord_inf_eq_zero hy` to reduce the goal to its premises. Simplify `hl` using `[projectiveLineSncData, h0, projLineAffineCoordinate, onePoint_elim_infty]`. Establish `hx0 : x ∈ projectiveLineSource 0`. Take `rfl | ⟨w, rfl⟩` from `onePoint_eq_infty_or_exists_coe x`. Conclude with `absurd (by simp [projLineAffineCoordinate, onePoint_elim_infty]) h0`.

Conclude with `coe_mem_projectiveLineSource_zero w`. Use `⟨projectiveLineSource 0 ∩ projectiveLineSource 1, (projectiveLine_isOpen_source 0).inter (projectiveLine_isOpen_source 1), ⟨hx0, hx⟩, Set.inter_subset_right, fun k => ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨rfl, hy, -⟩`. It suffices to derive a contradiction. Rewrite `hy` using `[projectiveLineSource_zero]`. Take `⟨z, hz⟩` from `hy`. Conclude with `OnePoint.coe_ne_infty z hz`.

Introduce and unpack `⟨-, l, hl, -⟩`. Simplify using `[projectiveLineSncData, h0] at hl`.
-/
theorem projectiveLine_component_eq (i : Fin 2) (x : OnePoint ℂ) (hx : x ∈ projectiveLineSource i) :
    ∃ O : Set (OnePoint ℂ), IsOpen O ∧ x ∈ O ∧ O ⊆ projectiveLineSource i ∧ ∀ k : Fin 1,
      ({∞} : Set (OnePoint ℂ)) ∩ O = {y ∈ O | ∃ l, (projectiveLineSncData i (projLineAffineCoordinate i x)).σ l = Option.some k ∧
        eval (projLineAffineCoordinate i y) ((projectiveLineSncData i (projLineAffineCoordinate i x)).r l) = 0} := by
  obtain rfl | rfl := finset_fin_two_eq_cases i
  · refine ⟨projectiveLineSource 0, projectiveLine_isOpen_source 0, hx, subset_rfl, fun k => ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, hy⟩
      exfalso
      rw [projectiveLineSource_zero] at hy
      obtain ⟨z, hz⟩ := hy
      exact OnePoint.coe_ne_infty z hz
    · rintro ⟨-, l, hl, -⟩
      simp [projectiveLineSncData] at hl
  · by_cases h0 : projLineAffineCoordinate 1 x 0 = 0
    · have hxinf : x = ∞ := projectiveLine_coord_inf_eq_zero hx (by simpa [projLineAffineCoordinate] using h0)
      subst hxinf
      refine ⟨projectiveLineSource 1, projectiveLine_isOpen_source 1, hx, subset_rfl, fun k => ?_⟩
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨rfl, hy⟩
        refine ⟨hy, 0, ?_, ?_⟩
        · simp [projectiveLineSncData, h0, Subsingleton.elim k 0]
        · simp [projectiveLineSncData]
      · rintro ⟨hy, l, -, hl⟩
        refine ⟨?_, hy⟩
        apply projectiveLine_coord_inf_eq_zero hy
        simpa [projectiveLineSncData, h0, projLineAffineCoordinate, onePoint_elim_infty] using hl
    · have hx0 : x ∈ projectiveLineSource 0 := by
        obtain rfl | ⟨w, rfl⟩ := onePoint_eq_infty_or_exists_coe x
        · exact absurd (by simp [projLineAffineCoordinate, onePoint_elim_infty]) h0
        · exact coe_mem_projectiveLineSource_zero w
      refine ⟨projectiveLineSource 0 ∩ projectiveLineSource 1, (projectiveLine_isOpen_source 0).inter (projectiveLine_isOpen_source 1), ⟨hx0, hx⟩,
        Set.inter_subset_right, fun k => ?_⟩
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨rfl, hy, -⟩
        exfalso
        rw [projectiveLineSource_zero] at hy
        obtain ⟨z, hz⟩ := hy
        exact OnePoint.coe_ne_infty z hz
      · rintro ⟨-, l, hl, -⟩
        simp [projectiveLineSncData, h0] at hl

/- English proof (translation)
Use `first`. Consider the case `exact eval₂Hom_bind₁ _ _ _ _`. Consider the case `(rw [← coe_aeval_eq_eval, aeval_bind₁]; simp only [coe_aeval_eq_eval])`. Consider the case `simp only [← coe_aeval_eq_eval, aeval_bind₁]`. Consider the case `(induction f using MvPolynomial.induction_on <;> simp_all)`.
-/
private theorem eval_bind₁_homogeneousLift (y : Fin 1 → ℂ) (i : Fin 2) (f : MvPolynomial (Σ _ : Unit, Fin 2) ℂ) :
    eval y (bind₁ (homogeneousLift i) f) = eval (fun q => eval y (homogeneousLift i q)) f := by
  first
  | exact eval₂Hom_bind₁ _ _ _ _
  | (rw [← coe_aeval_eq_eval, aeval_bind₁]; simp only [coe_aeval_eq_eval])
  | simp only [← coe_aeval_eq_eval, aeval_bind₁]
  | (induction f using MvPolynomial.induction_on <;> simp_all)

/- English proof (translation)
Rewrite using `[eval_bind₁_homogeneousLift]`. Introduce `h`. Establish `hm : (fun q => eval y (homogeneousLift i q)) ∈ conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ))` using `projectiveLine_mem_conePts_bot _ ⟨i, by simp [homogeneousLift]⟩`. Conclude with `h0 ((projectiveLine_mem_conePts_span _).mp (hz _ hm h)).2`.
-/
private theorem eval_bind₁_homogeneousLift_ne_zero (f : MvPolynomial (Σ _ : Unit, Fin 2) ℂ)
    (hz : ∀ z ∈ conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)), eval z f = 0 →
      z ∈ conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)))
    (i : Fin 2) (y : Fin 1 → ℂ) (h0 : eval y (homogeneousLift i ⟨(), 0⟩) ≠ 0) :
    eval y (bind₁ (homogeneousLift i) f) ≠ 0 := by
  rw [eval_bind₁_homogeneousLift]
  intro h
  have hm : (fun q => eval y (homogeneousLift i q)) ∈ conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)) :=
    projectiveLine_mem_conePts_bot _ ⟨i, by simp [homogeneousLift]⟩
  exact h0 ((projectiveLine_mem_conePts_span _).mp (hz _ hm h)).2

/- English proof (translation)
Establish `hmem : g ∉ ptIdeal p`. Introduce `h`. Apply `hg` to reduce the goal to its premises. Simplify `h` using `[ptIdeal, RingHom.mem_ker]`. Establish `h1 : IsUnit (algebraMap (MvPolynomial (Fin 1) ℂ) (locPt p) g)` using `IsLocalization.map_units (locPt p) (⟨g, hmem⟩ : (ptIdeal p).primeCompl)`.

Use `first`. Consider the case `(rw [← Ideal.Quotient.mk_algebraMap]; exact h1.map _)`. Consider the case `(rw [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]; exact h1.map _)`. Consider the case `simpa using h1.map (Ideal.Quotient.mk _)`.
-/
private theorem isUnit_algebraMap_locRing_of_eval_ne_zero (p : Fin 1 → ℂ) (g : MvPolynomial (Fin 1) ℂ) (hg : eval p g ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (Fin 1) ℂ) (locRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) p) g) := by
  have hmem : g ∉ ptIdeal p := by
    intro h
    apply hg
    simpa [ptIdeal, RingHom.mem_ker] using h
  have h1 : IsUnit (algebraMap (MvPolynomial (Fin 1) ℂ) (locPt p) g) :=
    IsLocalization.map_units (locPt p) (⟨g, hmem⟩ : (ptIdeal p).primeCompl)
  first
  | (rw [← Ideal.Quotient.mk_algebraMap]; exact h1.map _)
  | (rw [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]; exact h1.map _)
  | simpa using h1.map (Ideal.Quotient.mk _)

/- English proof (translation)
Establish `hcomp : (Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ)).comp (MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ))) = AlgHom.id ℂ (MvPolynomial (Fin 1) ℂ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `l`. Rewrite using `[Subsingleton.elim l 0]`. Simplify using the standard rewrite rules.

Establish `hψφ : ∀ Q, Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ) (MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) Q) = Q` using `fun Q => by`. Simplify using `using DFunLike.congr_fun hcomp Q`. Establish `hφ : MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) P ≠ 0`. Introduce `h`. Apply `hP` to reduce the goal to its premises.

Rewrite using `[← hψφ P, h, map_zero]`. Use `set R := MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) P with hR`. Use `⟨Polynomial.rootMultiplicity 0 R, Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ) (R /ₘ (Polynomial.X - Polynomial.C 0) ^ Polynomial.rootMultiplicity 0 R), ?_, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← hψφ P, ← hR, ← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq R 0]`. Simplify using the standard rewrite rules.

Establish `key : ∀ Q : Polynomial ℂ, MvPolynomial.eval (fun _ : Fin 1 => (0 : ℂ)) (Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ) Q) = Q.eval 0`. Introduce `Q`. Use `Polynomial.induction_on Q ?_ ?_ ?_` and prove the remaining obligations. Introduce `a`. Simplify using the standard rewrite rules.

Introduce `p q hp hq`. Rewrite using `[map_add, map_add, hp, hq, Polynomial.eval_add]`. Introduce `n a _`. Simplify using the standard rewrite rules. Rewrite using `[key]`.

Use `first`. Consider the case `exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hφ`. Consider the case `exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero hφ`.
-/
private theorem exists_X_pow_mul_eval_zero_ne_zero (P : MvPolynomial (Fin 1) ℂ) (hP : P ≠ 0) :
    ∃ (n : ℕ) (g : MvPolynomial (Fin 1) ℂ), P = X 0 ^ n * g ∧ eval (fun _ => 0) g ≠ 0 := by
  have hcomp : (Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ)).comp
      (MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ))) =
        AlgHom.id ℂ (MvPolynomial (Fin 1) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro l
    rw [Subsingleton.elim l 0]
    simp
  have hψφ : ∀ Q, Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ)
      (MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) Q) = Q := fun Q => by
    simpa using DFunLike.congr_fun hcomp Q
  have hφ : MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) P ≠ 0 := by
    intro h
    apply hP
    rw [← hψφ P, h, map_zero]
  set R := MvPolynomial.aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) P with hR
  refine ⟨Polynomial.rootMultiplicity 0 R,
    Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ) (R /ₘ (Polynomial.X - Polynomial.C 0) ^ Polynomial.rootMultiplicity 0 R),
    ?_, ?_⟩
  · conv_lhs => rw [← hψφ P, ← hR, ← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq R 0]
    simp
  · have key : ∀ Q : Polynomial ℂ, MvPolynomial.eval (fun _ : Fin 1 => (0 : ℂ))
        (Polynomial.aeval (X 0 : MvPolynomial (Fin 1) ℂ) Q) = Q.eval 0 := by
      intro Q
      refine Polynomial.induction_on Q ?_ ?_ ?_
      · intro a
        simp
      · intro p q hp hq
        rw [map_add, map_add, hp, hq, Polynomial.eval_add]
      · intro n a _
        simp
    rw [key]
    first
    | exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hφ
    | exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero hφ

/- English proof (translation)
Establish `hP : bind₁ (homogeneousLift 1) f ≠ 0`. Introduce `h`. Use `eval_bind₁_homogeneousLift_ne_zero f hz 1 (fun _ => 1) (by simp [homogeneousLift])` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `this rfl`.

Take `⟨n, g, hPg, hg⟩` from `exists_X_pow_mul_eval_zero_ne_zero _ hP`. Use `⟨fun _ => n, fun i x _ => ?_⟩` and prove the remaining obligations. Take `rfl | rfl` from `finset_fin_two_eq_cases i`. Use `⟨_, isUnit_algebraMap_locRing_of_eval_ne_zero _ _ (eval_bind₁_homogeneousLift_ne_zero f hz 0 _ (by simp [homogeneousLift])), ?_⟩` and prove the remaining obligations. Simplify using `[projectiveLineSncData]`.

Distinguish the cases in `h0 : projLineAffineCoordinate 1 x 0 = 0`. Establish `hy : projLineAffineCoordinate 1 x = fun _ => 0`. Use function extensionality and compare the values at `l`. Rewrite using `[Subsingleton.elim l 0, h0]`. Use `⟨algebraMap _ _ g, isUnit_algebraMap_locRing_of_eval_ne_zero _ _ (by rw [hy]; exact hg), ?_⟩` and prove the remaining obligations.

Establish `hJ : (projectiveLineSncData 1 (projLineAffineCoordinate 1 x)).J = {0}` using `by simp [projectiveLineSncData, h0]`. Rewrite using `[hJ, Finset.prod_singleton]`. Simplify using `[projectiveLineSncData, h0, hPg, mul_comm]`. Use `⟨_, isUnit_algebraMap_locRing_of_eval_ne_zero _ _ (eval_bind₁_homogeneousLift_ne_zero f hz 1 _ (by simpa [homogeneousLift] using h0)), ?_⟩` and prove the remaining obligations. Simplify using `[projectiveLineSncData, h0]`.
-/
theorem projectiveLine_multiplicity (f : MvPolynomial (Σ _ : Unit, Fin 2) ℂ) (a : Unit → ℕ) (hf : IsMultiHomog f a)
    (hz : ∀ z ∈ conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)), eval z f = 0 →
      z ∈ conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ))) :
    ∃ m : Fin 1 → ℕ, ∀ i x (_hx : x ∈ projectiveLineSource i),
      ∃ u : locRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (projLineAffineCoordinate i x), IsUnit u ∧
        algebraMap (MvPolynomial (Fin 1) ℂ) (locRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (projLineAffineCoordinate i x))
          (bind₁ (homogeneousLift i) f) =
          u * ∏ l ∈ (projectiveLineSncData i (projLineAffineCoordinate i x)).J,
            algebraMap (MvPolynomial (Fin 1) ℂ) (locRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (projLineAffineCoordinate i x))
              ((projectiveLineSncData i (projLineAffineCoordinate i x)).r l) ^ ((projectiveLineSncData i (projLineAffineCoordinate i x)).σ l).elim 0 m := by
  have hP : bind₁ (homogeneousLift 1) f ≠ 0 := by
    intro h
    have := eval_bind₁_homogeneousLift_ne_zero f hz 1 (fun _ => 1) (by simp [homogeneousLift])
    rw [h, map_zero] at this
    exact this rfl
  obtain ⟨n, g, hPg, hg⟩ := exists_X_pow_mul_eval_zero_ne_zero _ hP
  refine ⟨fun _ => n, fun i x _ => ?_⟩
  obtain rfl | rfl := finset_fin_two_eq_cases i
  · refine ⟨_, isUnit_algebraMap_locRing_of_eval_ne_zero _ _ (eval_bind₁_homogeneousLift_ne_zero f hz 0 _ (by simp [homogeneousLift])), ?_⟩
    simp [projectiveLineSncData]
  · by_cases h0 : projLineAffineCoordinate 1 x 0 = 0
    · have hy : projLineAffineCoordinate 1 x = fun _ => 0 := by
        funext l
        rw [Subsingleton.elim l 0, h0]
      refine ⟨algebraMap _ _ g, isUnit_algebraMap_locRing_of_eval_ne_zero _ _ (by rw [hy]; exact hg), ?_⟩
      have hJ : (projectiveLineSncData 1 (projLineAffineCoordinate 1 x)).J = {0} := by simp [projectiveLineSncData, h0]
      rw [hJ, Finset.prod_singleton]
      simp [projectiveLineSncData, h0, hPg, mul_comm]
    · refine ⟨_, isUnit_algebraMap_locRing_of_eval_ne_zero _ _ (eval_bind₁_homogeneousLift_ne_zero f hz 1 _ (by simpa [homogeneousLift] using h0)), ?_⟩
      simp [projectiveLineSncData, h0]

def projectiveLineAlgRes : AlgRes (fun _ : Unit => Fin 2) ⊥ (Ideal.span {X ⟨(), 0⟩}) 1 where
  M := OnePoint ℂ
  n := 2
  amb := fun _ => 1
  ideal := fun _ => ⊥
  src := projectiveLineSource
  isOpen_alt_bis := projectiveLine_isOpen_source
  cover := projectiveLine_cover
  coord := projLineAffineCoordinate
  isEmbedding := projectiveLine_isEmbedding
  image := projectiveLine_coord_image
  trans := projectiveLine_transition
  regular := fun _ _ _ => locRing_bot_regularN _
  dim := fun _ _ _ => locRing_bot_dimN _
  lift := homogeneousLift
  lift_one := fun i => ⟨fun _ => i, fun _ => by simp [homogeneousLift]⟩
  lift_mem := fun i x _ => projectiveLine_lift_mem_conePts i x
  compat := projLine_isCompatibleChart
  surj := projection_surjective
  inj := projectiveLine_injective_on_orbits
  inv := projectiveLine_local_inverse
  bd := p1Bd
  le_bd := fun _ => bot_le
  zero_bd := projectiveLine_zero_boundary
  rc := 1
  comp := fun _ => {∞}
  sncAt := fun i x _ => projectiveLineSncData i (projLineAffineCoordinate i x)
  comp_eq := projectiveLine_component_eq
  mult := fun f a hf _ hz => projectiveLine_multiplicity f a hf hz

end

end ReciprocityTheory.AnForm.R
