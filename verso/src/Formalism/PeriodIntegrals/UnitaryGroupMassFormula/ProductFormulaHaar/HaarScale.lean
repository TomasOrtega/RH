import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarBox

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hopen : ∀ y : K, y ≠ 0 → IsOpen {x : K | valuation K x ≤ valuation K y}`. Introduce `y hy`. Establish `h` using `isOpen_box (Basis.singleton Unit K) (fun _ => valuation K y) (fun _ => (Valuation.ne_zero_iff _).mpr hy)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using `[box, Basis.singleton_repr]`. Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun y : {y : K // y ≠ 0} => {x : K | valuation K x ≤ valuation K y.1}) (fun y => hopen y.1 y.2) (by`. Introduce `x _`. Distinguish the cases in `hx : x = 0`. Use `Set.mem_iUnion.mpr ⟨⟨1, one_ne_zero⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[hx]`. Conclude with `Set.mem_iUnion.mpr ⟨⟨x, hx⟩, show valuation K x ≤ valuation K x from le_rfl⟩)`. Break down `t.eq_empty_or_nonempty with h0 | hne` into its components or cases. Use `⟨1, one_ne_zero, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `ht hx`.

Simplify using `[h0] at h1`. Take `⟨y, hy, hmax⟩` from `t.exists_max_image (fun y => valuation K y.1) hne`. Use `⟨y.1, y.2, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx'` using `ht hx`. Simplify using `only [Set.mem_iUnion] at hx'`.

Take `⟨y', hy', hxy'⟩` from `hx'`. Establish `hxy'' : valuation K x ≤ valuation K y'.1` using `hxy'`. Conclude with `le_trans hxy'' (hmax y' hy')`.
-/
theorem exists_ball_of_isCompact {C : Set K} (hC : IsCompact C) :
    ∃ y : K, y ≠ 0 ∧ C ⊆ {x | valuation K x ≤ valuation K y} := by
  classical
  have hopen : ∀ y : K, y ≠ 0 → IsOpen {x : K | valuation K x ≤ valuation K y} := by
    intro y hy
    have h := isOpen_box (Basis.singleton Unit K) (fun _ => valuation K y)
      (fun _ => (Valuation.ne_zero_iff _).mpr hy)
    convert h using 1
    ext x
    simp [box, Basis.singleton_repr]
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun y : {y : K // y ≠ 0} => {x : K | valuation K x ≤ valuation K y.1})
    (fun y => hopen y.1 y.2) (by
      intro x _
      by_cases hx : x = 0
      · refine Set.mem_iUnion.mpr ⟨⟨1, one_ne_zero⟩, ?_⟩
        simp [hx]
      · exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, show valuation K x ≤ valuation K x from le_rfl⟩)
  rcases t.eq_empty_or_nonempty with h0 | hne
  · refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    have h1 := ht hx
    simp [h0] at h1
  · obtain ⟨y, hy, hmax⟩ := t.exists_max_image (fun y => valuation K y.1) hne
    refine ⟨y.1, y.2, fun x hx => ?_⟩
    have hx' := ht hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨y', hy', hxy'⟩ := hx'
    have hxy'' : valuation K x ≤ valuation K y'.1 := hxy'
    exact le_trans hxy'' (hmax y' hy')

variable [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Use `letI : MeasurableSpace K := borel K`. Use `haveI : BorelSpace K := ⟨rfl⟩`. Use `haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E`. Use `haveI := locallyCompact b`. Use `haveI := secondCountableE b`.

Use `haveI := secondCountable K`. Take `⟨c, hc⟩ : ∃ c : E → K, c = fun x => b.repr x i` from `⟨_, rfl⟩`. Take `⟨P, hP⟩ : ∃ P : Set E, P = {x | ∀ j, j ≠ i → valuation K (b.repr x j) ≤ 1}` from `⟨_, rfl⟩`. Establish `hcc : Continuous c` using `by rw [hc]; exact continuous_coord b i`. Establish `hcm : Measurable c` using `hcc.measurable`.

Establish `hPo : IsOpen P`. Establish `h : P = ⋂ j ∈ (Finset.univ.filter (· ≠ i)), (fun x : E => b.repr x j) ⁻¹' {z : K | valuation K z ≤ 1}`. Rewrite using `[hP]`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Conclude with `isOpen_biInter_finset (fun j _ => (isOpen_ball 1 one_ne_zero).preimage (continuous_coord b j))`. Set `ν : Measure K` to `(μ.restrict P).map c`. Establish `hνA : ∀ A : Set K, MeasurableSet A → ν A = μ (P ∩ c ⁻¹' A)`. Introduce `A hA`.

Use `show ((μ.restrict P).map c) A = _`. Rewrite using `[Measure.map_apply hcm hA, Measure.restrict_apply (hcm hA), Set.inter_comm]`. Establish `hrepr_add : ∀ (t : K) (x : E) (j : ι), b.repr (t • b i + x) j = (if i = j then t else 0) + b.repr x j`. Introduce `t x j`. Rewrite using `[map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `haveI : ν.IsAddLeftInvariant := by`. Use `⟨fun t => ?_⟩` and prove the remaining obligations. Use extensionality with `A hA`. Rewrite using `[Measure.map_apply (measurable_const_add t) hA, hνA _ hA, hνA _ (measurable_const_add t hA)]`.

Establish `hset : P ∩ c ⁻¹' ((fun x => t + x) ⁻¹' A) = (fun x : E => t • b i + x) ⁻¹' (P ∩ c ⁻¹' A)`. Use extensionality with `x`. Rewrite using `[hP, hc]`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hrepr_add]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨fun j hj => by rw [if_neg (Ne.symm hj), zero_add]; exact h1 j hj, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun j hj => ?_, h2⟩` and prove the remaining obligations. Use `h1 j hj` as an intermediate fact.

Rewrite `this` using `[if_neg (Ne.symm hj), zero_add]`. Then use the resulting hypothesis. Rewrite using `[hset, measure_preimage_add]`. Use `haveI : IsFiniteMeasureOnCompacts ν := by`. Use `⟨fun C hC => ?_⟩` and prove the remaining obligations. Take `⟨y, hy0, hCy⟩` from `exists_ball_of_isCompact hC`.

Establish `hyv : valuation K y ≠ 0` using `(Valuation.ne_zero_iff _).2 hy0`. Establish `hB : IsOpen {x : K | valuation K x ≤ valuation K y}` using `isOpen_ball _ hyv`. Combine the equalities or inequalities in the displayed calculation. Apply `measure_mono` to reduce the goal to its premises. Introduce and unpack `x ⟨hx1, hx2⟩ j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Function.update_self]`. Rewrite `hx2` using `[Set.mem_preimage, hc]`. Conclude with `hx2`.

Rewrite using `[Function.update_of_ne hj]`. Rewrite `hx1` using `[hP]`. Conclude with `hx1 j hj`. Use `_ < ⊤ := (isCompact_box b _).measure_lt_top`. Use `haveI : IsOpenPosMeasure ν := by`.

Use `⟨fun U hU hne => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hne`. Rewrite using `[hνA U hU.measurableSet]`. Establish `hO : IsOpen (P ∩ c ⁻¹' U)` using `hPo.inter (hU.preimage hcc)`. Use `hO.measure_ne_zero μ ⟨u • b i, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hP]`. Introduce `j hj`. Rewrite using `[map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hj), smul_zero, map_zero]`. Conclude with `zero_le'`. Rewrite using `[Set.mem_preimage, hc]`.

Simplify using `using hu`. Use `haveI : ν.IsAddHaarMeasure := { }`. Set `g : Kˣ` to `Units.mk0 a ha`. Establish `hOo : IsOpen {x : K | valuation K x ≤ 1}` using `isOpen_ball 1 one_ne_zero`. Establish `hgO : IsOpen (g • {x : K | valuation K x ≤ 1})` using `hOo.smul g`.

Establish `hscale : ν (g • {x : K | valuation K x ≤ 1}) = (distribHaarChar K g : ℝ≥0∞) * ν {x | valuation K x ≤ 1}`. Establish `h1 : (DomMulAct.mk g • ν) {x : K | valuation K x ≤ 1} = ν (g • {x : K | valuation K x ≤ 1})`. Simplify using `[domSMul_apply]`. Rewrite using `[← h1, measure_isAddHaarMeasure_eq_smul_of_isOpen _ ν hOo, addHaarScalarFactor_smul_eq_distribHaarChar, ENNReal.smul_def, smul_eq_mul]`. Establish `hrepr : ∀ (d : ι → K) (x : E) (j : ι), b.repr (Matrix.toLin b b (Matrix.diagonal d) x) j = d j * b.repr x j`.

Introduce `d x j`. Rewrite using `[Matrix.repr_toLin, Matrix.mulVec_diagonal]`. Establish `hR : box b 1 = P ∩ c ⁻¹' {x : K | valuation K x ≤ 1}`. Use extensionality with `x`. Rewrite using `[hP, hc]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun j _ => h j, h i⟩`. Introduce and unpack `⟨h1, h2⟩ j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Conclude with `h2`. Conclude with `h1 j hj`. Establish `hL : (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a))) '' box b 1 = P ∩ c ⁻¹' (g • {x : K | valuation K x ≤ 1})`. Use extensionality with `y`.

Rewrite using `[hP, hc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨fun j hj => ?_, ?_⟩` and prove the remaining obligations. Use `show valuation K (b.repr _ j) ≤ 1`.

Rewrite using `[hrepr, Function.update_of_ne hj, Pi.one_apply, one_mul]`. Conclude with `hx j`. Use `show b.repr _ i ∈ g • {x : K | valuation K x ≤ 1}`. Rewrite using `[hrepr, Function.update_self]`. Conclude with `Set.mem_smul_set.2 ⟨b.repr x i, hx i, rfl⟩`.

Introduce and unpack `⟨h1, h2⟩`. Take `⟨z, hz, hzy⟩` from `Set.mem_smul_set.1 h2`. Establish `hzy' : a * z = b.repr y i` using `hzy`. Set `T'` to `Matrix.toLin b b (Matrix.diagonal (Function.update (1 : ι → K) i a⁻¹))`. Use `⟨T' y, fun j => ?_, ?_⟩` and prove the remaining obligations.

Use `show valuation K (b.repr (T' y) j) ≤ 1`. Rewrite using `[hrepr]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Function.update_self, ← hzy', ← mul_assoc, inv_mul_cancel₀ ha, one_mul]`.

Conclude with `hz`. Rewrite using `[Function.update_of_ne hj, Pi.one_apply, one_mul]`. Conclude with `h1 j hj`. Use `show Matrix.toLin b b _ (Matrix.toLin b b _ y) = y`. Rewrite using `[← LinearMap.comp_apply, ← Matrix.toLin_mul, Matrix.diagonal_mul_diagonal]`.

Establish `hdd : (fun k => Function.update (1 : ι → K) i a k * Function.update (1 : ι → K) i a⁻¹ k) = (1 : ι → K)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[ha]`.

Simplify using `[Function.update_of_ne hk]`. Rewrite using `[hdd, Pi.one_def, Matrix.diagonal_one, Matrix.toLin_one, LinearMap.id_apply]`. Rewrite using `[hL, hR, ← hνA _ hgO.measurableSet, ← hνA _ hOo.measurableSet, hscale]`.
-/
theorem scale_box (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (i : ι) (a : K)
    (ha : a ≠ 0) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1) := by
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  haveI := secondCountable K
  obtain ⟨c, hc⟩ : ∃ c : E → K, c = fun x => b.repr x i := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Set E, P = {x | ∀ j, j ≠ i → valuation K (b.repr x j) ≤ 1} :=
    ⟨_, rfl⟩
  have hcc : Continuous c := by rw [hc]; exact continuous_coord b i
  have hcm : Measurable c := hcc.measurable
  have hPo : IsOpen P := by
    have h : P = ⋂ j ∈ (Finset.univ.filter (· ≠ i)),
        (fun x : E => b.repr x j) ⁻¹' {z : K | valuation K z ≤ 1} := by
      rw [hP]; ext x; simp
    rw [h]
    exact isOpen_biInter_finset
      (fun j _ => (isOpen_ball 1 one_ne_zero).preimage (continuous_coord b j))
  let ν : Measure K := (μ.restrict P).map c
  have hνA : ∀ A : Set K, MeasurableSet A → ν A = μ (P ∩ c ⁻¹' A) := by
    intro A hA
    show ((μ.restrict P).map c) A = _
    rw [Measure.map_apply hcm hA, Measure.restrict_apply (hcm hA), Set.inter_comm]
  have hrepr_add : ∀ (t : K) (x : E) (j : ι),
      b.repr (t • b i + x) j = (if i = j then t else 0) + b.repr x j := by
    intro t x j
    rw [map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun t => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add t) hA, hνA _ hA,
      hνA _ (measurable_const_add t hA)]
    have hset : P ∩ c ⁻¹' ((fun x => t + x) ⁻¹' A) =
        (fun x : E => t • b i + x) ⁻¹' (P ∩ c ⁻¹' A) := by
      ext x
      rw [hP, hc]
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hrepr_add]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun j hj => by rw [if_neg (Ne.symm hj), zero_add]; exact h1 j hj, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun j hj => ?_, h2⟩
        have := h1 j hj
        rwa [if_neg (Ne.symm hj), zero_add] at this
    rw [hset, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨y, hy0, hCy⟩ := exists_ball_of_isCompact hC
    have hyv : valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
    have hB : IsOpen {x : K | valuation K x ≤ valuation K y} := isOpen_ball _ hyv
    calc ν C ≤ ν {x | valuation K x ≤ valuation K y} := measure_mono hCy
      _ = μ (P ∩ c ⁻¹' {x | valuation K x ≤ valuation K y}) := hνA _ hB.measurableSet
      _ ≤ μ (box b (Function.update 1 i (valuation K y))) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩ j
          by_cases hj : j = i
          · subst hj
            rw [Function.update_self]
            rw [Set.mem_preimage, hc] at hx2
            exact hx2
          · rw [Function.update_of_ne hj]
            rw [hP] at hx1
            exact hx1 j hj
      _ < ⊤ := (isCompact_box b _).measure_lt_top
  haveI : IsOpenPosMeasure ν := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨u, hu⟩ := hne
    rw [hνA U hU.measurableSet]
    have hO : IsOpen (P ∩ c ⁻¹' U) := hPo.inter (hU.preimage hcc)
    refine hO.measure_ne_zero μ ⟨u • b i, ?_, ?_⟩
    · rw [hP]
      intro j hj
      rw [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (Ne.symm hj), smul_zero, map_zero]
      exact zero_le'
    · rw [Set.mem_preimage, hc]
      simpa using hu
  haveI : ν.IsAddHaarMeasure := { }
  let g : Kˣ := Units.mk0 a ha
  have hOo : IsOpen {x : K | valuation K x ≤ 1} := isOpen_ball 1 one_ne_zero
  have hgO : IsOpen (g • {x : K | valuation K x ≤ 1}) := hOo.smul g
  have hscale : ν (g • {x : K | valuation K x ≤ 1}) =
      (distribHaarChar K g : ℝ≥0∞) * ν {x | valuation K x ≤ 1} := by
    have h1 : (DomMulAct.mk g • ν) {x : K | valuation K x ≤ 1} =
        ν (g • {x : K | valuation K x ≤ 1}) := by
      simp [domSMul_apply]
    rw [← h1, measure_isAddHaarMeasure_eq_smul_of_isOpen _ ν hOo,
      addHaarScalarFactor_smul_eq_distribHaarChar, ENNReal.smul_def, smul_eq_mul]
  have hrepr : ∀ (d : ι → K) (x : E) (j : ι),
      b.repr (Matrix.toLin b b (Matrix.diagonal d) x) j = d j * b.repr x j := by
    intro d x j
    rw [Matrix.repr_toLin, Matrix.mulVec_diagonal]
  have hR : box b 1 = P ∩ c ⁻¹' {x : K | valuation K x ≤ 1} := by
    ext x
    rw [hP, hc]
    constructor
    · intro h
      exact ⟨fun j _ => h j, h i⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h2
      · exact h1 j hj
  have hL : (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a))) '' box b 1 =
      P ∩ c ⁻¹' (g • {x : K | valuation K x ≤ 1}) := by
    ext y
    rw [hP, hc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun j hj => ?_, ?_⟩
      · show valuation K (b.repr _ j) ≤ 1
        rw [hrepr, Function.update_of_ne hj, Pi.one_apply, one_mul]
        exact hx j
      · show b.repr _ i ∈ g • {x : K | valuation K x ≤ 1}
        rw [hrepr, Function.update_self]
        exact Set.mem_smul_set.2 ⟨b.repr x i, hx i, rfl⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.1 h2
      have hzy' : a * z = b.repr y i := hzy
      let T' := Matrix.toLin b b (Matrix.diagonal (Function.update (1 : ι → K) i a⁻¹))
      refine ⟨T' y, fun j => ?_, ?_⟩
      · show valuation K (b.repr (T' y) j) ≤ 1
        rw [hrepr]
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, ← hzy', ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
          exact hz
        · rw [Function.update_of_ne hj, Pi.one_apply, one_mul]
          exact h1 j hj
      · show Matrix.toLin b b _ (Matrix.toLin b b _ y) = y
        rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, Matrix.diagonal_mul_diagonal]
        have hdd : (fun k => Function.update (1 : ι → K) i a k * Function.update (1 : ι → K) i a⁻¹ k) =
            (1 : ι → K) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [ha]
          · simp [Function.update_of_ne hk]
        rw [hdd, Pi.one_def, Matrix.diagonal_one, Matrix.toLin_one, LinearMap.id_apply]
  rw [hL, hR, ← hνA _ hgO.measurableSet, ← hνA _ hOo.measurableSet, hscale]

end PI.ProdFormulaE.HaarBox
