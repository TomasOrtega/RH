import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

/- English proof (translation)
Establish `hm : MeasurableSet {u : (Fin n → ℂ) × ℝ | p + u.2 • u.1 ∉ Z}` using `(hZ.compl).preimage (f := fun u : (Fin n → ℂ) × ℝ => p + u.2 • u.1) (Continuous.measurable (by fun_prop))`. Establish `h1 : ∀ᵐ t : ℝ, ∀ᵐ x : Fin n → ℂ, p + t • x ∉ Z` using `(Measure.ae_ae_comm (p := fun (x : Fin n → ℂ) (t : ℝ) => p + t • x ∉ Z) hm).mp (Eventually.of_forall h)`. Establish `h2 : ∀ᵐ t : ℝ, t ≠ 0`. Simplify using `[ae_iff]`. Take `⟨t, ht, ht0⟩` from `(h1.and h2).exists`.

Establish `h3 : volume ((t • ·) ⁻¹' ((p + ·) ⁻¹' Z)) = 0`. Rewrite `ht` using `[ae_iff]`. Simplify `ht` using `[Set.preimage]`. Rewrite `h3` using `[Measure.addHaar_preimage_smul volume ht0, measure_preimage_add, mul_eq_zero]`. Use `h3.resolve_left ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.ofReal_eq_zero, not_le, abs_pos]`. Conclude with `inv_ne_zero (pow_ne_zero _ ht0)`.
-/
theorem null_of_lines {n : ℕ} (Z : Set (Fin n → ℂ)) (hZ : MeasurableSet Z) (p : Fin n → ℂ)
    (h : ∀ x : Fin n → ℂ, ∀ᵐ t : ℝ, p + t • x ∉ Z) : volume Z = 0 := by
  have hm : MeasurableSet {u : (Fin n → ℂ) × ℝ | p + u.2 • u.1 ∉ Z} :=
    (hZ.compl).preimage (f := fun u : (Fin n → ℂ) × ℝ => p + u.2 • u.1) (Continuous.measurable (by fun_prop))
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ x : Fin n → ℂ, p + t • x ∉ Z :=
    (Measure.ae_ae_comm (p := fun (x : Fin n → ℂ) (t : ℝ) => p + t • x ∉ Z) hm).mp (Eventually.of_forall h)
  have h2 : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff]
  obtain ⟨t, ht, ht0⟩ := (h1.and h2).exists
  have h3 : volume ((t • ·) ⁻¹' ((p + ·) ⁻¹' Z)) = 0 := by
    rw [ae_iff] at ht
    simpa [Set.preimage] using ht
  rw [Measure.addHaar_preimage_smul volume ht0, measure_preimage_add, mul_eq_zero] at h3
  refine h3.resolve_left ?_
  rw [ENNReal.ofReal_eq_zero, not_le, abs_pos]
  exact inv_ne_zero (pow_ne_zero _ ht0)

/- English proof (translation)
Establish `hm : MeasurableSet {x ∈ V | f x = 0}`. Establish `: {x ∈ V | f x = 0} = V \ (V ∩ f ⁻¹' {0}ᶜ)`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]`. The claim follows by propositional logic.

Rewrite using `[this]`. Conclude with `hV.measurableSet.diff (hf.continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton).measurableSet`. Use `null_of_lines _ hm p fun x => ?_` and prove the remaining obligations. Use `set S : Set ℝ := (fun t : ℝ => p + t • x) ⁻¹' V with hS`. Establish `hSo : IsOpen S` using `hV.preimage (by fun_prop)`.

Establish `hSc : Convex ℝ S`. Introduce `s hs t ht a b ha hb hab`. Use `hc hs ht ha hb hab` as an intermediate fact. Establish `e : a • (p + s • x) + b • (p + t • x) = p + (a • s + b • t) • x`. Establish `: p = a • p + b • p` using `by rw [← add_smul, hab, one_smul]`.

Use `conv_rhs => rw [this]`. Simplify using `only [smul_add, add_smul, smul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite `this` using `[e]`. Conclude with `this`.

Establish `hg : AnalyticOnNhd ℂ (fun s : ℂ => f (p + s • x)) ((fun s : ℂ => p + s • x) ⁻¹' V)`. Use `DifferentiableOn.analyticOnNhd ?_ (hV.preimage (by fun_prop))` and prove the remaining obligations. Conclude with `hf.comp (by fun_prop) fun s hs => hs`. Establish `hh : AnalyticOnNhd ℝ (fun t : ℝ => f (p + t • x)) S`. Introduce `t ht`.

Establish `h1 : AnalyticAt ℝ (fun s : ℂ => f (p + s • x)) (Complex.ofRealCLM t)` using `(hg t (by simpa [hS] using ht)).restrictScalars`. Use `h1.comp (Complex.ofRealCLM.analyticAt t)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Break down `hh.eqOn_zero_or_eventually_ne_zero_of_preconnected hSc.isPreconnected with h0 | h0` into its components or cases. Conclude with `(hfp (by simpa using h0 (x := 0) (by simpa [hS] using hp))).elim`.

Establish `h1 : ∀ᵐ t ∂(volume.restrict S), f (p + t • x) ≠ 0` using `ae_restrict_le_codiscreteWithin hSo.measurableSet h0`. Rewrite `h1` using `[ae_restrict_iff' hSo.measurableSet]`. Use `filter_upwards [h1] with t ht hz using ht hz.1 hz.2`.
-/
theorem zero_set_null {n : ℕ} (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hc : Convex ℝ V) (f : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f V) (p : Fin n → ℂ) (hp : p ∈ V) (hfp : f p ≠ 0) : volume {x ∈ V | f x = 0} = 0 := by
  have hm : MeasurableSet {x ∈ V | f x = 0} := by
    have : {x ∈ V | f x = 0} = V \ (V ∩ f ⁻¹' {0}ᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      tauto
    rw [this]
    exact hV.measurableSet.diff (hf.continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton).measurableSet
  refine null_of_lines _ hm p fun x => ?_
  set S : Set ℝ := (fun t : ℝ => p + t • x) ⁻¹' V with hS
  have hSo : IsOpen S := hV.preimage (by fun_prop)
  have hSc : Convex ℝ S := by
    intro s hs t ht a b ha hb hab
    have := hc hs ht ha hb hab
    have e : a • (p + s • x) + b • (p + t • x) = p + (a • s + b • t) • x := by
      have : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
      conv_rhs => rw [this]
      simp only [smul_add, add_smul, smul_assoc]
      abel
    rw [e] at this
    exact this
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => f (p + s • x)) ((fun s : ℂ => p + s • x) ⁻¹' V) := by
    refine DifferentiableOn.analyticOnNhd ?_ (hV.preimage (by fun_prop))
    exact hf.comp (by fun_prop) fun s hs => hs
  have hh : AnalyticOnNhd ℝ (fun t : ℝ => f (p + t • x)) S := by
    intro t ht
    have h1 : AnalyticAt ℝ (fun s : ℂ => f (p + s • x)) (Complex.ofRealCLM t) :=
      (hg t (by simpa [hS] using ht)).restrictScalars
    have := h1.comp (Complex.ofRealCLM.analyticAt t)
    simpa [Function.comp_def] using this
  rcases hh.eqOn_zero_or_eventually_ne_zero_of_preconnected hSc.isPreconnected with h0 | h0
  · exact (hfp (by simpa using h0 (x := 0) (by simpa [hS] using hp))).elim
  · have h1 : ∀ᵐ t ∂(volume.restrict S), f (p + t • x) ≠ 0 := ae_restrict_le_codiscreteWithin hSo.measurableSet h0
    rw [ae_restrict_iff' hSo.measurableSet] at h1
    filter_upwards [h1] with t ht hz using ht hz.1 hz.2

/- English proof (translation)
Use `⟨fun h => h (x := q) trivial, fun h q' _ => ?_⟩` and prove the remaining obligations. Establish `: q' = q` using `Subsingleton.elim (α := PrimeSpectrum ℂ) q' q`. Rewrite using `[this]`. Conclude with `h`.
-/
theorem top_le_iff_pt {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (q : Sp ℂ) : ⊤ ≤ x ⁻¹ᵁ U ↔ x q ∈ U := by
  refine ⟨fun h => h (x := q) trivial, fun h q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) q' q
  rw [this]
  exact h

/- English proof (translation)
Set `q : Sp ℂ` to `(default : PrimeSpectrum ℂ)`. Take `⟨W, hW, hbW, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (x := y b q) (U := ⊤) trivial`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp (hy W 0).1 b ⟨hb, (top_le_iff_pt _ _ q).mpr hbW⟩`. Use `⟨Metric.ball b ε, Metric.isOpen_ball, Metric.mem_ball_self hε, fun z hz => (hball hz).1, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨b', hb', hU⟩`.

Take `⟨f, hfU, hf⟩` from `hW.exists_basicOpen_le (V := U) ⟨y b' q, (top_le_iff_pt _ _ q).mp hU⟩ ((top_le_iff_pt _ _ q).mp (hball hb').2)`. Use `measure_mono_null ?_ (zero_set_null (Metric.ball b ε) Metric.isOpen_ball (convex_ball b ε) (fun z => valAt' (y z) W f) ((hy W f).2.mono hball) b' hb' ((valAt'_ne_zero_iff _ _ (hball hb').2 f q).mpr hf))` and prove the remaining obligations. Introduce and unpack `z ⟨hz, hzU⟩`. Use `⟨hz, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Conclude with `hzU ((top_le_iff_pt _ _ q).mpr (hfU ((valAt'_ne_zero_iff _ _ (hball hz).2 f q).mp hne)))`.
-/
theorem local_null {X : Scheme.{0}} {n : ℕ} {B : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (U : X.Opens)
    (hy : IsHolTo B y) {b : Fin n → ℂ} (hb : b ∈ B) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ b ∈ V ∧ V ⊆ B ∧
      ((∃ b' ∈ V, ⊤ ≤ y b' ⁻¹ᵁ U) → volume {b' ∈ V | ¬ ⊤ ≤ y b' ⁻¹ᵁ U} = 0) := by
  let q : Sp ℂ := (default : PrimeSpectrum ℂ)
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y b q) (U := ⊤) trivial
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hy W 0).1 b ⟨hb, (top_le_iff_pt _ _ q).mpr hbW⟩
  refine ⟨Metric.ball b ε, Metric.isOpen_ball, Metric.mem_ball_self hε, fun z hz => (hball hz).1, ?_⟩
  rintro ⟨b', hb', hU⟩
  obtain ⟨f, hfU, hf⟩ := hW.exists_basicOpen_le (V := U) ⟨y b' q, (top_le_iff_pt _ _ q).mp hU⟩
    ((top_le_iff_pt _ _ q).mp (hball hb').2)
  refine measure_mono_null ?_ (zero_set_null (Metric.ball b ε) Metric.isOpen_ball (convex_ball b ε)
    (fun z => valAt' (y z) W f) ((hy W f).2.mono hball) b' hb' ((valAt'_ne_zero_iff _ _ (hball hb').2 f q).mpr hf))
  rintro z ⟨hz, hzU⟩
  refine ⟨hz, ?_⟩
  by_contra hne
  exact hzU ((top_le_iff_pt _ _ q).mpr (hfU ((valAt'_ne_zero_iff _ _ (hball hz).2 f q).mp hne)))

/- English proof (translation)
Introduce `X n B y U _ hBc hy ⟨b₀, hb₀, hU₀⟩`. Use `choose! V hVo hVb hVB hV using fun b (hb : b ∈ B) => local_null U hy hb`. Use `set G : Set (Fin n → ℂ) := {b | ⊤ ≤ y b ⁻¹ᵁ U} with hG`. Establish `hsub : B ⊆ interior (closure G)`. Use `hBc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl (Set.disjoint_left.mpr fun z hz hz' => hz' (interior_subset hz)) (fun b hb => ?_) ?_ |>.trans le_rfl` and prove the remaining obligations.

Distinguish the cases in `hcl : b ∈ closure G`. Use `left`. Use `interior_maximal (t := V b) (fun z hz => ?_) (hVo b hb) (hVb b hb)` and prove the remaining obligations. Take `⟨b', hb'V, hb'G⟩` from `mem_closure_iff.mp hcl (V b) (hVo b hb) (hVb b hb)`. Establish `hnull` using `hV b hb ⟨b', hb'V, hb'G⟩`.

Assume the negation of the conclusion as `hz'`. Establish `ho : IsOpen (V b ∩ (closure G)ᶜ)` using `(hVo b hb).inter isClosed_closure.isOpen_compl`. Use `(ho.measure_pos volume ⟨z, hz, hz'⟩).ne' (measure_mono_null ?_ hnull)` and prove the remaining obligations. Conclude with `fun w hw => ⟨hw.1, fun h => hw.2 (subset_closure h)⟩`. Conclude with `Or.inr hcl`.

Use `⟨b₀, hb₀, interior_maximal (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}) (fun z hz => subset_closure hz.2) (hy U 0).1 ⟨hb₀, hU₀⟩⟩` and prove the remaining obligations. Use `measure_null_of_locally_null _ fun b hb => ?_` and prove the remaining obligations. Take `⟨b', hb'V, hb'G⟩` from `mem_closure_iff.mp (interior_subset (hsub hb.1)) (V b) (hVo b hb.1) (hVb b hb.1)`. Use `⟨{b' ∈ V b | ¬ ⊤ ≤ y b' ⁻¹ᵁ U}, ?_, hV b hb.1 ⟨b', hb'V, hb'G⟩⟩` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((hVo b hb.1).mem_nhds (hVb b hb.1))] with z hz hz' using ⟨hz', hz.2⟩`.
-/
theorem holNull : HolNull := by
  intro X n B y U _ hBc hy ⟨b₀, hb₀, hU₀⟩
  choose! V hVo hVb hVB hV using fun b (hb : b ∈ B) => local_null U hy hb
  set G : Set (Fin n → ℂ) := {b | ⊤ ≤ y b ⁻¹ᵁ U} with hG
  have hsub : B ⊆ interior (closure G) := by
    refine hBc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr fun z hz hz' => hz' (interior_subset hz)) (fun b hb => ?_) ?_ |>.trans le_rfl
    · by_cases hcl : b ∈ closure G
      · left
        refine interior_maximal (t := V b) (fun z hz => ?_) (hVo b hb) (hVb b hb)
        obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp hcl (V b) (hVo b hb) (hVb b hb)
        have hnull := hV b hb ⟨b', hb'V, hb'G⟩
        by_contra hz'
        have ho : IsOpen (V b ∩ (closure G)ᶜ) := (hVo b hb).inter isClosed_closure.isOpen_compl
        refine (ho.measure_pos volume ⟨z, hz, hz'⟩).ne' (measure_mono_null ?_ hnull)
        exact fun w hw => ⟨hw.1, fun h => hw.2 (subset_closure h)⟩
      · exact Or.inr hcl
    · refine ⟨b₀, hb₀, interior_maximal (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}) (fun z hz => subset_closure hz.2) (hy U 0).1 ⟨hb₀, hU₀⟩⟩
  refine measure_null_of_locally_null _ fun b hb => ?_
  obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp (interior_subset (hsub hb.1)) (V b) (hVo b hb.1) (hVb b hb.1)
  refine ⟨{b' ∈ V b | ¬ ⊤ ≤ y b' ⁻¹ᵁ U}, ?_, hV b hb.1 ⟨b', hb'V, hb'G⟩⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((hVo b hb.1).mem_nhds (hVb b hb.1))] with z hz hz'
    using ⟨hz', hz.2⟩

end SheetDecomposition
