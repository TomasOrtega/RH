import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOpenProjectionDominantComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermComponents

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.ComplexSets

variable {σ : Type} [Fintype σ]

/- English proof (translation)
Take `⟨N, k, f, hN, hwN, hf, hZN⟩` from `hZ`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hYZ` to reduce the goal to its premises. Establish `hall : ∀ i, ∀ᶠ z in 𝓝 w, z ∈ Y → f i z = 0`.

Introduce `i`. Apply `hcon (f i) (hf i w hwN)` to reduce the goal to its premises. Use `filter_upwards [hN.mem_nhds hwN] with z hzN hzZ`. Establish `hz : z ∈ Z ∩ N` using `⟨hzZ, hzN⟩`. Rewrite `hz` using `[hZN]`.

Conclude with `hz.2 i`. Establish `hall' : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y → f i z = 0` using `Filter.eventually_all.mpr hall`. Use `filter_upwards [hall', hN.mem_nhds hwN] with z hz hzN hzY`. Establish `hz' : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0}` using `⟨hzN, fun i => hz i hzY⟩`. Rewrite `hz'` using `[← hZN]`.

Conclude with `hz'.1`.
-/
theorem exists_equation_not_vanishing {Y Z : Set (σ → ℂ)} {w : σ → ℂ} (hZ : IsAnalyticNear Z w)
    (hYZ : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) :
    ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (∀ᶠ z in 𝓝 w, z ∈ Z → φ z = 0) ∧
      ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 := by
  obtain ⟨N, k, f, hN, hwN, hf, hZN⟩ := hZ
  by_contra hcon
  push_neg at hcon
  apply hYZ
  have hall : ∀ i, ∀ᶠ z in 𝓝 w, z ∈ Y → f i z = 0 := by
    intro i
    apply hcon (f i) (hf i w hwN)
    filter_upwards [hN.mem_nhds hwN] with z hzN hzZ
    have hz : z ∈ Z ∩ N := ⟨hzZ, hzN⟩
    rw [hZN] at hz
    exact hz.2 i
  have hall' : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y → f i z = 0 := Filter.eventually_all.mpr hall
  filter_upwards [hall', hN.mem_nhds hwN] with z hz hzN hzY
  have hz' : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
  rw [← hZN] at hz'
  exact hz'.1

/- English proof (translation)
Take `⟨hwY, hirr⟩` from `hY`. Use `revert hφ hne`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_ _ h`. Establish `h0` using `h.self_of_nhds hwY`.

Simplify using `at h0`. Introduce `a s has ih hφ hne h`. Rewrite `h` using `[Finset.prod_insert has]`. Break down `hirr (φ a) (fun z => ∏ j ∈ s, φ j z) (hφ a (Finset.mem_insert_self a s)) (by simpa only [Finset.prod_fn] using Finset.analyticAt_prod s fun j hj => hφ j (Finset.mem_insert_of_mem hj)) h with h1 | h1` into its components or cases. Conclude with `hne a (Finset.mem_insert_self a s) h1`.

Conclude with `ih (fun j hj => hφ j (Finset.mem_insert_of_mem hj)) (fun j hj => hne j (Finset.mem_insert_of_mem hj)) h1`.
-/
theorem not_eventually_prod_eq_zero {ι : Type} {Y : Set (σ → ℂ)} {w : σ → ℂ}
    (hY : GermIrreducibleAt Y w) (φ : ι → (σ → ℂ) → ℂ) (s : Finset ι)
    (hφ : ∀ j ∈ s, AnalyticAt ℂ (φ j) w)
    (hne : ∀ j ∈ s, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ j z = 0) :
    ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → ∏ j ∈ s, φ j z = 0 := by
  classical
  obtain ⟨hwY, hirr⟩ := hY
  revert hφ hne
  refine Finset.induction_on s ?_ ?_
  · intro _ _ h
    have h0 := h.self_of_nhds hwY
    simp at h0
  · intro a s has ih hφ hne h
    simp_rw [Finset.prod_insert has] at h
    rcases hirr (φ a) (fun z => ∏ j ∈ s, φ j z) (hφ a (Finset.mem_insert_self a s))
        (by simpa only [Finset.prod_fn] using
          Finset.analyticAt_prod s fun j hj => hφ j (Finset.mem_insert_of_mem hj)) h with h1 | h1
    · exact hne a (Finset.mem_insert_self a s) h1
    · exact ih (fun j hj => hφ j (Finset.mem_insert_of_mem hj))
        (fun j hj => hne j (Finset.mem_insert_of_mem hj)) h1

/- English proof (translation)
Use `haveI : Fintype ι := Fintype.ofFinite ι`. Set `P : Finset ι → Prop` to `fun T => ∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i`. Establish `hP : P Finset.univ` using `Filter.Eventually.of_forall fun z => by simp`. Take `⟨T, hT, hmin⟩` from `Finset.exists_min_image (Finset.univ.filter P) Finset.card ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩⟩`. Rewrite `hT` using `[Finset.mem_filter]`.

Use `⟨T, hT.2, ?_⟩` and prove the remaining obligations. Introduce `i hi j hj hij hsub`. Establish `hP' : P (T.erase i)` using `by filter_upwards [hT.2, hsub] with z hz hzs`. Rewrite using `[hz]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm, hzm⟩`. Distinguish the cases in `hmi : m = i`. Rewrite `hzm` using `[hmi]`. Conclude with `⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hzs hzm⟩`. Conclude with `⟨m, Finset.mem_erase.mpr ⟨hmi, hm⟩, hzm⟩`.

Introduce and unpack `⟨m, hm, hzm⟩`. Conclude with `⟨m, Finset.mem_of_mem_erase hm, hzm⟩`. Establish `hle` using `hmin (T.erase i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)`. Establish `hlt` using `Finset.card_erase_lt_of_mem hi`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_subfamily_no_containment {ι : Type} [Finite ι] (Y : ι → Set (σ → ℂ)) (w : σ → ℂ) :
    ∃ T : Finset ι, (∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i) ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  let P : Finset ι → Prop := fun T => ∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i
  have hP : P Finset.univ := Filter.Eventually.of_forall fun z => by simp
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P) Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩⟩
  rw [Finset.mem_filter] at hT
  refine ⟨T, hT.2, ?_⟩
  intro i hi j hj hij hsub
  have hP' : P (T.erase i) := by
    filter_upwards [hT.2, hsub] with z hz hzs
    rw [hz]
    constructor
    · rintro ⟨m, hm, hzm⟩
      by_cases hmi : m = i
      · rw [hmi] at hzm
        exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hzs hzm⟩
      · exact ⟨m, Finset.mem_erase.mpr ⟨hmi, hm⟩, hzm⟩
    · rintro ⟨m, hm, hzm⟩
      exact ⟨m, Finset.mem_of_mem_erase hm, hzm⟩
  have hle := hmin (T.erase i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)
  have hlt := Finset.card_erase_lt_of_mem hi
  omega

/- English proof (translation)
Establish `hsep : ∀ j, ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (j ≠ i → (∀ᶠ z in 𝓝 w, z ∈ Y j → φ z = 0) ∧ ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → φ z = 0)`. Introduce `j`. Distinguish the cases in `hj : j = i`. Conclude with `⟨fun _ => 1, analyticAt_const, fun h' => absurd hj h'⟩`. Take `⟨φ, h1, h2, h3⟩` from `exists_equation_not_vanishing (hYan j) (hno i j (Ne.symm hj))`.

Conclude with `⟨φ, h1, fun _ => ⟨h2, h3⟩⟩`. Use `choose φ hφan hφ using hsep`. Establish `hΦan : AnalyticAt ℂ (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) w` using `by simpa only [Finset.prod_fn] using Finset.analyticAt_prod (Finset.univ.erase i) fun j _ => hφan j`. Establish `hΦne : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → ∏ j ∈ Finset.univ.erase i, φ j z = 0` using `not_eventually_prod_eq_zero (hYirr i) φ _ (fun j _ => hφan j) (fun j hj => (hφ j (Finset.ne_of_mem_erase hj)).2)`. Establish `hΦY : ∀ᶠ z in 𝓝 w, ∀ j, j ≠ i → z ∈ Y j → ∏ j ∈ Finset.univ.erase i, φ j z = 0`.

Rewrite using `[Filter.eventually_all]`. Introduce `j`. Distinguish the cases in `hj : j = i`. Conclude with `Filter.Eventually.of_forall fun z h' => absurd hj h'`. Use `filter_upwards [(hφ j hj).1] with z hz _ hzj`.

Conclude with `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (hz hzj)`. Take `⟨ε, hε, hhb⟩` from `hh.exists_ball_analyticOnNhd`. Establish `hcont : ∀ᶠ z in 𝓝 w, ContinuousAt (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) z` using `hΦan.eventually_analyticAt.mono fun z hz => hz.continuousAt`. Establish `hAball : ∀ᶠ z in 𝓝 w, A z ∈ Metric.ball (A w) ε` using `A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)`. Establish `hgood` using `hcont.and (hΦY.and (hv.and (hAball.and (show ∀ᶠ z in 𝓝 w, z ∈ W from hW))))`.

Establish `hfreq` using `Filter.not_eventually.mp hΦne`. Take `⟨x, hx1, hx2⟩` from `(hfreq.and_eventually hgood.eventually_nhds).exists`. Use `push_neg at hx1`. Take `⟨hxY, hxΦ⟩` from `hx1`. Take `⟨hxc, -, -, hxA, hxW⟩` from `hx2.self_of_nhds`.

Establish `hxS : x ∈ S`. Establish `hx' : x ∈ (⋃ j, Y j) ∩ W` using `⟨Set.mem_iUnion.mpr ⟨i, hxY⟩, hxW⟩`. Rewrite `hx'` using `[← hS]`. Conclude with `hx'.1`. Establish `hV` using `hx2.and (hxc.eventually_ne hxΦ)`.

Establish `himg` using `hopen x hxS _ hV`. Establish `hzero : ∀ᶠ y in 𝓝 (A x), h y = 0` using `by filter_upwards [himg] with y hy`. Take `⟨z, ⟨hzS, ⟨⟨-, hzY, hzh, -, hzW⟩, hzΦ⟩⟩, rfl⟩` from `hy`. Establish `hz' : z ∈ (⋃ j, Y j) ∩ W` using `by rw [← hS]; exact ⟨hzS, hzW⟩`. Take `⟨j, hzj⟩` from `Set.mem_iUnion.mp hz'.1`.

Distinguish the cases in `hji : j = i`. Rewrite `hzj` using `[hji]`. Conclude with `hzh hzj`. Conclude with `absurd (hzY j hji hzj) hzΦ`. Establish `hEq` using `hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hxA hzero`.

Use `filter_upwards [Metric.ball_mem_nhds (A w) hε] with y hy`. Conclude with `hEq hy`.
-/
theorem dominant_of_open {ι : Type} [Fintype ι] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    {S W : Set (σ → ℂ)} {w : σ → ℂ} (Y : ι → Set (σ → ℂ))
    (hopen : ∀ x ∈ S, ∀ V ∈ 𝓝 x, A '' (S ∩ V) ∈ 𝓝 (A x))
    (hYan : ∀ i, IsAnalyticNear (Y i) w) (hYirr : ∀ i, GermIrreducibleAt (Y i) w)
    (hno : ∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j)
    (hW : W ∈ 𝓝 w) (hS : S ∩ W = (⋃ i, Y i) ∩ W) (i : ι)
    (h : (Fin d → ℂ) → ℂ) (hh : AnalyticAt ℂ h (A w))
    (hv : ∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) :
    ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  classical
  have hsep : ∀ j, ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (j ≠ i →
      (∀ᶠ z in 𝓝 w, z ∈ Y j → φ z = 0) ∧ ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → φ z = 0) := by
    intro j
    by_cases hj : j = i
    · exact ⟨fun _ => 1, analyticAt_const, fun h' => absurd hj h'⟩
    · obtain ⟨φ, h1, h2, h3⟩ := exists_equation_not_vanishing (hYan j) (hno i j (Ne.symm hj))
      exact ⟨φ, h1, fun _ => ⟨h2, h3⟩⟩
  choose φ hφan hφ using hsep
  have hΦan : AnalyticAt ℂ (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) w :=
    by simpa only [Finset.prod_fn] using Finset.analyticAt_prod (Finset.univ.erase i) fun j _ => hφan j
  have hΦne : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → ∏ j ∈ Finset.univ.erase i, φ j z = 0 :=
    not_eventually_prod_eq_zero (hYirr i) φ _ (fun j _ => hφan j)
      (fun j hj => (hφ j (Finset.ne_of_mem_erase hj)).2)
  have hΦY : ∀ᶠ z in 𝓝 w, ∀ j, j ≠ i → z ∈ Y j → ∏ j ∈ Finset.univ.erase i, φ j z = 0 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun z h' => absurd hj h'
    · filter_upwards [(hφ j hj).1] with z hz _ hzj
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (hz hzj)
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  have hcont : ∀ᶠ z in 𝓝 w, ContinuousAt (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) z :=
    hΦan.eventually_analyticAt.mono fun z hz => hz.continuousAt
  have hAball : ∀ᶠ z in 𝓝 w, A z ∈ Metric.ball (A w) ε :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  have hgood := hcont.and (hΦY.and (hv.and (hAball.and (show ∀ᶠ z in 𝓝 w, z ∈ W from hW))))
  have hfreq := Filter.not_eventually.mp hΦne
  obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually hgood.eventually_nhds).exists
  push_neg at hx1
  obtain ⟨hxY, hxΦ⟩ := hx1
  obtain ⟨hxc, -, -, hxA, hxW⟩ := hx2.self_of_nhds
  have hxS : x ∈ S := by
    have hx' : x ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.mpr ⟨i, hxY⟩, hxW⟩
    rw [← hS] at hx'
    exact hx'.1
  have hV := hx2.and (hxc.eventually_ne hxΦ)
  have himg := hopen x hxS _ hV
  have hzero : ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    filter_upwards [himg] with y hy
    obtain ⟨z, ⟨hzS, ⟨⟨-, hzY, hzh, -, hzW⟩, hzΦ⟩⟩, rfl⟩ := hy
    have hz' : z ∈ (⋃ j, Y j) ∩ W := by rw [← hS]; exact ⟨hzS, hzW⟩
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz'.1
    by_cases hji : j = i
    · rw [hji] at hzj
      exact hzh hzj
    · exact absurd (hzY j hji hzj) hzΦ
  have hEq := hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hxA hzero
  filter_upwards [Metric.ball_mem_nhds (A w) hε] with y hy
  exact hEq hy

/- English proof (translation)
Introduce `hAGC`. Unfold `AnalyticGermComponents.Statement at hAGC`. Unfold `OpenProjectionDominantComponents.Statement`. Introduce `σ _ X B k f d A hB hf hXB hopen w hw`. Establish `hAN : IsAnalyticNear (X ∩ B) w`.

Unfold `IsAnalyticNear`. Conclude with `⟨B, k, f, hB, hw.2, hf, by rw [Set.inter_assoc, Set.inter_self, hXB]⟩`. Take `⟨n₀, Y₀, hY₀, W, hW, hXW⟩` from `hAGC σ (X ∩ B) w hAN hw`. Take `⟨T, hT, hTno⟩` from `exists_subfamily_no_containment Y₀ w`. Set `e : Fin T.card ≃ T` to `T.equivFin.symm`.

Establish `hno : ∀ i j : Fin T.card, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y₀ (e i) → z ∈ Y₀ (e j)`. Introduce `i j hij`. Conclude with `hTno _ (e i).2 _ (e j).2 (fun h => hij (e.injective (Subtype.ext h)))`. Establish `hW' : W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i} ∈ 𝓝 w` using `Filter.inter_mem hW hT`. Establish `hS : X ∩ B ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) = (⋃ i, Y₀ (e i)) ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i})`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzXB, hzW, hzT⟩`. Establish `h1 : z ∈ (⋃ i, Y₀ i) ∩ W` using `by rw [← hXW]; exact ⟨hzXB, hzW⟩`. Take `⟨i, hiT, hzi⟩` from `hzT.mp h1.1`.

Use `⟨Set.mem_iUnion.mpr ⟨e.symm ⟨i, hiT⟩, ?_⟩, hzW, hzT⟩` and prove the remaining obligations. Simplify using `using hzi`. Introduce and unpack `⟨hzU, hzW, hzT⟩`. Take `⟨i, hzi⟩` from `Set.mem_iUnion.mp hzU`. Establish `h1 : z ∈ (⋃ i, Y₀ i) ∩ W` using `⟨Set.mem_iUnion.mpr ⟨_, hzi⟩, hzW⟩`.

Rewrite `h1` using `[← hXW]`. Conclude with `⟨h1.1, hzW, hzT⟩`. Use `⟨T.card, fun i => Y₀ (e i), fun i => ⟨(hY₀ _).1, (hY₀ _).2, fun h hh hv => ?_⟩, hno, _, hW', hS⟩` and prove the remaining obligations. Conclude with `dominant_of_open A (fun j => Y₀ (e j)) hopen (fun j => (hY₀ _).1) (fun j => (hY₀ _).2) hno hW' hS i h hh hv`.
-/
theorem openProjectionDominantComponents_of_analyticGermComponents :
    AnalyticGermComponents.Statement → OpenProjectionDominantComponents.Statement := by
  intro hAGC
  unfold AnalyticGermComponents.Statement at hAGC
  unfold OpenProjectionDominantComponents.Statement
  intro σ _ X B k f d A hB hf hXB hopen w hw
  have hAN : IsAnalyticNear (X ∩ B) w := by
    unfold IsAnalyticNear
    exact ⟨B, k, f, hB, hw.2, hf, by rw [Set.inter_assoc, Set.inter_self, hXB]⟩
  obtain ⟨n₀, Y₀, hY₀, W, hW, hXW⟩ := hAGC σ (X ∩ B) w hAN hw
  obtain ⟨T, hT, hTno⟩ := exists_subfamily_no_containment Y₀ w
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hno : ∀ i j : Fin T.card, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y₀ (e i) → z ∈ Y₀ (e j) := by
    intro i j hij
    exact hTno _ (e i).2 _ (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  have hW' : W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i} ∈ 𝓝 w := Filter.inter_mem hW hT
  have hS : X ∩ B ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) =
      (⋃ i, Y₀ (e i)) ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) := by
    ext z
    constructor
    · rintro ⟨hzXB, hzW, hzT⟩
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := by rw [← hXW]; exact ⟨hzXB, hzW⟩
      obtain ⟨i, hiT, hzi⟩ := hzT.mp h1.1
      refine ⟨Set.mem_iUnion.mpr ⟨e.symm ⟨i, hiT⟩, ?_⟩, hzW, hzT⟩
      simpa using hzi
    · rintro ⟨hzU, hzW, hzT⟩
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzU
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := ⟨Set.mem_iUnion.mpr ⟨_, hzi⟩, hzW⟩
      rw [← hXW] at h1
      exact ⟨h1.1, hzW, hzT⟩
  refine ⟨T.card, fun i => Y₀ (e i), fun i => ⟨(hY₀ _).1, (hY₀ _).2, fun h hh hv => ?_⟩, hno,
    _, hW', hS⟩
  exact dominant_of_open A (fun j => Y₀ (e j)) hopen (fun j => (hY₀ _).1) (fun j => (hY₀ _).2)
    hno hW' hS i h hh hv

end GlobalTheory.CompanionTheory.ComplexSets
