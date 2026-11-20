import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

namespace DiscriminantSheetCover

/- English proof (translation)
Use `set S := {y : Fin d → ℂ | eval y P = 0} with hSdef`. Establish `hS : MeasurableSet S` using `(isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet`. Establish `hnull : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc ((⊥ : Ideal (MvPolynomial (Fin d) ℂ)) ⊔ Ideal.span {P})) = 0` using `NullSmaller.proof d d _ (MassFinite.dim_sup_lt ⊥ Ideal.isPrime_bot (space_dim d) P (by simpa [Ideal.mem_bot] using hP))`. Take `⟨c, hc⟩` from `SheetAreaCompare.exists_lintegral_volume_eq d`. Establish `h` using `hc (S.indicator 1)`.

Rewrite `h` using `[lintegral_indicator_one hS]`. Rewrite using `[h]`. Establish `hae : (fun y : EuclideanSpace ℂ (Fin d) => S.indicator (1 : (Fin d → ℂ) → ENNReal) (WithLp.ofLp y)) =ᵐ[(μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d)))] 0`. Use `ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)` and prove the remaining obligations. Establish `hyS : WithLp.ofLp y ∈ S`.

Assume the negation of the conclusion as `h'`. Conclude with `hy (by simp [Set.indicator_of_notMem h'])`. Introduce `q hq`. Rewrite `hq` using `[bot_sup_eq]`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hq`.

Establish `: eval (WithLp.ofLp y) P = 0` using `hyS`. Simplify using `only [map_mul]`. Rewrite using `[show (fun i => y i) = WithLp.ofLp y from rfl, this, mul_zero]`. Rewrite using `[lintegral_congr_ae hae]`. Simplify using the standard rewrite rules.
-/
theorem volume_zero_set {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0) :
    volume {y : Fin d → ℂ | eval y P = 0} = 0 := by
  set S := {y : Fin d → ℂ | eval y P = 0} with hSdef
  have hS : MeasurableSet S :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  have hnull : μH[((2 * d : ℕ) : ℝ)]
      (zeroSetEuc ((⊥ : Ideal (MvPolynomial (Fin d) ℂ)) ⊔ Ideal.span {P})) = 0 :=
    NullSmaller.proof d d _ (MassFinite.dim_sup_lt ⊥ Ideal.isPrime_bot (space_dim d) P
      (by simpa [Ideal.mem_bot] using hP))
  obtain ⟨c, hc⟩ := SheetAreaCompare.exists_lintegral_volume_eq d
  have h := hc (S.indicator 1)
  rw [lintegral_indicator_one hS] at h
  rw [h]
  have hae : (fun y : EuclideanSpace ℂ (Fin d) => S.indicator (1 : (Fin d → ℂ) → ENNReal) (WithLp.ofLp y))
      =ᵐ[(μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d)))] 0 := by
    refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
    have hyS : WithLp.ofLp y ∈ S := by
      by_contra h'
      exact hy (by simp [Set.indicator_of_notMem h'])
    intro q hq
    rw [bot_sup_eq] at hq
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    have : eval (WithLp.ofLp y) P = 0 := hyS
    simp only [map_mul]
    rw [show (fun i => y i) = WithLp.ofLp y from rfl, this, mul_zero]
  rw [lintegral_congr_ae hae]
  simp

/- English proof (translation)
Take `⟨hfin, hcard, hloc⟩` from `hcov y₀ hy₀`. Establish `: Finite (fibre J A y₀)` using `hfin`. Set `e : fibre J A y₀ ≃ Fin N` to `Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard])`. Set `x : Fin N → Fin n → ℂ` to `fun j => (e.symm j).1`. Establish `hx : ∀ j, x j ∈ fibre J A y₀` using `fun j => (e.symm j).2`.

Establish `hxinj : Function.Injective x` using `fun i j h => e.symm.injective (Subtype.ext h)`. Use `choose U V g hU hyU hV hxV hg hgy hAg hZ using fun j => hloc (x j) (hx j)`. Establish `hcont : ∀ j, ContinuousAt (g j) y₀` using `fun j => (hg j).continuousOn.continuousAt ((hU j).mem_nhds (hyU j))`. Establish `hev : ∀ᶠ w in 𝓝 y₀, (∀ j, w ∈ U j) ∧ eval w P ≠ 0 ∧ ∀ i j, i ≠ j → g i w ≠ g j w`. Use `(eventually_all.2 fun j => (hU j).mem_nhds (hyU j)).and (((MvPolynomial.continuous_eval P).continuousAt.eventually_ne hy₀).and ?_)` and prove the remaining obligations.

Use `eventually_all.2 fun i => eventually_all.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Conclude with `Eventually.of_forall fun _ h => absurd hij h`. Establish `hne : g i y₀ - g j y₀ ≠ 0`. Rewrite using `[hgy, hgy]`.

Conclude with `sub_ne_zero.2 fun h => hij (hxinj h)`. Use `filter_upwards [((hcont i).sub (hcont j)).eventually_ne hne] with w hw _`. Conclude with `sub_ne_zero.1 hw`. Take `⟨W, hWsub, hWo, hyW⟩` from `mem_nhds_iff.1 hev`. Establish `hgZ : ∀ j, ∀ w ∈ U j, g j w ∈ zeroSet J ∩ V j` using `fun j w hw => (hZ j).symm ▸ ⟨w, hw, rfl⟩`.

Use `⟨W, hWo, hyW, fun w hw => (hWsub hw).2.1, g, fun j => (hg j).mono fun w hw => (hWsub hw).1 j, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨hwU, hwP, hwinj⟩` from `hWsub hw`. Establish `hinj : Function.Injective (fun j => g j w)` using `fun i j h => by_contra fun hij => hwinj i j hij h`. Establish `hsub : Set.range (fun j => g j w) ⊆ fibre J A w`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `⟨(hgZ j w (hwU j)).1, hAg j w (hwU j)⟩`. Take `⟨hfinw, hcardw, -⟩` from `hcov w hwP`. Use `⟨(Set.eq_of_subset_of_ncard_le hsub ?_ hfinw).symm, hinj, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hcardw, Set.ncard_range_of_injective hinj, Nat.card_fin]`. Use `⟨W, hWo, by rw [hAg j w (hwU j)]; exact hw, (hg j).mono fun v hv => (hWsub hv).1 j, by rw [hAg j w (hwU j)], fun v hv => ⟨hAg j v ((hWsub hv).1 j), (hgZ j v ((hWsub hv).1 j)).1⟩, V j, (hV j).mem_nhds (hgZ j w (hwU j)).2, fun x' hx' _ => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu, rfl⟩ : x' ∈ g j '' U j` from `hZ j ▸ hx'`. Rewrite using `[hAg j u hu]`.
-/
theorem local_sheets {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {P : MvPolynomial (Fin d) ℂ} {N : ℕ}
    (hcov : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (fibre J A y).Finite ∧ (fibre J A y).ncard = N ∧
        ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A.mulVec (g w) = w) ∧
            zeroSet J ∩ V = g '' U)
    (y₀ : Fin d → ℂ) (hy₀ : eval y₀ P ≠ 0) :
    ∃ W : Set (Fin d → ℂ), IsOpen W ∧ y₀ ∈ W ∧ W ⊆ {y | eval y P ≠ 0} ∧
      ∃ s : Fin N → (Fin d → ℂ) → Fin n → ℂ, (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ y ∈ W, fibre J A y = Set.range (fun j => s j y) ∧ Function.Injective (fun j => s j y) ∧
          ∀ j, IsSheetAt J A (s j y) (s j) := by
  obtain ⟨hfin, hcard, hloc⟩ := hcov y₀ hy₀
  have : Finite (fibre J A y₀) := hfin
  let e : fibre J A y₀ ≃ Fin N := Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard])
  let x : Fin N → Fin n → ℂ := fun j => (e.symm j).1
  have hx : ∀ j, x j ∈ fibre J A y₀ := fun j => (e.symm j).2
  have hxinj : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  choose U V g hU hyU hV hxV hg hgy hAg hZ using fun j => hloc (x j) (hx j)
  have hcont : ∀ j, ContinuousAt (g j) y₀ := fun j =>
    (hg j).continuousOn.continuousAt ((hU j).mem_nhds (hyU j))
  have hev : ∀ᶠ w in 𝓝 y₀, (∀ j, w ∈ U j) ∧ eval w P ≠ 0 ∧ ∀ i j, i ≠ j → g i w ≠ g j w := by
    refine (eventually_all.2 fun j => (hU j).mem_nhds (hyU j)).and
      (((MvPolynomial.continuous_eval P).continuousAt.eventually_ne hy₀).and ?_)
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · have hne : g i y₀ - g j y₀ ≠ 0 := by
        rw [hgy, hgy]; exact sub_ne_zero.2 fun h => hij (hxinj h)
      filter_upwards [((hcont i).sub (hcont j)).eventually_ne hne] with w hw _
      exact sub_ne_zero.1 hw
  obtain ⟨W, hWsub, hWo, hyW⟩ := mem_nhds_iff.1 hev
  have hgZ : ∀ j, ∀ w ∈ U j, g j w ∈ zeroSet J ∩ V j := fun j w hw => (hZ j).symm ▸ ⟨w, hw, rfl⟩
  refine ⟨W, hWo, hyW, fun w hw => (hWsub hw).2.1, g,
    fun j => (hg j).mono fun w hw => (hWsub hw).1 j, fun w hw => ?_⟩
  obtain ⟨hwU, hwP, hwinj⟩ := hWsub hw
  have hinj : Function.Injective (fun j => g j w) := fun i j h => by_contra fun hij => hwinj i j hij h
  have hsub : Set.range (fun j => g j w) ⊆ fibre J A w := by
    rintro _ ⟨j, rfl⟩
    exact ⟨(hgZ j w (hwU j)).1, hAg j w (hwU j)⟩
  obtain ⟨hfinw, hcardw, -⟩ := hcov w hwP
  refine ⟨(Set.eq_of_subset_of_ncard_le hsub ?_ hfinw).symm, hinj, fun j => ?_⟩
  · rw [hcardw, Set.ncard_range_of_injective hinj, Nat.card_fin]
  · refine ⟨W, hWo, by rw [hAg j w (hwU j)]; exact hw, (hg j).mono fun v hv => (hWsub hv).1 j,
      by rw [hAg j w (hwU j)], fun v hv => ⟨hAg j v ((hWsub hv).1 j), (hgZ j v ((hWsub hv).1 j)).1⟩,
      V j, (hV j).mem_nhds (hgZ j w (hwU j)).2, fun x' hx' _ => ?_⟩
    obtain ⟨u, hu, rfl⟩ : x' ∈ g j '' U j := hZ j ▸ hx'
    rw [hAg j u hu]

end DiscriminantSheetCover

/- English proof (translation)
Introduce `n d J A hJ hdim hA`. Take `⟨P, hP, hcov⟩` from `h₁ n d J A hJ hdim hA`. Establish `hall : ∀ y : Fin d → ℂ, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ (eval y P ≠ 0 → y ∈ W) ∧ W ⊆ {y | eval y P ≠ 0} ∧ ∃ s : Fin (projDegree J A) → (Fin d → ℂ) → Fin n → ℂ, (∀ j, DifferentiableOn ℂ (s j) W) ∧ ∀ w ∈ W, fibre J A w = Set.range (fun j => s j w) ∧ Function.Injective (fun j => s …`. Introduce `y`. Distinguish the cases in `hy : eval y P = 0`.

Conclude with `⟨∅, isOpen_empty, fun h => absurd hy h, Set.empty_subset _, fun _ _ => 0, fun _ => differentiableOn_empty, fun _ h => h.elim⟩`. Take `⟨W, hWo, hyW, hWP, s, hs, hsW⟩` from `DiscriminantSheetCover.local_sheets hcov y hy`. Conclude with `⟨W, hWo, fun _ => hyW, hWP, s, hs, hsW⟩`. Use `choose W hWo hyW hWP s hs hsW using hall`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable W hWo`.

Take `⟨e, he⟩` from `(hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)`. Establish `hcover : {y | eval y P ≠ 0} ⊆ ⋃ k, W (e k)`. Introduce `y hy`. Establish `: y ∈ ⋃ i ∈ T, W i` using `hTU ▸ Set.mem_iUnion.2 ⟨y, hyW y hy⟩`. Take `⟨i, hiT, hyi⟩` from `Set.mem_iUnion₂.1 this`.

Take `⟨k, rfl⟩ : i ∈ Set.range e` from `he ▸ Set.mem_insert_of_mem 0 hiT`. Conclude with `Set.mem_iUnion.2 ⟨k, hyi⟩`. Establish `hcompl : (⋃ k, disjointed (fun k => W (e k)) k)ᶜ ⊆ {y | eval y P = 0}`. Rewrite using `[iUnion_disjointed]`. Introduce `y hy`.

Assume the negation of the conclusion as `h`. Conclude with `hy (hcover h)`. Conclude with `⟨P, fun k => W (e k), disjointed (fun k => W (e k)), fun _ => projDegree J A, fun k => s (e k), hP, fun k => ⟨hWo _, MeasurableSet.disjointed (fun i => (hWo _).measurableSet) k, disjointed_le _ k, hs _⟩, disjoint_disjointed _, hcompl, measure_mono_null hcompl (DiscriminantSheetCo …`.
-/
theorem DiscriminantSheetCover.proof (h₁ : ComplexSets.DiscriminantCover.Statement) :
    DiscriminantSheetCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨P, hP, hcov⟩ := h₁ n d J A hJ hdim hA
  have hall : ∀ y : Fin d → ℂ, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ (eval y P ≠ 0 → y ∈ W) ∧
      W ⊆ {y | eval y P ≠ 0} ∧ ∃ s : Fin (projDegree J A) → (Fin d → ℂ) → Fin n → ℂ,
        (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ w ∈ W, fibre J A w = Set.range (fun j => s j w) ∧ Function.Injective (fun j => s j w) ∧
          ∀ j, IsSheetAt J A (s j w) (s j) := by
    intro y
    by_cases hy : eval y P = 0
    · exact ⟨∅, isOpen_empty, fun h => absurd hy h, Set.empty_subset _, fun _ _ => 0,
        fun _ => differentiableOn_empty, fun _ h => h.elim⟩
    · obtain ⟨W, hWo, hyW, hWP, s, hs, hsW⟩ := DiscriminantSheetCover.local_sheets hcov y hy
      exact ⟨W, hWo, fun _ => hyW, hWP, s, hs, hsW⟩
  choose W hWo hyW hWP s hs hsW using hall
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : {y | eval y P ≠ 0} ⊆ ⋃ k, W (e k) := by
    intro y hy
    have : y ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨y, hyW y hy⟩
    obtain ⟨i, hiT, hyi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact Set.mem_iUnion.2 ⟨k, hyi⟩
  have hcompl : (⋃ k, disjointed (fun k => W (e k)) k)ᶜ ⊆ {y | eval y P = 0} := by
    rw [iUnion_disjointed]
    intro y hy
    by_contra h
    exact hy (hcover h)
  exact ⟨P, fun k => W (e k), disjointed (fun k => W (e k)), fun _ => projDegree J A, fun k => s (e k), hP,
    fun k => ⟨hWo _, MeasurableSet.disjointed (fun i => (hWo _).measurableSet) k, disjointed_le _ k, hs _⟩,
    disjoint_disjointed _, hcompl, measure_mono_null hcompl (DiscriminantSheetCover.volume_zero_set P hP),
    fun k => hsW (e k)⟩

end

end GroundTheory.Heights₂.Heights
