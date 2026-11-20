import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreLocalUnbranched
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOpenProjectionDominantComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermMeetOverHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Take `⟨r, hr, hball⟩` from `Metric.mem_nhds_iff.1 ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)`. Distinguish the cases in `hf0 : ∀ z ∈ Metric.ball y r, f z = 0`. Conclude with `Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)`. Use `right push Not at hf0`. Take `⟨p, hp, hfp⟩` from `hf0`.

Establish `hgp : g =ᶠ[𝓝 p] 0` using `by filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp] with z hz1 hz2`. Conclude with `(mul_eq_zero.1 (hball hz2).2).resolve_left hz1`. Establish `hgan : AnalyticOnNhd ℂ g (Metric.ball y r)` using `fun z hz => (hball hz).1.2`. Establish `hzero` using `hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp`. Conclude with `Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz`.
-/
private theorem germ_zero_of_mul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Take `⟨z, hz⟩` from `hprod.exists`. Simplify using `at hz`. Consider the case `insert a s ha ih`.

Establish `hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y` using `Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)`. Establish `hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0` using `by filter_upwards [hprod] with z hz`. Rewrite `hz` using `[Finset.prod_insert ha]`. Then use the resulting hypothesis. Break down `germ_zero_of_mul_zero (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1` into its components or cases. Conclude with `⟨a, Finset.mem_insert_self a s, h1⟩`.

Take `⟨i, hi, h2⟩` from `ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1`. Conclude with `⟨i, Finset.mem_insert_of_mem hi, h2⟩`.
-/
private theorem germ_factor_zero_of_prod_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_zero_of_mul_zero (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

/- English proof (translation)
Establish `hEq : N \ Y = ⋃ m, N ∩ φ m ⁻¹' {0}ᶜ`. Use extensionality with `z`. Simplify using `only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzN, hzY⟩`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hz : z ∈ Y ∩ N`. Rewrite using `[hY]`. Conclude with `⟨hzN, fun m => hcon m hzN⟩`.

Conclude with `hzY hz.1`. Introduce and unpack `⟨m, hzN, hzm⟩`. Use `⟨hzN, fun hzY => hzm ?_⟩` and prove the remaining obligations. Establish `hz : z ∈ Y ∩ N` using `⟨hzY, hzN⟩`. Rewrite `hz` using `[hY]`.

Conclude with `hz.2 m`. Rewrite using `[hEq]`. Conclude with `isOpen_iUnion fun m => (hφ m).continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton`.
-/
private theorem isOpen_diff_of_zeroSet {σ : Type} [Fintype σ] {Y N : Set (σ → ℂ)} {k : ℕ}
    {φ : Fin k → (σ → ℂ) → ℂ} (hN : IsOpen N) (hφ : ∀ m, AnalyticOnNhd ℂ (φ m) N)
    (hY : Y ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0}) : IsOpen (N \ Y) := by
  have hEq : N \ Y = ⋃ m, N ∩ φ m ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzN, hzY⟩
      by_contra hcon
      push Not at hcon
      have hz : z ∈ Y ∩ N := by
        rw [hY]
        exact ⟨hzN, fun m => hcon m hzN⟩
      exact hzY hz.1
    · rintro ⟨m, hzN, hzm⟩
      refine ⟨hzN, fun hzY => hzm ?_⟩
      have hz : z ∈ Y ∩ N := ⟨hzY, hzN⟩
      rw [hY] at hz
      exact hz.2 m
  rw [hEq]
  exact isOpen_iUnion fun m => (hφ m).continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton

/- English proof (translation)
Introduce `σ _ X B k f d A hB hf hXB hopen w hw hiso`. Take `⟨n, Y, hY, hsepY, W0, hW0, hXW0⟩` from `hcomp σ X B k f d A hB hf hXB hopen w hw`. Take `⟨W, hW, hWiso⟩` from `hiso`. Establish `hisoY : ∀ i, ∃ W' ∈ 𝓝 w, ∀ x ∈ Y i ∩ W', A x = A w → x = w` using `fun i => ⟨W ∩ W0, inter_mem hW hW0, fun x hx hAx => by`. Establish `hxX : x ∈ X ∩ B ∩ W0`.

Rewrite using `[hXW0]`. Conclude with `⟨Set.mem_iUnion.2 ⟨i, hx.1⟩, hx.2.2⟩`. Conclude with `hWiso x ⟨hxX.1, hx.2.1⟩ hAx⟩`. Establish `hsh : ∀ i, ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) ∧ ∃ M ∈ 𝓝 w, ∀ y ∈ Y i ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ Y i ∩ …`. Introduce `i`.

Take `⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hP, hsep, hQ⟩` from `hprim σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2`. Conclude with `⟨δ, hδ, hδ0, hsheet σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2 ℓ N a δ q ha hδ hq hδ0 hP hsep hQ⟩`. Use `choose δ hδa hδ0 M hM hMsh using hsh`. Establish `hsp : ∀ i j, ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧ (i ≠ j → ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j → e (A z) = 0)`. Introduce `i j`.

Distinguish the cases in `hij : i = j`. Use `⟨fun _ => 1, analyticAt_const, fun h => ?_, fun h => absurd hij h⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h.exists`. Conclude with `one_ne_zero hy`. Take `⟨e, he, he0, hez⟩` from `hmeet σ (Y i) (Y j) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY j).1 (hsepY i j hij)`.

Conclude with `⟨e, he, he0, fun _ => hez⟩`. Use `choose e hea he0 hez using hsp`. Establish `hYa : ∀ j, ∃ (N : Set (σ → ℂ)) (kk : ℕ) (φ : Fin kk → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧ (∀ m, AnalyticOnNhd ℂ (φ m) N) ∧ Y j ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0}` using `fun j => (hY j).1`. Use `choose N kk φ hNo hwN hφ hYN using hYa`. Establish `hfac : ∀ i, AnalyticAt ℂ (fun y => δ i y * ∏ j, e i j y) (A w)` using `fun i => (hδa i).mul (Finset.analyticAt_fun_prod _ fun j _ => hea i j)`.

Use `⟨interior W0 ∩ (⋂ i, M i) ∩ (⋂ j, N j) ∩ {z | ∀ i j, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0}, fun y => ∏ i, (δ i y * ∏ j, e i j y), ?_, Finset.analyticAt_fun_prod _ fun i _ => hfac i, ?_, ?_⟩` and prove the remaining obligations. Use `inter_mem (inter_mem (inter_mem (interior_mem_nhds.2 hW0) (iInter_mem.2 hM)) (iInter_mem.2 fun j => (hNo j).mem_nhds (hwN j))) ?_` and prove the remaining obligations. Establish `hev : ∀ i j, ∀ᶠ z in 𝓝 w, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0` using `fun i j => by`. Distinguish the cases in `hij : i = j`. Conclude with `Eventually.of_forall fun _ h => absurd hij h`.

Use `filter_upwards [hez i j hij] with z hz _ using hz`. Conclude with `eventually_all.2 fun i => eventually_all.2 fun j => hev i j`. Introduce `hg0`. Take `⟨i, -, hi⟩` from `germ_factor_zero_of_prod_zero (fun i y => δ i y * ∏ j, e i j y) Finset.univ (fun i _ => hfac i) hg0`. Break down `germ_zero_of_mul_zero (hδa i) (Finset.analyticAt_fun_prod _ fun j _ => hea i j) hi with h1 | h1` into its components or cases.

Conclude with `hδ0 i h1`. Take `⟨j, -, hj⟩` from `germ_factor_zero_of_prod_zero (e i) Finset.univ (fun j _ => hea i j) h1`. Conclude with `he0 i j hj`. Introduce `x hx hgx`. Take `⟨hxXB, ⟨⟨hxW0, hxM⟩, hxN⟩, hxe⟩` from `hx`.

Simplify using `only [Set.mem_iInter] at hxM hxN`. Establish `hgx' : ∀ i, δ i (A x) ≠ 0 ∧ ∀ j, e i j (A x) ≠ 0`. Introduce `i`. Establish `hi` using `(Finset.prod_ne_zero_iff.1 hgx) i (Finset.mem_univ i)`. Conclude with `⟨left_ne_zero_of_mul hi, fun j => (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hi)) j (Finset.mem_univ j)⟩`.

Establish `hxU : x ∈ (⋃ i, Y i) ∩ W0`. Rewrite using `[← hXW0]`. Conclude with `⟨hxXB, interior_subset hxW0⟩`. Take `⟨i, hxi⟩` from `Set.mem_iUnion.1 hxU.1`. Establish `hxnot : ∀ j, j ≠ i → x ∉ Y j` using `fun j hji hxj => (hgx' i).2 j (hxe i j (Ne.symm hji) hxi hxj)`.

Set `U : Set (σ → ℂ)` to `interior W0 ∩ ⋂ j, (if j = i then Set.univ else N j \ Y j)`. Establish `hUo : IsOpen U`. Use `isOpen_interior.inter (isOpen_iInter_of_finite fun j => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `isOpen_univ`.

Conclude with `isOpen_diff_of_zeroSet (hNo j) (hφ j) (hYN j)`. Establish `hxUm : x ∈ U`. Use `⟨hxW0, Set.mem_iInter.2 fun j => ?_⟩` and prove the remaining obligations. Use `split_ifs with hji`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `⟨hxN j, hxnot j hji⟩`. Establish `hXU : X ∩ B ∩ U = Y i ∩ U`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzXB, hzU⟩`.

Establish `hzW : z ∈ (⋃ i, Y i) ∩ W0`. Rewrite using `[← hXW0]`. Conclude with `⟨hzXB, interior_subset hzU.1⟩`. Take `⟨j, hzj⟩` from `Set.mem_iUnion.1 hzW.1`. Distinguish the cases in `hji : j = i`.

Rewrite `hzj` using `[hji]`. Conclude with `⟨hzj, hzU⟩`. Establish `hzj'` using `Set.mem_iInter.1 hzU.2 j`. Rewrite `hzj'` using `[if_neg hji]`. Conclude with `absurd hzj hzj'.2`.

Introduce and unpack `⟨hzi, hzU⟩`. Establish `hzW : z ∈ X ∩ B ∩ W0`. Rewrite using `[hXW0]`. Conclude with `⟨Set.mem_iUnion.2 ⟨i, hzi⟩, interior_subset hzU.1⟩`. Conclude with `⟨hzW.1, hzU⟩`.

Take `⟨O, V, h, hO, hV, hxV, hh, hAh, hYV⟩` from `hMsh i x ⟨hxi, hxM i⟩ (hgx' i).1`. Use `⟨O ∩ h ⁻¹' U, V ∩ U, h, hh.continuousOn.isOpen_inter_preimage hO hUo, hV.inter hUo, ⟨hxV, hxUm⟩, hh.mono Set.inter_subset_left, fun t ht => hAh t ht.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.image_inter_preimage, ← hYV]`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hzXB, hzV, hzU⟩`. Establish `hz : z ∈ Y i ∩ U`. Rewrite using `[← hXU]`. Conclude with `⟨hzXB, hzU⟩`. Conclude with `⟨⟨hz.1, hzV⟩, hzU⟩`.

Introduce and unpack `⟨⟨hzi, hzV⟩, hzU⟩`. Establish `hz : z ∈ X ∩ B ∩ U`. Rewrite using `[hXU]`. Conclude with `⟨hzi, hzU⟩`. Conclude with `⟨hz.1, hzV, hzU⟩`.
-/
theorem IsolatedFibreLocalUnbranched.proof (hcomp : OpenProjectionDominantComponents.Statement)
    (hmeet : IrreducibleGermMeetOverHypersurface.Statement)
    (hprim : IrreducibleGermPrimitiveForm.Statement)
    (hsheet : PrimitiveFormSheetedOffDiscriminant.Statement) :
    IsolatedFibreLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A hB hf hXB hopen w hw hiso
  obtain ⟨n, Y, hY, hsepY, W0, hW0, hXW0⟩ := hcomp σ X B k f d A hB hf hXB hopen w hw
  obtain ⟨W, hW, hWiso⟩ := hiso

  have hisoY : ∀ i, ∃ W' ∈ 𝓝 w, ∀ x ∈ Y i ∩ W', A x = A w → x = w := fun i =>
    ⟨W ∩ W0, inter_mem hW hW0, fun x hx hAx => by
      have hxX : x ∈ X ∩ B ∩ W0 := by
        rw [hXW0]
        exact ⟨Set.mem_iUnion.2 ⟨i, hx.1⟩, hx.2.2⟩
      exact hWiso x ⟨hxX.1, hx.2.1⟩ hAx⟩

  have hsh : ∀ i, ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) ∧
      ∃ M ∈ 𝓝 w, ∀ y ∈ Y i ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ Y i ∩ V = g '' O := by
    intro i
    obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hP, hsep, hQ⟩ :=
      hprim σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2
    exact ⟨δ, hδ, hδ0,
      hsheet σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2 ℓ N a δ q ha hδ hq hδ0 hP hsep hQ⟩
  choose δ hδa hδ0 M hM hMsh using hsh

  have hsp : ∀ i j, ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      (i ≠ j → ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j → e (A z) = 0) := by
    intro i j
    by_cases hij : i = j
    · refine ⟨fun _ => 1, analyticAt_const, fun h => ?_, fun h => absurd hij h⟩
      obtain ⟨y, hy⟩ := h.exists
      exact one_ne_zero hy
    · obtain ⟨e, he, he0, hez⟩ :=
        hmeet σ (Y i) (Y j) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY j).1 (hsepY i j hij)
      exact ⟨e, he, he0, fun _ => hez⟩
  choose e hea he0 hez using hsp

  have hYa : ∀ j, ∃ (N : Set (σ → ℂ)) (kk : ℕ) (φ : Fin kk → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
      (∀ m, AnalyticOnNhd ℂ (φ m) N) ∧ Y j ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0} := fun j => (hY j).1
  choose N kk φ hNo hwN hφ hYN using hYa
  have hfac : ∀ i, AnalyticAt ℂ (fun y => δ i y * ∏ j, e i j y) (A w) := fun i =>
    (hδa i).mul (Finset.analyticAt_fun_prod _ fun j _ => hea i j)
  refine ⟨interior W0 ∩ (⋂ i, M i) ∩ (⋂ j, N j) ∩
      {z | ∀ i j, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0},
    fun y => ∏ i, (δ i y * ∏ j, e i j y), ?_, Finset.analyticAt_fun_prod _ fun i _ => hfac i, ?_, ?_⟩
  · refine inter_mem (inter_mem (inter_mem (interior_mem_nhds.2 hW0) (iInter_mem.2 hM))
      (iInter_mem.2 fun j => (hNo j).mem_nhds (hwN j))) ?_
    have hev : ∀ i j, ∀ᶠ z in 𝓝 w, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0 := fun i j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · filter_upwards [hez i j hij] with z hz _ using hz
    exact eventually_all.2 fun i => eventually_all.2 fun j => hev i j
  · intro hg0
    obtain ⟨i, -, hi⟩ := germ_factor_zero_of_prod_zero (fun i y => δ i y * ∏ j, e i j y) Finset.univ
      (fun i _ => hfac i) hg0
    rcases germ_zero_of_mul_zero (hδa i) (Finset.analyticAt_fun_prod _ fun j _ => hea i j) hi with h1 | h1
    · exact hδ0 i h1
    · obtain ⟨j, -, hj⟩ := germ_factor_zero_of_prod_zero (e i) Finset.univ (fun j _ => hea i j) h1
      exact he0 i j hj
  · intro x hx hgx
    obtain ⟨hxXB, ⟨⟨hxW0, hxM⟩, hxN⟩, hxe⟩ := hx
    simp only [Set.mem_iInter] at hxM hxN
    have hgx' : ∀ i, δ i (A x) ≠ 0 ∧ ∀ j, e i j (A x) ≠ 0 := by
      intro i
      have hi := (Finset.prod_ne_zero_iff.1 hgx) i (Finset.mem_univ i)
      exact ⟨left_ne_zero_of_mul hi,
        fun j => (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hi)) j (Finset.mem_univ j)⟩
    have hxU : x ∈ (⋃ i, Y i) ∩ W0 := by
      rw [← hXW0]
      exact ⟨hxXB, interior_subset hxW0⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxU.1
    have hxnot : ∀ j, j ≠ i → x ∉ Y j := fun j hji hxj =>
      (hgx' i).2 j (hxe i j (Ne.symm hji) hxi hxj)

    let U : Set (σ → ℂ) := interior W0 ∩ ⋂ j, (if j = i then Set.univ else N j \ Y j)
    have hUo : IsOpen U := by
      refine isOpen_interior.inter (isOpen_iInter_of_finite fun j => ?_)
      split_ifs
      · exact isOpen_univ
      · exact isOpen_diff_of_zeroSet (hNo j) (hφ j) (hYN j)
    have hxUm : x ∈ U := by
      refine ⟨hxW0, Set.mem_iInter.2 fun j => ?_⟩
      split_ifs with hji
      · trivial
      · exact ⟨hxN j, hxnot j hji⟩
    have hXU : X ∩ B ∩ U = Y i ∩ U := by
      ext z
      constructor
      · rintro ⟨hzXB, hzU⟩
        have hzW : z ∈ (⋃ i, Y i) ∩ W0 := by
          rw [← hXW0]
          exact ⟨hzXB, interior_subset hzU.1⟩
        obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hzW.1
        by_cases hji : j = i
        · rw [hji] at hzj
          exact ⟨hzj, hzU⟩
        · have hzj' := Set.mem_iInter.1 hzU.2 j
          rw [if_neg hji] at hzj'
          exact absurd hzj hzj'.2
      · rintro ⟨hzi, hzU⟩
        have hzW : z ∈ X ∩ B ∩ W0 := by
          rw [hXW0]
          exact ⟨Set.mem_iUnion.2 ⟨i, hzi⟩, interior_subset hzU.1⟩
        exact ⟨hzW.1, hzU⟩

    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hYV⟩ := hMsh i x ⟨hxi, hxM i⟩ (hgx' i).1
    refine ⟨O ∩ h ⁻¹' U, V ∩ U, h, hh.continuousOn.isOpen_inter_preimage hO hUo, hV.inter hUo,
      ⟨hxV, hxUm⟩, hh.mono Set.inter_subset_left, fun t ht => hAh t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    constructor
    · rintro ⟨hzXB, hzV, hzU⟩
      have hz : z ∈ Y i ∩ U := by
        rw [← hXU]
        exact ⟨hzXB, hzU⟩
      exact ⟨⟨hz.1, hzV⟩, hzU⟩
    · rintro ⟨⟨hzi, hzV⟩, hzU⟩
      have hz : z ∈ X ∩ B ∩ U := by
        rw [hXU]
        exact ⟨hzi, hzU⟩
      exact ⟨hz.1, hzV, hzU⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
