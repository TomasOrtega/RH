import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.FrobProd

/- English proof (translation)
Take `⟨K, hK, hxK, hKu⟩` from `exists_compact_subset hu hx`. Take `⟨V, hV, hxV, hVK⟩` from `(loc_compact_Haus_tot_disc_of_zero_dim (H := X)).exists_subset_of_mem_open hxK isOpen_interior`. Establish `hVK' : V ⊆ K` using `hVK.trans interior_subset`. Conclude with `⟨V, hK.of_isClosed_subset hV.isClosed hVK', hV, hxV, hVK'.trans hKu⟩`.
-/
theorem exists_compact_clopen {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {x : X} {u : Set X} (hu : IsOpen u) (hx : x ∈ u) :
    ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ u := by
  obtain ⟨K, hK, hxK, hKu⟩ := exists_compact_subset hu hx
  obtain ⟨V, hV, hxV, hVK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := X)).exists_subset_of_mem_open
    hxK isOpen_interior
  have hVK' : V ⊆ K := hVK.trans interior_subset
  exact ⟨V, hK.of_isClosed_subset hV.isClosed hVK', hV, hxV, hVK'.trans hKu⟩

open Classical in

/- English proof (translation)
Use `mem_SB_iff.2 ⟨hξ.comp (fun t => if t = s then (1 : ℂ) else 0), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro hs fun x hx => ?_` and prove the remaining obligations. Establish `: ξ x ≠ s` using `hx`. Simplify using `[this]`.
-/
theorem fiber_ind_mem {X S : Type} [TopologicalSpace X] [T2Space X] {ξ : X → S}
    (hξ : IsLocallyConstant ξ) (s : S) (hs : IsCompact (ξ ⁻¹' {s})) :
    (fun x => if ξ x = s then (1 : ℂ) else 0) ∈ SB X := by
  refine mem_SB_iff.2 ⟨hξ.comp (fun t => if t = s then (1 : ℂ) else 0), ?_⟩
  refine HasCompactSupport.intro hs fun x hx => ?_
  have : ξ x ≠ s := hx
  simp [this]

open Classical in

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `h : ∀ᶠ y in nhds x, ∀ i, (y ∈ U i ↔ x ∈ U i)`. Rewrite using `[Filter.eventually_all]`. Introduce `i`.

Distinguish the cases in `hx : x ∈ U i`. Use `filter_upwards [(hU i).isOpen.mem_nhds hx] with y hy`. Conclude with `iff_of_true hy hx`. Use `filter_upwards [(hU i).compl.isOpen.mem_nhds hx] with y hy`. Conclude with `iff_of_false hy hx`.

Use `filter_upwards [h] with y hy`. Use extensionality with `i`. Simplify using `[hy i]`.
-/
theorem isLocallyConstant_pattern {X ι : Type} [TopologicalSpace X] [Fintype ι] {U : ι → Set X}
    (hU : ∀ i, IsClopen (U i)) :
    IsLocallyConstant (fun x => Finset.univ.filter (fun i => x ∈ U i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ᶠ y in nhds x, ∀ i, (y ∈ U i ↔ x ∈ U i) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hx : x ∈ U i
    · filter_upwards [(hU i).isOpen.mem_nhds hx] with y hy
      exact iff_of_true hy hx
    · filter_upwards [(hU i).compl.isOpen.mem_nhds hx] with y hy
      exact iff_of_false hy hx
  filter_upwards [h] with y hy
  ext i
  simp [hy i]

open Classical in

/- English proof (translation)
Take `⟨i, hi⟩` from `Finset.nonempty_iff_ne_empty.2 hs`. Use `(hc i).of_isClosed_subset ((isLocallyConstant_pattern hU).isClosed_fiber s) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : Finset.univ.filter (fun i => x ∈ U i) = s` using `hx`. Rewrite `hi` using `[← hx']`.

Simplify using `using hi`.
-/
theorem isCompact_pattern_fiber {X ι : Type} [TopologicalSpace X] [T2Space X] [Fintype ι]
    {U : ι → Set X} (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) (s : Finset ι)
    (hs : s ≠ ∅) :
    IsCompact ((fun x => Finset.univ.filter (fun i => x ∈ U i)) ⁻¹' {s}) := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs
  refine (hc i).of_isClosed_subset ((isLocallyConstant_pattern hU).isClosed_fiber s) ?_
  intro x hx
  have hx' : Finset.univ.filter (fun i => x ∈ U i) = s := hx
  rw [← hx'] at hi
  simpa using hi

open Classical in

/- English proof (translation)
Establish `hsum : (f : A × B → ℂ) = ∑ p : S × T, fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0`. Use function extensionality and compare the values at `q`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single (ξ q.1, η q.2)]`. Simplify using the standard rewrite rules. Introduce `p _ hp`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hp (Prod.ext h1.symm h2.symm)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Use `Eq.mpr (congrArg (· ∈ _) hsum) (Submodule.sum_mem _ fun p _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hex : ∃ q0 : A × B, ξ q0.1 = p.1 ∧ η q0.2 = p.2 ∧ (f : A × B → ℂ) q0 ≠ 0`. Take `⟨q0, h1, h2, h3⟩` from `hex`. Establish `hs : p.1 ≠ s0` using `fun h => h3 (h0 q0 (h1.trans h))`. Establish `ht : p.2 ≠ t0` using `fun h => h3 (h0' q0 (h2.trans h))`.

Set `ia : SB A` to `⟨_, fiber_ind_mem hξ p.1 (hcs _ hs)⟩`. Set `ib : SB B` to `⟨_, fiber_ind_mem hη p.2 (hct _ ht)⟩`. Establish `hia : ∀ x, (ia : A → ℂ) x = if ξ x = p.1 then 1 else 0` using `fun _ => rfl`. Establish `hib : ∀ x, (ib : B → ℂ) x = if η x = p.2 then 1 else 0` using `fun _ => rfl`. Use `Submodule.subset_span ⟨(f : A × B → ℂ) q0 • ia, ib, ?_, ?_⟩` and prove the remaining obligations.

Introduce `q ha hb`. Establish `e1 : ξ q.1 = p.1`. Assume the negation of the conclusion as `h`. Apply `ha` to reduce the goal to its premises. Simplify using `[hia, h]`.

Establish `e2 : η q.2 = p.2`. Assume the negation of the conclusion as `h`. Apply `hb` to reduce the goal to its premises. Simplify using `[hib, h]`. Rewrite using `[hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]`.

Conclude with `h3`. Use function extensionality and compare the values at `q`. Distinguish the cases in `e1 : ξ q.1 = p.1`. Distinguish the cases in `e2 : η q.2 = p.2`. Simplify using `[hia, hib, e1, e2, hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]`.

Simplify using `[hia, hib, e2]`. Simplify using `[hia, e1]`. Establish `hz : (fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0) = 0`. Use function extensionality and compare the values at `q`. Distinguish the cases in `e : ξ q.1 = p.1 ∧ η q.2 = p.2`.

Rewrite using `[if_pos e]`. Assume the negation of the conclusion as `h`. Conclude with `hex ⟨q, e.1, e.2, h⟩`. Rewrite using `[if_neg e]`. Both sides reduce to the same expression.

Rewrite using `[hz]`. Conclude with `Submodule.zero_mem _`.
-/
theorem span_of_factor {A B S T : Type} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    [T2Space B] [Fintype S] [Fintype T] {ξ : A → S} {η : B → T}
    (hξ : IsLocallyConstant ξ) (hη : IsLocallyConstant η) (s0 : S) (t0 : T)
    (hcs : ∀ s, s ≠ s0 → IsCompact (ξ ⁻¹' {s})) (hct : ∀ t, t ≠ t0 → IsCompact (η ⁻¹' {t}))
    (f : SB (A × B))
    (hΦ : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q')
    (h0 : ∀ q : A × B, ξ q.1 = s0 → (f : A × B → ℂ) q = 0)
    (h0' : ∀ q : A × B, η q.2 = t0 → (f : A × B → ℂ) q = 0) :
    (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B,
      (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧
        F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  have hsum : (f : A × B → ℂ) =
      ∑ p : S × T, fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0 := by
    funext q
    rw [Finset.sum_apply, Finset.sum_eq_single (ξ q.1, η q.2)]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hp (Prod.ext h1.symm h2.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine Eq.mpr (congrArg (· ∈ _) hsum) (Submodule.sum_mem _ fun p _ => ?_)
  by_cases hex : ∃ q0 : A × B, ξ q0.1 = p.1 ∧ η q0.2 = p.2 ∧ (f : A × B → ℂ) q0 ≠ 0
  · obtain ⟨q0, h1, h2, h3⟩ := hex
    have hs : p.1 ≠ s0 := fun h => h3 (h0 q0 (h1.trans h))
    have ht : p.2 ≠ t0 := fun h => h3 (h0' q0 (h2.trans h))
    let ia : SB A := ⟨_, fiber_ind_mem hξ p.1 (hcs _ hs)⟩
    let ib : SB B := ⟨_, fiber_ind_mem hη p.2 (hct _ ht)⟩
    have hia : ∀ x, (ia : A → ℂ) x = if ξ x = p.1 then 1 else 0 := fun _ => rfl
    have hib : ∀ x, (ib : B → ℂ) x = if η x = p.2 then 1 else 0 := fun _ => rfl
    refine Submodule.subset_span ⟨(f : A × B → ℂ) q0 • ia, ib, ?_, ?_⟩
    · intro q ha hb
      have e1 : ξ q.1 = p.1 := by
        by_contra h
        apply ha
        simp [hia, h]
      have e2 : η q.2 = p.2 := by
        by_contra h
        apply hb
        simp [hib, h]
      rw [hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
      exact h3
    · funext q
      by_cases e1 : ξ q.1 = p.1
      · by_cases e2 : η q.2 = p.2
        · simp [hia, hib, e1, e2, hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
        · simp [hia, hib, e2]
      · simp [hia, e1]
  · have hz : (fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0) = 0 := by
      funext q
      by_cases e : ξ q.1 = p.1 ∧ η q.2 = p.2
      · rw [if_pos e]
        by_contra h
        exact hex ⟨q, e.1, e.2, h⟩
      · rw [if_neg e]
        rfl
    rw [hz]
    exact Submodule.zero_mem _

open Classical in

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ _ _ f`. Establish `hlc : IsLocallyConstant (f : A × B → ℂ)` using `(mem_SB_iff.1 f.2).1`. Establish `hcs : HasCompactSupport (f : A × B → ℂ)` using `(mem_SB_iff.1 f.2).2`. Establish `hbox : ∀ q : A × B, ∃ U : Set A, ∃ V : Set B, IsCompact U ∧ IsClopen U ∧ IsCompact V ∧ IsClopen V ∧ q.1 ∈ U ∧ q.2 ∈ V ∧ ∀ q' : A × B, q'.1 ∈ U → q'.2 ∈ V → (f : A × B → ℂ) q' = (f : A × B → ℂ) q`. Introduce `q`.

Take `⟨u, v, hu, hv, hqu, hqv, huv⟩` from `isOpen_prod_iff.1 (hlc.isOpen_fiber ((f : A × B → ℂ) q)) q.1 q.2 rfl`. Take `⟨U, hUc, hUo, hqU, hUu⟩` from `exists_compact_clopen hu hqu`. Take `⟨V, hVc, hVo, hqV, hVv⟩` from `exists_compact_clopen hv hqv`. Conclude with `⟨U, V, hUc, hUo, hVc, hVo, hqU, hqV, fun q' h1 h2 => huv ⟨hUu h1, hVv h2⟩⟩`. Use `choose U V hUc hUo hVc hVo hqU hqV hUV using hbox`.

Take `⟨t, -, ht⟩` from `hcs.isCompact.elim_nhds_subcover (fun q => U q ×ˢ V q) (fun q _ => ((hUo q).isOpen.prod (hVo q).isOpen).mem_nhds ⟨hqU q, hqV q⟩)`. Establish `hcov : ∀ q : A × B, (f : A × B → ℂ) q ≠ 0 → ∃ i : t, q.1 ∈ U i ∧ q.2 ∈ V i`. Introduce `q hq`. Use `ht (subset_tsupport _ hq)` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`.

Take `⟨i, hi, h⟩` from `this`. Conclude with `⟨⟨i, hi⟩, h.1, h.2⟩`. Set `ξ : A → Finset t` to `fun x => Finset.univ.filter (fun i : t => x ∈ U i)`. Set `η : B → Finset t` to `fun x => Finset.univ.filter (fun i : t => x ∈ V i)`. Establish `hξm : ∀ x i, i ∈ ξ x ↔ x ∈ U i` using `fun x i => by simp [ξ]`.

Establish `hηm : ∀ x i, i ∈ η x ↔ x ∈ V i` using `fun x i => by simp [η]`. Establish `hstep : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 → (f : A × B → ℂ) q ≠ 0 → (f : A × B → ℂ) q = (f : A × B → ℂ) q'`. Introduce `q q' e1 e2 hq`. Take `⟨i, h1, h2⟩` from `hcov q hq`. Establish `h1' : q'.1 ∈ U i` using `(hξm _ _).1 (e1 ▸ (hξm _ _).2 h1)`.

Establish `h2' : q'.2 ∈ V i` using `(hηm _ _).1 (e2 ▸ (hηm _ _).2 h2)`. Rewrite using `[hUV i q h1 h2, hUV i q' h1' h2']`. Use `span_of_factor (ξ := ξ) (η := η) (isLocallyConstant_pattern (U := fun i : t => U i) fun i => hUo i) (isLocallyConstant_pattern (U := fun i : t => V i) fun i => hVo i) ∅ ∅ (fun s hs => isCompact_pattern_fiber (U := fun i : t => U i) (fun i => hUo i) (fun i => hUc i) s hs) (fun s h …` and prove the remaining obligations. Introduce `q q' e1 e2`. Distinguish the cases in `hq : (f : A × B → ℂ) q = 0`.

Distinguish the cases in `hq' : (f : A × B → ℂ) q' = 0`. Rewrite using `[hq, hq']`. Conclude with `(hstep q' q e1.symm e2.symm hq').symm`. Conclude with `hstep q q' e1 e2 hq`. Introduce `q hq`.

Assume the negation of the conclusion as `h`. Take `⟨i, h1, -⟩` from `hcov q h`. Establish `: i ∈ ξ q.1` using `(hξm _ _).2 h1`. Rewrite `this` using `[hq]`. Simplify using `at this`.

Introduce `q hq`. Assume the negation of the conclusion as `h`. Take `⟨i, -, h2⟩` from `hcov q h`. Establish `: i ∈ η q.2` using `(hηm _ _).2 h2`. Rewrite `this` using `[hq]`.

Simplify using `at this`.
-/
theorem span_box : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] (f : SB (A × B)), (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B, (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧ F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  intro A B _ _ _ _ _ _ _ _ f
  have hlc : IsLocallyConstant (f : A × B → ℂ) := (mem_SB_iff.1 f.2).1
  have hcs : HasCompactSupport (f : A × B → ℂ) := (mem_SB_iff.1 f.2).2
  have hbox : ∀ q : A × B, ∃ U : Set A, ∃ V : Set B, IsCompact U ∧ IsClopen U ∧ IsCompact V ∧
      IsClopen V ∧ q.1 ∈ U ∧ q.2 ∈ V ∧
      ∀ q' : A × B, q'.1 ∈ U → q'.2 ∈ V → (f : A × B → ℂ) q' = (f : A × B → ℂ) q := by
    intro q
    obtain ⟨u, v, hu, hv, hqu, hqv, huv⟩ := isOpen_prod_iff.1
      (hlc.isOpen_fiber ((f : A × B → ℂ) q)) q.1 q.2 rfl
    obtain ⟨U, hUc, hUo, hqU, hUu⟩ := exists_compact_clopen hu hqu
    obtain ⟨V, hVc, hVo, hqV, hVv⟩ := exists_compact_clopen hv hqv
    exact ⟨U, V, hUc, hUo, hVc, hVo, hqU, hqV, fun q' h1 h2 => huv ⟨hUu h1, hVv h2⟩⟩
  choose U V hUc hUo hVc hVo hqU hqV hUV using hbox
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover (fun q => U q ×ˢ V q)
    (fun q _ => ((hUo q).isOpen.prod (hVo q).isOpen).mem_nhds ⟨hqU q, hqV q⟩)
  have hcov : ∀ q : A × B, (f : A × B → ℂ) q ≠ 0 → ∃ i : t, q.1 ∈ U i ∧ q.2 ∈ V i := by
    intro q hq
    have := ht (subset_tsupport _ hq)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h.1, h.2⟩
  let ξ : A → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ U i)
  let η : B → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ V i)
  have hξm : ∀ x i, i ∈ ξ x ↔ x ∈ U i := fun x i => by simp [ξ]
  have hηm : ∀ x i, i ∈ η x ↔ x ∈ V i := fun x i => by simp [η]
  have hstep : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 → (f : A × B → ℂ) q ≠ 0 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q' := by
    intro q q' e1 e2 hq
    obtain ⟨i, h1, h2⟩ := hcov q hq
    have h1' : q'.1 ∈ U i := (hξm _ _).1 (e1 ▸ (hξm _ _).2 h1)
    have h2' : q'.2 ∈ V i := (hηm _ _).1 (e2 ▸ (hηm _ _).2 h2)
    rw [hUV i q h1 h2, hUV i q' h1' h2']
  refine span_of_factor (ξ := ξ) (η := η)
    (isLocallyConstant_pattern (U := fun i : t => U i) fun i => hUo i)
    (isLocallyConstant_pattern (U := fun i : t => V i) fun i => hVo i) ∅ ∅
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => U i) (fun i => hUo i) (fun i => hUc i) s hs)
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => V i) (fun i => hVo i) (fun i => hVc i) s hs)
    f ?_ ?_ ?_
  · intro q q' e1 e2
    by_cases hq : (f : A × B → ℂ) q = 0
    · by_cases hq' : (f : A × B → ℂ) q' = 0
      · rw [hq, hq']
      · exact (hstep q' q e1.symm e2.symm hq').symm
    · exact hstep q q' e1 e2 hq
  · intro q hq
    by_contra h
    obtain ⟨i, h1, -⟩ := hcov q h
    have : i ∈ ξ q.1 := (hξm _ _).2 h1
    rw [hq] at this
    simp at this
  · intro q hq
    by_contra h
    obtain ⟨i, -, h2⟩ := hcov q h
    have : i ∈ η q.2 := (hηm _ _).2 h2
    rw [hq] at this
    simp at this

end GlobalTheory.CompanionTheory.FrobProd
