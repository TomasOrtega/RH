import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreSectionsCovering
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

/- English proof (translation)
Introduce `n e N A Ω X hX hfib hsec`. Set `f : X → Ω` to `Set.MapsTo.restrict _ X Ω hX`. Use `show IsCoveringMap f`. Establish `hAc : Continuous (fun x : Fin n → ℂ => A *ᵥ x)` using `(Matrix.mulVecLin A).continuous_of_finiteDimensional`. Use `choose O V' g hO hAO hV' hxV' hg hgx hAg hXV' using hsec`.

Establish `key : ∀ x₀ (h₀ : x₀ ∈ X) x, x ∈ X → x ∈ V' x₀ h₀ → g x₀ h₀ (A *ᵥ x) = x`. Introduce `x₀ h₀ x hx hxv`. Establish `hx' : x ∈ g x₀ h₀ '' O x₀ h₀` using `hXV' x₀ h₀ ▸ ⟨hx, hxv⟩`. Take `⟨o, ho, rfl⟩` from `hx'`. Rewrite using `[hAg x₀ h₀ o ho]`.

Establish `inX : ∀ x₀ (h₀ : x₀ ∈ X) w, w ∈ O x₀ h₀ → g x₀ h₀ w ∈ X ∧ g x₀ h₀ w ∈ V' x₀ h₀`. Introduce `x₀ h₀ w hw`. Establish `h : g x₀ h₀ w ∈ X ∩ V' x₀ h₀` using `hXV' x₀ h₀ ▸ ⟨w, hw, rfl⟩`. Conclude with `h`. Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases.

Establish `: IsEmpty X`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `hfib _ (hX x.2)`. Rewrite `h` using `[hN, Nat.cast_zero, Set.encard_eq_zero]`. Establish `hm : (x : Fin n → ℂ) ∈ {x' | x' ∈ X ∧ A *ᵥ x' = A *ᵥ (x : Fin n → ℂ)}` using `⟨x.2, rfl⟩`.

Rewrite `hm` using `[h]`. Conclude with `hm`. Conclude with `IsCoveringMap.of_isEmpty _`. Introduce `y`. Establish `hFenc : {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)}.encard = N` using `hfib y y.2`.

Establish `hFfin` using `Set.finite_of_encard_eq_coe hFenc`. Use `hFfin.to_subtype` as an intermediate fact. Establish `hFcard : Nat.card {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)} = N`. Rewrite using `[Nat.card_coe_set_eq, Set.ncard_def, hFenc]`. Both sides reduce to the same expression.

Set `eq` to `(Finite.equivFinOfCardEq hFcard).symm`. Set `pt : Fin N → Fin n → ℂ` to `fun i => (eq i : Fin n → ℂ)`. Establish `pt_mem : ∀ i, pt i ∈ X ∧ A *ᵥ pt i = y` using `fun i => (eq i).2`. Establish `pt_inj : Function.Injective pt` using `fun i j h => eq.injective (Subtype.ext h)`. Set `G : Fin N → (Fin (e + 1) → ℂ) → Fin n → ℂ` to `fun i => g (pt i) (pt_mem i).1`.

Set `OO : Fin N → Set (Fin (e + 1) → ℂ)` to `fun i => O (pt i) (pt_mem i).1`. Set `VV : Fin N → Set (Fin n → ℂ)` to `fun i => V' (pt i) (pt_mem i).1`. Establish `hGy : ∀ i, G i y = pt i` using `fun i => by`. Rewrite using `[← (pt_mem i).2]`. Conclude with `hgx (pt i) (pt_mem i).1`.

Establish `hOy : ∀ i, OO i ∈ 𝓝 (y : Fin (e + 1) → ℂ)` using `fun i => (hO _ _).mem_nhds (by have h : A *ᵥ pt i ∈ OO i := hAO _ _; rwa [(pt_mem i).2] at h)`. Establish `hGc : ∀ i, ∀ w ∈ OO i, ContinuousAt (G i) w` using `fun i w hw => (hg _ _).continuousOn.continuousAt ((hO _ _).mem_nhds hw)`. Establish `hS : ∀ᶠ w in 𝓝 (y : Fin (e + 1) → ℂ), (∀ i, w ∈ OO i) ∧ ∀ i j, i ≠ j → G i w ≠ G j w`. Use `(Filter.eventually_all.2 hOy).and (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hij : i = j`.

Conclude with `Filter.Eventually.of_forall fun _ h => absurd hij h`. Establish `hne : G i y ≠ G j y`. Rewrite using `[hGy, hGy]`. Conclude with `fun h => hij (pt_inj h)`. Conclude with `(((hGc i y (mem_of_mem_nhds (hOy i))).ne_iff_eventually_ne (hGc j y (mem_of_mem_nhds (hOy j)))).1 hne).mono fun _ hw _ => hw`.

Take `⟨W, hWS, hWo, hyW⟩` from `mem_nhds_iff.1 hS`. Establish `hWO : ∀ i, ∀ w ∈ W, w ∈ OO i` using `fun i w hw => (hWS hw).1 i`. Establish `hWd : ∀ w ∈ W, ∀ i j, i ≠ j → G i w ≠ G j w` using `fun w hw => (hWS hw).2`. Establish `hGX : ∀ i, ∀ w ∈ W, G i w ∈ X` using `fun i w hw => (inX _ _ w (hWO i w hw)).1`. Establish `hGV : ∀ i, ∀ w ∈ W, G i w ∈ VV i` using `fun i w hw => (inX _ _ w (hWO i w hw)).2`.

Establish `hAG : ∀ i, ∀ w ∈ W, A *ᵥ G i w = w` using `fun i w hw => hAg _ _ w (hWO i w hw)`. Establish `hfc : Continuous f` using `(hAc.comp continuous_subtype_val).subtype_mk fun x => hX x.2`. Establish `hres : ∀ i (q : Ω) (hq : (q : Fin (e + 1) → ℂ) ∈ W), f ⟨G i q, hGX i q hq⟩ = q` using `fun i q hq => Subtype.ext (hAG i q hq)`. Set `V : Set Ω` to `{p | (p : Fin (e + 1) → ℂ) ∈ W}`. Set `U : Fin N → Set X` to `fun i => {x | (x : Fin n → ℂ) ∈ VV i ∧ A *ᵥ (x : Fin n → ℂ) ∈ W}`.

Establish `hVo : IsOpen V` using `continuous_subtype_val.isOpen_preimage _ hWo`. Establish `hUo : ∀ i, IsOpen (U i)` using `fun i => continuous_subtype_val.isOpen_preimage _ ((hV' _ _).inter (hWo.preimage hAc))`. Establish `hUG : ∀ i (x : X), x ∈ U i → G i (A *ᵥ (x : Fin n → ℂ)) = x` using `fun i x hx => key _ _ _ x.2 hx.1`. Establish `open_iff : ∀ i {W' : Set Ω}, W' ⊆ V → (IsOpen W' ↔ IsOpen (f ⁻¹' W' ∩ U i))`. Introduce `i W' hW'V`.

Use `⟨fun h => (hfc.isOpen_preimage _ h).inter (hUo i), fun h => ?_⟩` and prove the remaining obligations. Take `⟨T', hT'o, hT'eq⟩` from `isOpen_induced_iff.1 h`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `p hp`. Establish `hpW : (p : Fin (e + 1) → ℂ) ∈ W` using `hW'V hp`.

Establish `hGp : G i p ∈ T'`. Establish `hm : (⟨G i p, hGX i p hpW⟩ : X) ∈ f ⁻¹' W' ∩ U i`. Use `⟨?_, hGV i p hpW, ?_⟩` and prove the remaining obligations. Use `show f ⟨G i p, hGX i p hpW⟩ ∈ W'`. Rewrite using `[hres i p hpW]`.

Conclude with `hp`. Use `show A *ᵥ G i p ∈ W`. Rewrite using `[hAG i p hpW]`. Conclude with `hpW`. Rewrite `hm` using `[← hT'eq]`.

Conclude with `hm`. Rewrite using `[mem_nhds_subtype]`. Use `⟨W ∩ G i ⁻¹' T', Filter.inter_mem (hWo.mem_nhds hpW) ((hGc i p (hWO i p hpW)).preimage_mem_nhds (hT'o.mem_nhds hGp)), ?_⟩` and prove the remaining obligations. Introduce and unpack `q ⟨hqW, hqT⟩`. Establish `hm : (⟨G i q, hGX i q hqW⟩ : X) ∈ Subtype.val ⁻¹' T'` using `hqT`.

Rewrite `hm` using `[hT'eq]`. Establish `h1` using `hm.1`. Rewrite `h1` using `[Set.mem_preimage, hres i q hqW]`. Conclude with `h1`. Establish `inj : ∀ i, (U i).InjOn f`.

Introduce `i x hx x' hx' hxx'`. Establish `h : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (x' : Fin n → ℂ)` using `congrArg Subtype.val hxx'`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hUG i x hx, ← hUG i x' hx', h]`. Establish `surj : ∀ i, (U i).SurjOn f V`.

Introduce `i p hp`. Use `⟨⟨G i p, hGX i p hp⟩, ⟨hGV i p hp, ?_⟩, hres i p hp⟩` and prove the remaining obligations. Use `show A *ᵥ G i p ∈ W`. Rewrite using `[hAG i p hp]`. Conclude with `hp`.

Establish `disj : Pairwise (Function.onFun Disjoint U)`. Introduce `i j hij`. Use `Set.disjoint_left.2 fun x hxi hxj => ?_` and prove the remaining obligations. Conclude with `hWd _ hxi.2 i j hij ((hUG i x hxi).trans (hUG j x hxj).symm)`. Establish `exh : f ⁻¹' V ⊆ ⋃ i, U i`.

Introduce `x hx`. Establish `hxW : A *ᵥ (x : Fin n → ℂ) ∈ W` using `hx`. Use `set w := A *ᵥ (x : Fin n → ℂ) with hw`. Establish `hwΩ : w ∈ Ω` using `hX x.2`. Establish `hFw` using `hfib w hwΩ`.

Establish `hsub : Set.range (fun i => G i w) ⊆ {x' | x' ∈ X ∧ A *ᵥ x' = w}`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨hGX i w hxW, hAG i w hxW⟩`. Establish `hinj : Function.Injective (fun i => G i w)`. Introduce `i j h`.

Assume the negation of the conclusion as `hij`. Conclude with `hWd w hxW i j hij h`. Establish `heq : Set.range (fun i => G i w) = {x' | x' ∈ X ∧ A *ᵥ x' = w}`. Use `((Set.finite_of_encard_eq_coe hFw).subset hsub).eq_of_subset_of_encard_le hsub ?_` and prove the remaining obligations. Rewrite using `[hFw]`.

Use `le_trans ?_ hinj.encard_range` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hxmem : (x : Fin n → ℂ) ∈ Set.range (fun i => G i w)`. Rewrite using `[heq]`. Conclude with `⟨x.2, rfl⟩`.

Take `⟨i, hi⟩` from `hxmem`. Use `Set.mem_iUnion.2 ⟨i, ?_, hxW⟩` and prove the remaining obligations. Use `show (x : Fin n → ℂ) ∈ VV i`. Rewrite using `[← hi]`. Conclude with `hGV i w hxW`.

Establish `: Nonempty (Fin N)` using `⟨⟨0, hN⟩⟩`. Establish `: Nonempty (Ω → X)` using `⟨fun _ => ⟨pt ⟨0, hN⟩, (pt_mem _).1⟩⟩`. Set `T` to `IsOpen.trivializationDiscrete (f := f) U V hVo open_iff inj surj disj exh`. Establish `hyT : y ∈ T.baseSet` using `hyW`. Conclude with `(IsEvenlyCovered.of_trivialization hyT).to_isEvenlyCovered_preimage`.
-/
theorem FibreSectionsCovering.proof : FibreSectionsCovering.Statement := by
  intro n e N A Ω X hX hfib hsec
  let f : X → Ω := Set.MapsTo.restrict _ X Ω hX
  show IsCoveringMap f
  have hAc : Continuous (fun x : Fin n → ℂ => A *ᵥ x) :=
    (Matrix.mulVecLin A).continuous_of_finiteDimensional
  choose O V' g hO hAO hV' hxV' hg hgx hAg hXV' using hsec

  have key : ∀ x₀ (h₀ : x₀ ∈ X) x, x ∈ X → x ∈ V' x₀ h₀ → g x₀ h₀ (A *ᵥ x) = x := by
    intro x₀ h₀ x hx hxv
    have hx' : x ∈ g x₀ h₀ '' O x₀ h₀ := hXV' x₀ h₀ ▸ ⟨hx, hxv⟩
    obtain ⟨o, ho, rfl⟩ := hx'
    rw [hAg x₀ h₀ o ho]

  have inX : ∀ x₀ (h₀ : x₀ ∈ X) w, w ∈ O x₀ h₀ → g x₀ h₀ w ∈ X ∧ g x₀ h₀ w ∈ V' x₀ h₀ := by
    intro x₀ h₀ w hw
    have h : g x₀ h₀ w ∈ X ∩ V' x₀ h₀ := hXV' x₀ h₀ ▸ ⟨w, hw, rfl⟩
    exact h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : IsEmpty X := by
      refine ⟨fun x => ?_⟩
      have h := hfib _ (hX x.2)
      rw [hN, Nat.cast_zero, Set.encard_eq_zero] at h
      have hm : (x : Fin n → ℂ) ∈ {x' | x' ∈ X ∧ A *ᵥ x' = A *ᵥ (x : Fin n → ℂ)} := ⟨x.2, rfl⟩
      rw [h] at hm
      exact hm
    exact IsCoveringMap.of_isEmpty _
  intro y

  have hFenc : {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)}.encard = N := hfib y y.2
  have hFfin := Set.finite_of_encard_eq_coe hFenc
  have := hFfin.to_subtype
  have hFcard : Nat.card {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)} = N := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hFenc]
    rfl
  let eq := (Finite.equivFinOfCardEq hFcard).symm
  let pt : Fin N → Fin n → ℂ := fun i => (eq i : Fin n → ℂ)
  have pt_mem : ∀ i, pt i ∈ X ∧ A *ᵥ pt i = y := fun i => (eq i).2
  have pt_inj : Function.Injective pt := fun i j h => eq.injective (Subtype.ext h)
  let G : Fin N → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun i => g (pt i) (pt_mem i).1
  let OO : Fin N → Set (Fin (e + 1) → ℂ) := fun i => O (pt i) (pt_mem i).1
  let VV : Fin N → Set (Fin n → ℂ) := fun i => V' (pt i) (pt_mem i).1
  have hGy : ∀ i, G i y = pt i := fun i => by
    rw [← (pt_mem i).2]
    exact hgx (pt i) (pt_mem i).1
  have hOy : ∀ i, OO i ∈ 𝓝 (y : Fin (e + 1) → ℂ) := fun i =>
    (hO _ _).mem_nhds (by have h : A *ᵥ pt i ∈ OO i := hAO _ _; rwa [(pt_mem i).2] at h)
  have hGc : ∀ i, ∀ w ∈ OO i, ContinuousAt (G i) w := fun i w hw =>
    (hg _ _).continuousOn.continuousAt ((hO _ _).mem_nhds hw)
  have hS : ∀ᶠ w in 𝓝 (y : Fin (e + 1) → ℂ), (∀ i, w ∈ OO i) ∧ ∀ i j, i ≠ j → G i w ≠ G j w := by
    refine (Filter.eventually_all.2 hOy).and
      (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · have hne : G i y ≠ G j y := by
        rw [hGy, hGy]
        exact fun h => hij (pt_inj h)
      exact (((hGc i y (mem_of_mem_nhds (hOy i))).ne_iff_eventually_ne
        (hGc j y (mem_of_mem_nhds (hOy j)))).1 hne).mono fun _ hw _ => hw
  obtain ⟨W, hWS, hWo, hyW⟩ := mem_nhds_iff.1 hS
  have hWO : ∀ i, ∀ w ∈ W, w ∈ OO i := fun i w hw => (hWS hw).1 i
  have hWd : ∀ w ∈ W, ∀ i j, i ≠ j → G i w ≠ G j w := fun w hw => (hWS hw).2
  have hGX : ∀ i, ∀ w ∈ W, G i w ∈ X := fun i w hw => (inX _ _ w (hWO i w hw)).1
  have hGV : ∀ i, ∀ w ∈ W, G i w ∈ VV i := fun i w hw => (inX _ _ w (hWO i w hw)).2
  have hAG : ∀ i, ∀ w ∈ W, A *ᵥ G i w = w := fun i w hw => hAg _ _ w (hWO i w hw)
  have hfc : Continuous f := (hAc.comp continuous_subtype_val).subtype_mk fun x => hX x.2
  have hres : ∀ i (q : Ω) (hq : (q : Fin (e + 1) → ℂ) ∈ W),
      f ⟨G i q, hGX i q hq⟩ = q := fun i q hq =>
    Subtype.ext (hAG i q hq)
  let V : Set Ω := {p | (p : Fin (e + 1) → ℂ) ∈ W}
  let U : Fin N → Set X := fun i => {x | (x : Fin n → ℂ) ∈ VV i ∧ A *ᵥ (x : Fin n → ℂ) ∈ W}
  have hVo : IsOpen V := continuous_subtype_val.isOpen_preimage _ hWo
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    continuous_subtype_val.isOpen_preimage _ ((hV' _ _).inter (hWo.preimage hAc))

  have hUG : ∀ i (x : X), x ∈ U i → G i (A *ᵥ (x : Fin n → ℂ)) = x := fun i x hx =>
    key _ _ _ x.2 hx.1
  have open_iff : ∀ i {W' : Set Ω}, W' ⊆ V → (IsOpen W' ↔ IsOpen (f ⁻¹' W' ∩ U i)) := by
    intro i W' hW'V
    refine ⟨fun h => (hfc.isOpen_preimage _ h).inter (hUo i), fun h => ?_⟩
    obtain ⟨T', hT'o, hT'eq⟩ := isOpen_induced_iff.1 h
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpW : (p : Fin (e + 1) → ℂ) ∈ W := hW'V hp
    have hGp : G i p ∈ T' := by
      have hm : (⟨G i p, hGX i p hpW⟩ : X) ∈ f ⁻¹' W' ∩ U i := by
        refine ⟨?_, hGV i p hpW, ?_⟩
        · show f ⟨G i p, hGX i p hpW⟩ ∈ W'
          rw [hres i p hpW]
          exact hp
        · show A *ᵥ G i p ∈ W
          rw [hAG i p hpW]
          exact hpW
      rw [← hT'eq] at hm
      exact hm
    rw [mem_nhds_subtype]
    refine ⟨W ∩ G i ⁻¹' T', Filter.inter_mem (hWo.mem_nhds hpW)
      ((hGc i p (hWO i p hpW)).preimage_mem_nhds (hT'o.mem_nhds hGp)), ?_⟩
    rintro q ⟨hqW, hqT⟩
    have hm : (⟨G i q, hGX i q hqW⟩ : X) ∈ Subtype.val ⁻¹' T' := hqT
    rw [hT'eq] at hm
    have h1 := hm.1
    rw [Set.mem_preimage, hres i q hqW] at h1
    exact h1
  have inj : ∀ i, (U i).InjOn f := by
    intro i x hx x' hx' hxx'
    have h : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (x' : Fin n → ℂ) := congrArg Subtype.val hxx'
    apply Subtype.ext
    rw [← hUG i x hx, ← hUG i x' hx', h]
  have surj : ∀ i, (U i).SurjOn f V := by
    intro i p hp
    refine ⟨⟨G i p, hGX i p hp⟩, ⟨hGV i p hp, ?_⟩, hres i p hp⟩
    show A *ᵥ G i p ∈ W
    rw [hAG i p hp]
    exact hp
  have disj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj => ?_
    exact hWd _ hxi.2 i j hij ((hUG i x hxi).trans (hUG j x hxj).symm)
  have exh : f ⁻¹' V ⊆ ⋃ i, U i := by
    intro x hx
    have hxW : A *ᵥ (x : Fin n → ℂ) ∈ W := hx
    set w := A *ᵥ (x : Fin n → ℂ) with hw
    have hwΩ : w ∈ Ω := hX x.2
    have hFw := hfib w hwΩ
    have hsub : Set.range (fun i => G i w) ⊆ {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      rintro _ ⟨i, rfl⟩
      exact ⟨hGX i w hxW, hAG i w hxW⟩
    have hinj : Function.Injective (fun i => G i w) := by
      intro i j h
      by_contra hij
      exact hWd w hxW i j hij h
    have heq : Set.range (fun i => G i w) = {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      refine ((Set.finite_of_encard_eq_coe hFw).subset hsub).eq_of_subset_of_encard_le hsub ?_
      rw [hFw]
      refine le_trans ?_ hinj.encard_range
      simp
    have hxmem : (x : Fin n → ℂ) ∈ Set.range (fun i => G i w) := by
      rw [heq]
      exact ⟨x.2, rfl⟩
    obtain ⟨i, hi⟩ := hxmem
    refine Set.mem_iUnion.2 ⟨i, ?_, hxW⟩
    show (x : Fin n → ℂ) ∈ VV i
    rw [← hi]
    exact hGV i w hxW
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Ω → X) := ⟨fun _ => ⟨pt ⟨0, hN⟩, (pt_mem _).1⟩⟩
  let T := IsOpen.trivializationDiscrete (f := f) U V hVo open_iff inj surj disj exh
  have hyT : y ∈ T.baseSet := hyW
  exact (IsEvenlyCovered.of_trivialization hyT).to_isEvenlyCovered_preimage

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
