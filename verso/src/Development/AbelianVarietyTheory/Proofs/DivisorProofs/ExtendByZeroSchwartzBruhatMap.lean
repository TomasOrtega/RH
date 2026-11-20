import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section

namespace GlobalTheory.SchwartzBruhatRestrict

/- English proof (translation)
Introduce `F _ _ κ₁ κ _ _ j hj v`. Use `set ext : (κ₁ → Fv F v) → (κ → Fv F v) := fun y => Function.extend j y 0 with hext`. Establish `hr : Function.LeftInverse (fun x : κ → Fv F v => x ∘ j) ext` using `fun y => funext fun i => hj.extend_apply y 0 i`. Establish `hcr : Continuous (fun x : κ → Fv F v => x ∘ j)` using `continuous_pi fun i => continuous_apply (j i)`. Establish `hce : Continuous ext`.

Use `continuous_pi fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : ∃ i, j i = k`. Take `⟨i, rfl⟩` from `hk`. Simplify using `only [ext, hj.extend_apply]`. Conclude with `continuous_apply i`.

Simplify using `only [ext, Function.extend_apply' _ _ _ hk]`. Conclude with `continuous_const`. Establish `hemb : Topology.IsClosedEmbedding ext` using `hr.isClosedEmbedding hcr hce`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨φ, ⟨hlc, hcs⟩, rfl⟩`.

Conclude with `⟨hlc.comp_continuous hce, hcs.comp_isClosedEmbedding hemb⟩`. Introduce and unpack `φ₁ ⟨hlc, hcs⟩`. Set `O : Set (Fv F v)` to `(v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Establish `hOeq : O = ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F))`. Use extensionality with `x`.

Simplify using `only [O, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]`. Establish `hOo : IsOpen O` using `by rw [hOeq]; exact Valued.isOpen_integer _`. Establish `hOc : IsClosed O` using `by rw [hOeq]; exact Valued.isClosed_integer _`. Establish `hOk : IsCompact O` using `isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)`. Establish `hO0 : (0 : Fv F v) ∈ O` using `(v.adicCompletionIntegers F).zero_mem`.

Set `S : Set (κ → Fv F v)` to `{x | ∀ k, k ∉ Set.range j → x k ∈ O}`. Establish `hSeq : S = ⋂ k ∈ (Set.range j)ᶜ, (fun x : κ → Fv F v => x k) ⁻¹' O`. Use extensionality with `x`. Simplify using `[S]`. Establish `hSo : IsOpen S`.

Rewrite using `[hSeq]`. Conclude with `Set.Finite.isOpen_biInter (Set.toFinite _) fun k _ => hOo.preimage (continuous_apply k)`. Establish `hSc : IsClosed S`. Rewrite using `[hSeq]`. Conclude with `isClosed_biInter fun k _ => hOc.preimage (continuous_apply k)`.

Use `set g : (κ → Fv F v) → ℂ := fun x => φ₁ (x ∘ j) with hg`. Establish `hglc : IsLocallyConstant g` using `hlc.comp_continuous hcr`. Use `⟨S.indicator g, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ S`.

Use `filter_upwards [hSo.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hglc x] with y hy hgy`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx, hgy]`. Use `filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Set `C : κ → Set (Fv F v)` to `fun k => if h : k ∈ Set.range j then (fun y : κ₁ → Fv F v => y (Classical.choose h)) '' tsupport φ₁ else O`.

Establish `hC : IsCompact (Set.univ.pi C)`. Use `isCompact_univ_pi fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h : k ∈ Set.range j`. Simplify using `only [C, dif_pos h]`. Conclude with `hcs.isCompact.image (continuous_apply _)`.

Simplify using `only [C, dif_neg h]`. Conclude with `hOk`. Use `HasCompactSupport.intro hC fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hxS : x ∈ S`.

Assume the negation of the conclusion as `hxS`. Conclude with `hne (Set.indicator_of_notMem hxS _)`. Establish `hgx : g x ≠ 0` using `by rwa [Set.indicator_of_mem hxS] at hne`. Apply `hx` to reduce the goal to its premises. Introduce `k _`.

Distinguish the cases in `h : k ∈ Set.range j`. Simplify using `only [C, dif_pos h]`. Use `⟨x ∘ j, subset_tsupport _ hgx, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[Classical.choose_spec h]`.

Simplify using `only [C, dif_neg h]`. Conclude with `hxS k h`. Use function extensionality and compare the values at `y`. Rewrite using `[LinearMap.funLeft_apply]`. Establish `hyS : ext y ∈ S`.

Introduce `k hk`. Establish `hk' : ¬ ∃ i, j i = k` using `hk`. Simplify using `only [ext, Function.extend_apply' _ _ _ hk']`. Conclude with `hO0`. Rewrite using `[Set.indicator_of_mem hyS]`.

Conclude with `congrArg φ₁ (hr y)`.
-/
theorem map_funLeft_extendZero : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ v : Pl F, (SB (κ → Fv F v)).map (LinearMap.funLeft ℂ ℂ (fun y : κ₁ → Fv F v => Function.extend j y 0)) = SB (κ₁ → Fv F v) := by
  intro F _ _ κ₁ κ _ _ j hj v
  classical
  set ext : (κ₁ → Fv F v) → (κ → Fv F v) := fun y => Function.extend j y 0 with hext
  have hr : Function.LeftInverse (fun x : κ → Fv F v => x ∘ j) ext :=
    fun y => funext fun i => hj.extend_apply y 0 i
  have hcr : Continuous (fun x : κ → Fv F v => x ∘ j) :=
    continuous_pi fun i => continuous_apply (j i)
  have hce : Continuous ext := by
    refine continuous_pi fun k => ?_
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simp only [ext, hj.extend_apply]
      exact continuous_apply i
    · simp only [ext, Function.extend_apply' _ _ _ hk]
      exact continuous_const
  have hemb : Topology.IsClosedEmbedding ext := hr.isClosedEmbedding hcr hce
  apply le_antisymm
  · rintro _ ⟨φ, ⟨hlc, hcs⟩, rfl⟩
    exact ⟨hlc.comp_continuous hce, hcs.comp_isClosedEmbedding hemb⟩
  · rintro φ₁ ⟨hlc, hcs⟩
    let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hOeq : O = ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F)) := by
      ext x
      simp only [O, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        Valuation.mem_integer_iff]
    have hOo : IsOpen O := by rw [hOeq]; exact Valued.isOpen_integer _
    have hOc : IsClosed O := by rw [hOeq]; exact Valued.isClosed_integer _
    have hOk : IsCompact O :=
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    have hO0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
    let S : Set (κ → Fv F v) := {x | ∀ k, k ∉ Set.range j → x k ∈ O}
    have hSeq : S = ⋂ k ∈ (Set.range j)ᶜ, (fun x : κ → Fv F v => x k) ⁻¹' O := by
      ext x; simp [S]
    have hSo : IsOpen S := by
      rw [hSeq]
      exact Set.Finite.isOpen_biInter (Set.toFinite _) fun k _ => hOo.preimage (continuous_apply k)
    have hSc : IsClosed S := by
      rw [hSeq]
      exact isClosed_biInter fun k _ => hOc.preimage (continuous_apply k)
    set g : (κ → Fv F v) → ℂ := fun x => φ₁ (x ∘ j) with hg
    have hglc : IsLocallyConstant g := hlc.comp_continuous hcr
    refine ⟨S.indicator g, ⟨?_, ?_⟩, ?_⟩
    · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
      by_cases hx : x ∈ S
      · filter_upwards [hSo.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hglc x] with y hy hgy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hgy]
      · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · let C : κ → Set (Fv F v) := fun k =>
        if h : k ∈ Set.range j then (fun y : κ₁ → Fv F v => y (Classical.choose h)) '' tsupport φ₁ else O
      have hC : IsCompact (Set.univ.pi C) := by
        refine isCompact_univ_pi fun k => ?_
        by_cases h : k ∈ Set.range j
        · simp only [C, dif_pos h]
          exact hcs.isCompact.image (continuous_apply _)
        · simp only [C, dif_neg h]
          exact hOk
      refine HasCompactSupport.intro hC fun x hx => ?_
      by_contra hne
      have hxS : x ∈ S := by
        by_contra hxS; exact hne (Set.indicator_of_notMem hxS _)
      have hgx : g x ≠ 0 := by rwa [Set.indicator_of_mem hxS] at hne
      apply hx
      intro k _
      by_cases h : k ∈ Set.range j
      · simp only [C, dif_pos h]
        refine ⟨x ∘ j, subset_tsupport _ hgx, ?_⟩
        simp only [Function.comp_apply]
        rw [Classical.choose_spec h]
      · simp only [C, dif_neg h]
        exact hxS k h
    · funext y
      rw [LinearMap.funLeft_apply]
      have hyS : ext y ∈ S := by
        intro k hk
        have hk' : ¬ ∃ i, j i = k := hk
        simp only [ext, Function.extend_apply' _ _ _ hk']
        exact hO0
      rw [Set.indicator_of_mem hyS]
      exact congrArg φ₁ (hr y)

end GlobalTheory.SchwartzBruhatRestrict
