import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemNsp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing

open GlobalTheory.WeilM Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.CoverSB

/- English proof (translation)
Use `⟨?_, hg.2.mono fun x hx => by` and prove the remaining obligations. Apply the tactic sequence `by_contra h; exact hx (by by_cases hxW : x ∈ W <;> simp [Set.indicator, hxW, Function.notMem_support.1 h])⟩`. Establish `h1 : IsLocallyConstant (W.indicator (fun _ => (1 : ℂ)))` using `(IsLocallyConstant.iff_isOpen_fiber).2 fun c => by`. Apply the tactic sequence `by_cases h0 : c = 1 <;> by_cases h0' : c = 0`. Substitute `h0` using the available equality.

Simplify using `at h0'`. Substitute `h0` using the available equality. Use `hW.isOpen using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]`. Substitute `h0'` using the available equality.

Use `hW.compl.isOpen using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]`. Use `(isOpen_empty : IsOpen (∅ : Set X)) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx, Ne.symm h0, Ne.symm h0']`. Establish `e : W.indicator g = fun x => W.indicator (fun _ => (1 : ℂ)) x * g x`.

Apply the tactic sequence `funext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]`. Rewrite using `[e]`. Conclude with `h1.mul hg.1`.
-/
theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) {g : X → ℂ}
    (hg : g ∈ SB X) : W.indicator g ∈ SB X := by
  classical
  refine ⟨?_, hg.2.mono fun x hx => by
    by_contra h; exact hx (by by_cases hxW : x ∈ W <;> simp [Set.indicator, hxW, Function.notMem_support.1 h])⟩
  have h1 : IsLocallyConstant (W.indicator (fun _ => (1 : ℂ))) :=
    (IsLocallyConstant.iff_isOpen_fiber).2 fun c => by
      by_cases h0 : c = 1 <;> by_cases h0' : c = 0
      · subst h0; simp at h0'
      · subst h0
        convert hW.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · subst h0'
        convert hW.compl.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · convert (isOpen_empty : IsOpen (∅ : Set X)) using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx, Ne.symm h0, Ne.symm h0']
  have e : W.indicator g = fun x => W.indicator (fun _ => (1 : ℂ)) x * g x := by
    funext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
  rw [e]
  exact h1.mul hg.1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h0 : (fun y => x + y) ⁻¹' U ∈ 𝓝 (0 : Matrix A D k)`. Use `(continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using hU.mem_nhds hx`. Take `⟨a, ha⟩` from `GlobalTheory.LocMod.Inhab.exists_box_subset h0`. Establish `hBo` using `GlobalTheory.LocMod.Inhab.isOpen_box (Y := A) (Y' := D) a`.

Establish `hBc : IsClosed ((GlobalTheory.LocMod.Inhab.box A D a : AddSubgroup (Matrix A D k)) : Set (Matrix A D k))` using `AddSubgroup.isClosed_of_isOpen _ hBo`. Use `⟨(fun y => y - x) ⁻¹' (GlobalTheory.LocMod.Inhab.box A D a : Set (Matrix A D k)), ⟨hBc.preimage (continuous_id.sub continuous_const), hBo.preimage (continuous_id.sub continuous_const)⟩, by simpa using (GlobalTheory.LocMod.Inhab.box A D a).zero_mem, fun y hy => ?_⟩` and prove the remaining obligations. Use `ha _ hy` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_isClopen_subset {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    {U : Set (Matrix A D k)} (hU : IsOpen U) {x : Matrix A D k} (hx : x ∈ U) :
    ∃ V : Set (Matrix A D k), IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  have h0 : (fun y => x + y) ⁻¹' U ∈ 𝓝 (0 : Matrix A D k) := by
    refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hx
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset h0
  have hBo := GlobalTheory.LocMod.Inhab.isOpen_box (Y := A) (Y' := D) a
  have hBc : IsClosed ((GlobalTheory.LocMod.Inhab.box A D a : AddSubgroup (Matrix A D k)) : Set (Matrix A D k)) :=
    AddSubgroup.isClosed_of_isOpen _ hBo
  refine ⟨(fun y => y - x) ⁻¹' (GlobalTheory.LocMod.Inhab.box A D a : Set (Matrix A D k)),
    ⟨hBc.preimage (continuous_id.sub continuous_const), hBo.preimage (continuous_id.sub continuous_const)⟩,
    by simpa using (GlobalTheory.LocMod.Inhab.box A D a).zero_mem, fun y hy => ?_⟩
  have := ha _ hy
  simpa using this

end GlobalTheory.CoverSB

namespace GlobalTheory.CoverSB

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ _ _ ι _ U hU f hf hcov`. Use `set P := Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} with hP`. Establish `hcl : IsClosed (Function.support f)`. Establish `: Function.support f = (f ⁻¹' {0})ᶜ` using `by ext; simp`. Rewrite using `[this]`.

Conclude with `(hf.1.isOpen_fiber 0).isClosed_compl`. Establish `hcpt : IsCompact (Function.support f)`. Use `hf.2` as an intermediate fact. Rewrite `this` using `[HasCompactSupport, tsupport, hcl.closure_eq]`. Conclude with `this`.

Set `p : Set (Matrix A D k) → Prop` to `fun T => ∃ W, IsClopen W ∧ T ⊆ W ∧ ∀ g ∈ SB (Matrix A D k), Function.support g ⊆ W → g ∈ P`. Establish `hp : p (Function.support f)`. Use `hcpt.induction_on ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `⟨∅, isClopen_empty, subset_rfl, fun g _ hg => ?_⟩` and prove the remaining obligations. Establish `: g = 0`.

Use function extensionality and compare the values at `y`. Assume the negation of the conclusion as `h`. Conclude with `hg h`. Rewrite using `[this]`. Conclude with `P.zero_mem`.

Introduce and unpack `s t hst ⟨W, hW, htW, h⟩`. Conclude with `⟨W, hW, hst.trans htW, h⟩`. Introduce and unpack `s t ⟨W₁, hW₁, hs, h₁⟩ ⟨W₂, hW₂, ht, h₂⟩`. Use `⟨W₁ ∪ W₂, hW₁.union hW₂, Set.union_subset_union hs ht, fun g hg hsupp => ?_⟩` and prove the remaining obligations. Rewrite using `[← Set.indicator_self_add_compl W₁ g]`.

Use `P.add_mem (h₁ _ (indicator_mem_SB hW₁ hg) Set.support_indicator_subset) (h₂ _ (indicator_mem_SB hW₁.compl hg) fun y hy => ?_)` and prove the remaining obligations. Establish `hyc : y ∈ W₁ᶜ` using `Set.support_indicator_subset hy`. Establish `hyg : y ∈ Function.support g`. Assume the negation of the conclusion as `h; exact hy (by simp [Set.indicator, hyc, Function.notMem_support.1 h])`. Break down `hsupp hyg with h | h` into its components or cases.

Conclude with `absurd h hyc`. Conclude with `h`. Introduce `x hx`. Take `⟨i, hi⟩` from `hcov x hx`. Take `⟨V, hV, hxV, hVU⟩` from `exists_isClopen_subset (hU i) hi`.

Use `⟨V, mem_nhdsWithin_of_mem_nhds (hV.isOpen.mem_nhds hxV), V, hV, subset_rfl, fun g hg hsupp => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨hg, i, fun Y hY => hVU (hsupp hY)⟩`. Take `⟨W, -, hW, h⟩` from `hp`. Conclude with `h f hf hW`.
-/
theorem mem_span_of_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  intro k _ _ _ _ A D _ _ _ _ ι _ U hU f hf hcov
  set P := Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} with hP

  have hcl : IsClosed (Function.support f) := by
    have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hf.1.isOpen_fiber 0).isClosed_compl
  have hcpt : IsCompact (Function.support f) := by
    have := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
    exact this
  let p : Set (Matrix A D k) → Prop := fun T => ∃ W, IsClopen W ∧ T ⊆ W ∧
    ∀ g ∈ SB (Matrix A D k), Function.support g ⊆ W → g ∈ P
  have hp : p (Function.support f) := by
    refine hcpt.induction_on ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, fun g _ hg => ?_⟩
      have : g = 0 := by
        funext y; by_contra h; exact hg h
      rw [this]; exact P.zero_mem
    · rintro s t hst ⟨W, hW, htW, h⟩
      exact ⟨W, hW, hst.trans htW, h⟩
    · rintro s t ⟨W₁, hW₁, hs, h₁⟩ ⟨W₂, hW₂, ht, h₂⟩
      refine ⟨W₁ ∪ W₂, hW₁.union hW₂, Set.union_subset_union hs ht, fun g hg hsupp => ?_⟩
      rw [← Set.indicator_self_add_compl W₁ g]
      refine P.add_mem (h₁ _ (indicator_mem_SB hW₁ hg) Set.support_indicator_subset)
        (h₂ _ (indicator_mem_SB hW₁.compl hg) fun y hy => ?_)
      have hyc : y ∈ W₁ᶜ := Set.support_indicator_subset hy
      have hyg : y ∈ Function.support g := by
        by_contra h; exact hy (by simp [Set.indicator, hyc, Function.notMem_support.1 h])
      rcases hsupp hyg with h | h
      · exact absurd h hyc
      · exact h
    · intro x hx
      obtain ⟨i, hi⟩ := hcov x hx
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isClopen_subset (hU i) hi
      refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.isOpen.mem_nhds hxV), V, hV, subset_rfl, fun g hg hsupp => ?_⟩
      exact Submodule.subset_span ⟨hg, i, fun Y hY => hVU (hsupp hY)⟩
  obtain ⟨W, -, hW, h⟩ := hp
  exact h f hf hW

end GlobalTheory.CoverSB
