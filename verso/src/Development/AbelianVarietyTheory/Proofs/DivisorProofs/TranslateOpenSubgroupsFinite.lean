import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalBoxIndicator

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ S`. Use `filter_upwards [hcl.isOpen.mem_nhds hx] with y hy`.

Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Both sides reduce to the same expression. Use `filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Conclude with `HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)`.
-/
theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {S : Set X} (hcl : IsClopen S) (hco : IsCompact S) :
    Set.indicator S (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  classical
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

/- English proof (translation)
Introduce `F _ _ κ _ B hBo hBO hBcof r`. Use `⟨fun v => ?_, ?_⟩` and prove the remaining obligations. Use `set c : κ → v.adicCompletion F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) with hc`. Establish `hS : {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v} = (Homeomorph.subRight c) ⁻¹' (Set.univ.pi fun _ => (B v : Set (v.adicCompletion F)))`. Use extensionality with `x`.

Simplify using `[Set.mem_pi, hc]`. Establish `hBc : IsCompact (B v : Set (v.adicCompletion F))` using `(ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen (B v) (hBo v)) (hBO v)`. Establish `hT : IsClopen (Set.univ.pi fun _ : κ => (B v : Set (v.adicCompletion F)))` using `⟨isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen (B v) (hBo v), isOpen_set_pi Set.finite_univ fun _ _ => hBo v⟩`. Rewrite using `[hS]`. Conclude with `indicator_mem_SB (hT.preimage (Homeomorph.subRight c).continuous) ((Homeomorph.subRight c).isCompact_preimage.2 (isCompact_univ_pi fun _ => hBc))`.

Establish `hr : ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun i => (r i).2 filter_upwards [hr, hBcof] with v hv hBv`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations.

Rewrite using `[← SetLike.mem_coe, hBv, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(v.adicCompletionIntegers F).add_mem _ _ h (hv i)` as an intermediate fact. Simplify using `using this`.

Introduce `h`. Conclude with `(v.adicCompletionIntegers F).sub_mem h (hv i)`.
-/
theorem indicator_box_translate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  intro F _ _ κ _ B hBo hBO hBcof r
  refine ⟨fun v => ?_, ?_⟩
  · set c : κ → v.adicCompletion F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) with hc
    have hS : {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        = (Homeomorph.subRight c) ⁻¹' (Set.univ.pi fun _ => (B v : Set (v.adicCompletion F))) := by
      ext x
      simp [Set.mem_pi, hc]
    have hBc : IsCompact (B v : Set (v.adicCompletion F)) :=
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).of_isClosed_subset
        (AddSubgroup.isClosed_of_isOpen (B v) (hBo v)) (hBO v)
    have hT : IsClopen (Set.univ.pi fun _ : κ => (B v : Set (v.adicCompletion F))) :=
      ⟨isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen (B v) (hBo v),
        isOpen_set_pi Set.finite_univ fun _ _ => hBo v⟩
    rw [hS]
    exact indicator_mem_SB (hT.preimage (Homeomorph.subRight c).continuous)
      ((Homeomorph.subRight c).isCompact_preimage.2 (isCompact_univ_pi fun _ => hBc))
  · have hr : ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun i => (r i).2
    filter_upwards [hr, hBcof] with v hv hBv
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hBv, SetLike.mem_coe]
    constructor
    · intro h
      have := (v.adicCompletionIntegers F).add_mem _ _ h (hv i)
      simpa using this
    · intro h
      exact (v.adicCompletionIntegers F).sub_mem h (hv i)

end GlobalTheory.LocalBoxIndicator

end
