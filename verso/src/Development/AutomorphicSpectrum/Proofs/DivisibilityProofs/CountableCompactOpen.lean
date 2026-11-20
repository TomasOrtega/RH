import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT.Inj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank

/- English proof (translation)
Establish `hb` using `TopologicalSpace.isBasis_countableBasis X`. Establish `hc` using `TopologicalSpace.countable_countableBasis X`. Establish `hfin : {t : Set (Set X) | t.Finite ∧ t ⊆ TopologicalSpace.countableBasis X}.Countable` using `Set.countable_setOf_finite_subset hc`. Use `(hfin.image fun t => ⋃₀ t).mono ?_` and prove the remaining obligations. Introduce and unpack `U ⟨hU, hK⟩`.

Take `⟨S, hS, rfl⟩` from `hb.open_eq_sUnion hU`. Take `⟨t, htS, htf, hcov⟩` from `hK.elim_finite_subcover_image (b := S) (c := fun s => s) (fun s hs => hb.isOpen (hS hs)) Set.sUnion_eq_biUnion.subset`. Use `⟨t, ⟨htf, htS.trans hS⟩, Set.Subset.antisymm ?_ ?_⟩` and prove the remaining obligations. Conclude with `Set.sUnion_subset_sUnion htS`. Simplify `hcov` using `[Set.sUnion_eq_biUnion]`.
-/
theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsOpen U ∧ IsCompact U}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis X
  have hc := TopologicalSpace.countable_countableBasis X
  have hfin : {t : Set (Set X) | t.Finite ∧ t ⊆ TopologicalSpace.countableBasis X}.Countable :=
    Set.countable_setOf_finite_subset hc
  refine (hfin.image fun t => ⋃₀ t).mono ?_
  rintro U ⟨hU, hK⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion hU
  obtain ⟨t, htS, htf, hcov⟩ := hK.elim_finite_subcover_image (b := S) (c := fun s => s)
    (fun s hs => hb.isOpen (hS hs)) Set.sUnion_eq_biUnion.subset
  refine ⟨t, ⟨htf, htS.trans hS⟩, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.sUnion_subset_sUnion htS
  · simpa [Set.sUnion_eq_biUnion] using hcov

/- English proof (translation)
Take `⟨hl, hK⟩` from `hf`. Establish `hK' : IsCompact (tsupport f)` using `hK`. Take `⟨t, ht⟩` from `hK'.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c}) (fun c => hl.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)`. Establish `hsum : f = ∑ c ∈ t, c • (f ⁻¹' {c}).indicator (1 : X → ℂ)`. Use function extensionality and compare the values at `x`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`.

Establish `hx : x ∈ tsupport f` using `subset_tsupport f (fun h0 => hne (by simpa using h0))`. Take `⟨c, hc, hxc⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Establish `: f x = c` using `hxc`. Conclude with `h (this ▸ hc)`. Rewrite using `[hsum]`.

Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hl.isOpen_fiber c, ?_⟩, rfl⟩)` and prove the remaining obligations. Use `hK'.of_isClosed_subset (hl.isClosed_fiber c) fun x hx => subset_tsupport f ?_` and prove the remaining obligations.

Establish `: f x = c` using `hx`. Simplify `hc` using `[Function.mem_support, this]`.
-/
theorem mem_span_indicator {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) :
    f ∈ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) := by
  classical
  obtain ⟨hl, hK⟩ := hf
  have hK' : IsCompact (tsupport f) := hK
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c})
    (fun c => hl.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hsum : f = ∑ c ∈ t, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      have hx : x ∈ tsupport f := subset_tsupport f (fun h0 => hne (by simpa using h0))
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hx)
      have : f x = c := hxc
      exact h (this ▸ hc)
  rw [hsum]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = 0
  · simp [hc]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hl.isOpen_fiber c, ?_⟩, rfl⟩)
    refine hK'.of_isClosed_subset (hl.isClosed_fiber c) fun x hx => subset_tsupport f ?_
    have : f x = c := hx
    simpa [Function.mem_support, this] using hc

/- English proof (translation)
Establish `hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U})` using `fun f hf => mem_span_indicator hf`. Use `(Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)` and prove the remaining obligations. Conclude with `Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)`.
-/
theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  have hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    fun f hf => mem_span_indicator hf
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)

end GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank
end
