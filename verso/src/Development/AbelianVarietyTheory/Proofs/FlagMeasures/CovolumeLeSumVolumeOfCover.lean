import Mathlib
import Formalism.HermitianLattices.StatementMass

open MeasureTheory NumberField Finset

namespace GlobalTheory

open Pointwise in

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ L`. Establish `hF` using `ZLattice.isAddFundamentalDomain b (volume : Measure (ι → ℝ))`. Use `set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) with hFdef`. Use `haveI : Countable L := b.repr.toEquiv.countable_iff.2 inferInstance`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]`.

Use `le_trans ENNReal.ofReal_toReal_le ?_` and prove the remaining obligations. Use `le_trans ?_ (measure_biUnion_finset_le T A)` and prove the remaining obligations. Use `set U := ⋃ k ∈ T, A k with hU`. Use `haveI : MeasurableConstVAdd L (ι → ℝ) := ⟨fun c => by`. Express the relevant statement in the definitionally equal form `Measurable fun x : ι → ℝ => (c : ι → ℝ) + x`.

Conclude with `measurable_const_add _⟩`. Use `haveI : VAddInvariantMeasure L (ι → ℝ) volume := ⟨fun c s _ => measure_preimage_add volume (c : ι → ℝ) s⟩`. Rewrite using `[hF.measure_eq_tsum U]`. Use `le_trans (measure_mono ?_) (measure_iUnion_le _)` and prove the remaining obligations. Introduce `t ht`.

Take `⟨k, hk, l, hl, htl⟩` from `hcov t`. Use `Set.mem_iUnion.2 ⟨-(⟨l, hl⟩ : L), ?_, ht⟩` and prove the remaining obligations. Rewrite using `[Set.mem_neg_vadd_set_iff]`. Establish `: (⟨l, hl⟩ : L) +ᵥ t = t + l`. Express the relevant statement in the definitionally equal form `l + t = t + l`.

Conclude with `add_comm _ _`. Rewrite using `[this]`. Conclude with `Set.mem_biUnion hk htl`.
-/
theorem covolume_le_sum_volume_of_cover (ι : Type) [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (κ : Type) (T : Finset κ) (A : κ → Set (ι → ℝ))
    (_hA : ∀ k, MeasurableSet (A k))
    (hcov : ∀ t : ι → ℝ, ∃ k ∈ T, ∃ l ∈ L, t + l ∈ A k) :
    ENNReal.ofReal (ZLattice.covolume L volume) ≤ ∑ k ∈ T, volume (A k) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (ι → ℝ))
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) with hFdef
  haveI : Countable L := b.repr.toEquiv.countable_iff.2 inferInstance
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  refine le_trans ENNReal.ofReal_toReal_le ?_
  refine le_trans ?_ (measure_biUnion_finset_le T A)
  set U := ⋃ k ∈ T, A k with hU
  haveI : MeasurableConstVAdd L (ι → ℝ) :=
    ⟨fun c => by
      change Measurable fun x : ι → ℝ => (c : ι → ℝ) + x
      exact measurable_const_add _⟩
  haveI : VAddInvariantMeasure L (ι → ℝ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : ι → ℝ) s⟩
  rw [hF.measure_eq_tsum U]
  refine le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro t ht
  obtain ⟨k, hk, l, hl, htl⟩ := hcov t
  refine Set.mem_iUnion.2 ⟨-(⟨l, hl⟩ : L), ?_, ht⟩
  rw [Set.mem_neg_vadd_set_iff]
  have : (⟨l, hl⟩ : L) +ᵥ t = t + l := by
    change l + t = t + l
    exact add_comm _ _
  rw [this]
  exact Set.mem_biUnion hk htl

end GlobalTheory
