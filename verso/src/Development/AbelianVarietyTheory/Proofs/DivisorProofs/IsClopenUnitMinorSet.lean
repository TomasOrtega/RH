import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.UnitMinor

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `y hy`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`.

Distinguish the cases in `h0 : y = 0`. Substitute `h0` using the available equality. Use `⟨1, fun z hz ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Units.val_one, sub_zero, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢`. Conclude with `hz.ne`.

Establish `hv : valuation k y ≠ 0` using `by simpa using h0`. Use `⟨Units.mk0 _ hv, fun z hz ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢`. Establish `: z = y + (z - y)` using `by ring`. Rewrite using `[this, (valuation k).map_add_eq_of_lt_left hz]`.

Conclude with `hy`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `y hy`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨1, fun z hz ↦ ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_ofPred_eq, Units.val_one, Set.mem_setOf_eq] at hz hy ⊢`. Establish `: z = y + (z - y)` using `by ring`. Rewrite using `[this, (valuation k).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]`.
-/
theorem isClopen_setOf_valuation_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsClopen {x : k | valuation k x = 1} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
    rw [IsValuativeTopology.mem_nhds_iff']
    by_cases h0 : y = 0
    · subst h0
      refine ⟨1, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_one, sub_zero, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      exact hz.ne
    · have hv : valuation k y ≠ 0 := by simpa using h0
      refine ⟨Units.mk0 _ hv, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      have : z = y + (z - y) := by ring
      rw [this, (valuation k).map_add_eq_of_lt_left hz]
      exact hy
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [IsValuativeTopology.mem_nhds_iff']
    refine ⟨1, fun z hz ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_one, Set.mem_setOf_eq] at hz hy ⊢
    have : z = y + (z - y) := by ring
    rw [this, (valuation k).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

/- English proof (translation)
Establish `hI : IsClopen {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]}`. Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Conclude with `⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩`. Establish `hU : IsClopen (⋃ f : Fin n ↪ Fin d, (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1})`. Use `isClopen_iUnion_of_finite fun f ↦ (isClopen_setOf_valuation_eq_one k).preimage ?_` and prove the remaining obligations.

Conclude with `Continuous.matrix_det (Continuous.matrix_submatrix continuous_id _ _)`. Establish `e : unitMinorSet k n d = {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} ∩ ⋃ f : Fin n ↪ Fin d, (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1}`. Use extensionality with `Y`. Simplify using `[unitMinorSet]`. Rewrite using `[e]`.

Conclude with `hI.inter hU`.
-/
theorem isClopen_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) : IsClopen (unitMinorSet k n d) := by
  have hI : IsClopen {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    exact ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hU : IsClopen (⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1}) := by
    refine isClopen_iUnion_of_finite fun f ↦ (isClopen_setOf_valuation_eq_one k).preimage ?_
    exact Continuous.matrix_det (Continuous.matrix_submatrix continuous_id _ _)
  have e : unitMinorSet k n d = {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} ∩ ⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1} := by
    ext Y; simp [unitMinorSet]
  rw [e]; exact hI.inter hU

end GlobalTheory.FullRankCoinv.UnitMinor
