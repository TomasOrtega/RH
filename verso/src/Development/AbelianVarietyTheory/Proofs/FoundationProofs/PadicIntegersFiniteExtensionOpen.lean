import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `: FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Set `b` to `Module.finBasis ℚ_[l] ↥LL.1`. Establish `h : ∀ i, ∃ c : ℤ_[l], c ≠ 0 ∧ IsIntegral ℤ_[l] (c • b i)`. Introduce `i`. Establish `h1 : IsAlgebraic ℤ_[l] (b i)` using `(IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic _)`.

Conclude with `h1.exists_integral_multiple`. Use `choose c hc0 hc using h`. Establish `hcont : ∀ i, Continuous (fun x : ↥LL.1 => b.coord i x)` using `fun i => (b.coord i).continuous_of_finiteDimensional`. Establish `hopen : IsOpen {x : ↥LL.1 | ∀ i, ‖b.coord i x‖ < ‖(c i : ℚ_[l])‖}`. Rewrite using `[Set.ofPred_forall]`.

Conclude with `isOpen_iInter_of_finite fun i => isOpen_lt (hcont i).norm continuous_const`. Establish `hcq : ∀ i, (c i : ℚ_[l]) ≠ 0` using `fun i h => hc0 i (Subtype.ext h)`. Use `AddSubgroup.isOpen_of_mem_nhds (OL LL).toSubring.toAddSubgroup (g := 0) ?_` and prove the remaining obligations. Use `Filter.mem_of_superset (hopen.mem_nhds ?_) ?_` and prove the remaining obligations. Introduce `i`.

Simplify using `using hcq i`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `x ∈ OL LL`. Rewrite using `[← b.sum_repr x]`. Use `Subalgebra.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Establish `hle : ‖b.repr x i / (c i : ℚ_[l])‖ ≤ 1`. Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 (hcq i))]`. Conclude with `(hx i).le`. Set `d : ℤ_[l]` to `⟨_, hle⟩`. Establish `: b.repr x i • b i = d • (c i • b i)`.

Rewrite using `[← algebraMap_smul ℚ_[l] (c i), ← algebraMap_smul ℚ_[l] d, smul_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = b.repr x i / (c i : ℚ_[l]) * (c i : ℚ_[l])`. Rewrite using `[div_mul_cancel₀ _ (hcq i)]`. Rewrite using `[this]`.

Conclude with `Subalgebra.smul_mem _ (hc i) _`.
-/
theorem isOpen_integers_finExt (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    IsOpen ((OL LL : Subalgebra ℤ_[l] ↥LL.1) : Set ↥LL.1) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  let b := Module.finBasis ℚ_[l] ↥LL.1
  have h : ∀ i, ∃ c : ℤ_[l], c ≠ 0 ∧ IsIntegral ℤ_[l] (c • b i) := by
    intro i
    have h1 : IsAlgebraic ℤ_[l] (b i) :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic _)
    exact h1.exists_integral_multiple
  choose c hc0 hc using h
  have hcont : ∀ i, Continuous (fun x : ↥LL.1 => b.coord i x) := fun i =>
    (b.coord i).continuous_of_finiteDimensional
  have hopen : IsOpen {x : ↥LL.1 | ∀ i, ‖b.coord i x‖ < ‖(c i : ℚ_[l])‖} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (hcont i).norm continuous_const
  have hcq : ∀ i, (c i : ℚ_[l]) ≠ 0 := fun i h => hc0 i (Subtype.ext h)
  refine AddSubgroup.isOpen_of_mem_nhds (OL LL).toSubring.toAddSubgroup (g := 0) ?_
  refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
  · intro i
    simpa using hcq i
  · intro x hx
    change x ∈ OL LL
    rw [← b.sum_repr x]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    have hle : ‖b.repr x i / (c i : ℚ_[l])‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.2 (hcq i))]
      exact (hx i).le
    let d : ℤ_[l] := ⟨_, hle⟩
    have : b.repr x i • b i = d • (c i • b i) := by
      rw [← algebraMap_smul ℚ_[l] (c i), ← algebraMap_smul ℚ_[l] d, smul_smul]
      congr 1
      change _ = b.repr x i / (c i : ℚ_[l]) * (c i : ℚ_[l])
      rw [div_mul_cancel₀ _ (hcq i)]
    rw [this]
    exact Subalgebra.smul_mem _ (hc i) _

end GlobalTheory
