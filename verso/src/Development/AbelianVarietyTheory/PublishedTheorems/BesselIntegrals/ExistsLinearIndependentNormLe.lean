import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

noncomputable section

open Module Submodule

namespace GlobalTheory.Published

def SuccMinTransference : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ), 1 ≤ i → i ≤ n → succMin L i * succMin (dualLattice L) (n - i + 1) ≤ n

namespace SuccMinTransference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end SuccMinTransference

/- English proof (translation)
Introduce `n L _ _ i h1 hi`. Simplify `hi)` using `using h _ L i h1 (by simpa`.
-/
theorem SuccMinTransference.of_forall
    (h : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (i : ℕ), 1 ≤ i →
      i ≤ finrank ℝ E →
      succMin L i * succMin (dualLattice L) (finrank ℝ E - i + 1) ≤ finrank ℝ E) :
    SuccMinTransference := by
  intro n L _ _ i h1 hi
  simpa using h _ L i h1 (by simpa using hi)

/- English proof (translation)
Use `minNorm_one_real` as an intermediate fact. Rewrite `this` using `[minNorm]`. Simplify using `[dualLattice_one_real, this]`.
-/
example : succMin (1 : Submodule ℤ ℝ) 1 * succMin (dualLattice (1 : Submodule ℤ ℝ)) (1 - 1 + 1) =
    ((1 : ℕ) : ℝ) := by
  have := minNorm_one_real
  rw [minNorm] at this
  simp [dualLattice_one_real, this]

/- English proof (translation)
The claim follows from `h n _ i h1 hi`.
-/
example (h : SuccMinTransference) (n : ℕ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ n) :
    let L := span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    succMin L i * succMin (dualLattice L) (n - i + 1) ≤ n :=
  h n _ i h1 hi

end GlobalTheory.Published
