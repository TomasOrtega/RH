import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.DatumToG

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

/- English proof (translation)
Introduce `E _ _ _ A z hz`. Establish `h1` using `congrArg (algebraMap (𝓞 E) E) A.tr_eq`. Establish `h2` using `congrArg (algebraMap (𝓞 E) E) A.nm_eq`. Simplify using `only [map_add, map_mul, map_intCast] at h1 h2`. Establish `hq : (A.ω : E) * (A.ω : E) = (A.tr : E) * (A.ω : E) - (A.nm : E)`.

Rewrite using `[← h1, ← h2]`. Simplify using `only [NumberField.RingOfIntegers.coe_eq_algebraMap]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hz` using `[← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)]`. Proceed by induction on `hz using Algebra.adjoin_induction with`.

Consider the case `mem x hx => exact ⟨0, 1, by simpa using hx⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add x y _ _ hx hy => obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy; exact ⟨a + c, b + d, by push_cast; ring⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`.

Take `⟨c, d, rfl⟩` from `hy`. Conclude with `⟨a * c - b * d * A.nm, a * d + b * c + b * d * A.tr, by push_cast; linear_combination (b * d : E) * hq⟩`.
-/
theorem UpperTheory.Reformulated.B.AdjoinSimpleRationalCoordinates.coords :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] (A : UpperTheory.Gal.W2.Seed.Arith E),
    ∀ z ∈ ℚ⟮(↑A.ω : E)⟯,
      ∃ (α : ℚ) (β : ℚ),
        z =
          (↑α : E) +
            (↑β : E) *
              (↑A.ω :
                E) := by
  intro E _ _ _ A z hz
  have h1 := congrArg (algebraMap (𝓞 E) E) A.tr_eq
  have h2 := congrArg (algebraMap (𝓞 E) E) A.nm_eq
  simp only [map_add, map_mul, map_intCast] at h1 h2
  have hq : (A.ω : E) * (A.ω : E) = (A.tr : E) * (A.ω : E) - (A.nm : E) := by
    rw [← h1, ← h2]; simp only [NumberField.RingOfIntegers.coe_eq_algebraMap]; ring
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)] at hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by simpa using hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy => obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy; exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - b * d * A.nm, a * d + b * c + b * d * A.tr, by push_cast; linear_combination (b * d : E) * hq⟩
