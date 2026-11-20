import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal

namespace GlobalTheory.CoordsOfMemAdjoin

open IntermediateField

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_coords_of_mem_adjoin {F : Type*} [Field F] [Algebra ℚ F] {s : F} {c : ℚ}
    (hs : s ^ 2 = algebraMap ℚ F c) {x : F} (hx : x ∈ ℚ⟮s⟯) :
    ∃ a b : ℚ, x = algebraMap ℚ F a + algebraMap ℚ F b * s := by
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set F) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    refine ⟨0, 1, ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    simp
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a + a', b + b', ?_⟩
    simp only [map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add, map_mul, ← hs]
    ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_rat_coords {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {x : H.E} (hx : x ∈ H.K) :
    ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD := by
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hs : H.sqrtMinusD ^ 2 = algebraMap ℚ H.E (-(H.d : ℚ)) := by
    rw [map_neg, map_natCast]
    exact hb
  obtain ⟨a, b, h⟩ := exists_coords_of_mem_adjoin hs hx
  exact ⟨a, b, by simpa only [eq_ratCast] using h⟩

end GlobalTheory.CoordsOfMemAdjoin
