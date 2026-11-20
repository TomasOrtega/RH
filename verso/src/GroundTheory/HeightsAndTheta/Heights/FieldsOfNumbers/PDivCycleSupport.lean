import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPrincipalDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem DivCycleSupport.proof : DivCycleSupport.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hdim c f hf hfP W hW
  have h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by rw [divCycle, dif_neg h])
  obtain ⟨hmin, hrel⟩ := h
  have hWh : IsMultiHomogIdeal W := (Bridge.isMultiHomogIdeal_iff W).mpr
    (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
      ((Bridge.isMultiHomogIdeal_iff P).mp hP.multiHomog) ((Bridge.isMultiHomog_iff f c).mp hf) hmin)
  refine ⟨⟨hmin.1.1, hWh, hrel⟩, ?_⟩
  have := hP.isPrime
  have hPd : ringKrullDim (MRing ι F ⧸ P) = ((Fintype.card K + n + 1 : ℕ) : WithBot ℕ∞) := by
    apply relDim_map_injective (K := K)
    change relDim P = _
    rw [hdim]
    show (((n + 1 : ℕ) : ℤ) : WithBot (WithTop ℤ)) =
      ((((Fintype.card K + n + 1 : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ))
    congr 1
    push_cast
    ring
  have key : ringKrullDim (MRing ι F ⧸ W) + 1 = ringKrullDim (MRing ι F ⧸ P) :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_quot_minimal_add_one hfP hmin (fun h => by
      rw [hPd] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  rw [hPd] at key
  have hWd := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  rw [relDim_of_ringKrullDim_eq W _ hWd]
  show ((((Fintype.card K + n : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) =
    (((n : ℕ) : ℤ) : WithBot (WithTop ℤ))
  congr 1
  push_cast
  ring

end GroundTheory.Heights₂.Heights.FieldNumbers
