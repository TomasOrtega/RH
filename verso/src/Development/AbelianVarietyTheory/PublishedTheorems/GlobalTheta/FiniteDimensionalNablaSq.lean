import Mathlib
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.PolynomialDimension.WeylDim

open Formalism.BasicNotions

namespace GlobalTheory.Published

def WeylDimensionGL : Prop :=
  ∀ (n : ℕ) (lam : DomWeight n),
    (FiniteDimensional ℂ (nablaSq ℂ n lam) ∧
      (Module.finrank ℂ (nablaSq ℂ n lam) : ℚ) =
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          ((lam.w i : ℚ) - (lam.w j : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) ∧
    (FiniteDimensional ℂ (delSq ℂ n lam) ∧
      (Module.finrank ℂ (delSq ℂ n lam) : ℚ) =
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          ((lam.w i : ℚ) - (lam.w j : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)))

end GlobalTheory.Published

namespace GlobalTheory.WeylDimGL

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations.

Both sides reduce to the same expression.
-/
theorem weylDim_eq_prod_Ioi (n : ℕ) (lam : Fin n → ℤ) :
    Formalism.CountingSumsFrames.weylDim n lam = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      ((lam i : ℚ) - (lam j : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
  unfold Formalism.CountingSumsFrames.weylDim
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finiteDimensional_nablaSq (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) :
    FiniteDimensional K (nablaSq K n lam) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis K n n lam.natW
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  unfold nablaSq
  rw [← hb]
  exact FiniteDimensional.span_of_finite K (Set.finite_range b)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_nablaSq (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) :
    (Module.finrank K (nablaSq K n lam) : ℚ) = Formalism.CountingSumsFrames.weylDim n lam.w := by
  refine (Formalism.L2.G.Model.weyl_dualWeyl K n lam.natW (factNatW n lam).1).trans ?_
  unfold Formalism.CountingSumsFrames.weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [← (factNatW n lam).2.1 i, ← (factNatW n lam).2.1 j]
  push_cast
  congr 2
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_delSq (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n) :
    (Module.finrank K (delSq K n lam) : ℚ) = Formalism.CountingSumsFrames.weylDim n lam.w := by
  rw [← Formalism.L2.Col.nablaSq_eq_delSq K lam]
  exact finrank_nablaSq K n lam

end GlobalTheory.WeylDimGL

namespace GlobalTheory.Published

open GlobalTheory.WeylDimGL

end GlobalTheory.Published
