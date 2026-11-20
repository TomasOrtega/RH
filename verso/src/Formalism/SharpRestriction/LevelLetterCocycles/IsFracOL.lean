import Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.UnusedSlot80.BCW

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem OL_le {LL LL' : FinExt l} (hLL : LL.1 ≤ LL'.1) (x : ↥(OL LL)) :
    IntermediateField.inclusion hLL (x : ↥LL.1) ∈ OL LL' := by
  obtain ⟨p, hp, hx⟩ := x.2
  exact ⟨p, hp, by
    have := congrArg (IntermediateField.inclusion hLL) hx
    rw [map_zero] at this
    rw [← this, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    rfl⟩

def jO {LL LL' : FinExt l} (hLL : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion hLL (x : ↥LL.1), OL_le hLL x⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/- English proof (translation)
A detailed English derivation is pending.
-/
example (LL : FinExt l) : IsTopologicalRing ↥LL.1 := inferInstance
/- English proof (translation)
A detailed English derivation is pending.
-/
example (LL : FinExt l) : IsDomain ↥(OL LL) := inferInstance
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isFrac_OL (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  exact IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)

end Formalism.MainNotions.UnusedSlot80.BCF
