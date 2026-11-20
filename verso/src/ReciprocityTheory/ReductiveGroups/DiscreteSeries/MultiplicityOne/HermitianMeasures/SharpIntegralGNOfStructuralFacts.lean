import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nRecHaar_of_structural_facts (h : UnitaryGroupStructuralFacts) : NRecHaar := by
  exact h.1.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nilpotent_basis_of_hypotheses (h : UnitaryGroupStructuralFacts) : NBase := by
  exact h.1.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem compact_unitary_of_hypotheses (h : UnitaryGroupStructuralFacts) : CompactW := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem norm_lower_bound_of_hypotheses (h : UnitaryGroupStructuralFacts) : GNLower := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem haar_unique_of_hypotheses (h : UnitaryGroupStructuralFacts) : HaarUnique := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem closedN_of_structural_facts (h : UnitaryGroupStructuralFacts) : ClosedN := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem closed_unitary_of_hypotheses (h : UnitaryGroupStructuralFacts) : ClosedW := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_haar_W_of_structural_facts (h : UnitaryGroupStructuralFacts) : HaarWExists := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem haar_exists_nilpotent_of_hypotheses (h : UnitaryGroupStructuralFacts) : HaarNExists := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
