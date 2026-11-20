import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.HeckePair

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem stPair : StPair := by
  intro G _ _ _ K hKo hKc g
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hcont : Continuous fun k : K => (((k : G) * g : G) : G ⧸ K) :=
    (QuotientGroup.continuous_mk (N := K)).comp (continuous_subtype_val.mul continuous_const)
  have hfin : (Set.range fun k : K => (((k : G) * g : G) : G ⧸ K)).Finite :=
    (isCompact_range hcont).finite_of_discrete
  refine hfin.subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.HeckePair
