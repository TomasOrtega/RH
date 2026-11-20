import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.HeckePair

/- English proof (translation)
Introduce `G _ _ _ K hKo hKc g`. Establish `: DiscreteTopology (G ⧸ K)` using `QuotientGroup.discreteTopology hKo`. Establish `: CompactSpace K` using `isCompact_iff_compactSpace.mp hKc`. Establish `hcont : Continuous fun k : K => (((k : G) * g : G) : G ⧸ K)` using `(QuotientGroup.continuous_mk (N := K)).comp (continuous_subtype_val.mul continuous_const)`. Establish `hfin : (Set.range fun k : K => (((k : G) * g : G) : G ⧸ K)).Finite` using `(isCompact_range hcont).finite_of_discrete`.

Use `hfin.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨k, rfl⟩`.
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
