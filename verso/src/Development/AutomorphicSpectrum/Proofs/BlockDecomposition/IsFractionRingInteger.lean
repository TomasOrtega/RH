import Mathlib

namespace GlobalTheory.CompanionTheory.LocalFieldValuationRing

/- English proof (translation)
The claim follows from `(Valuation.integer.integers (ValuativeRel.valuation k)).isFractionRing`.
-/
theorem isFractionRing_integer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsFractionRing (ValuativeRel.valuation k).integer k :=
  (Valuation.integer.integers (ValuativeRel.valuation k)).isFractionRing

end GlobalTheory.CompanionTheory.LocalFieldValuationRing
