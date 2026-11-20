import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace DistinctCharacterUnits

/- English proof (translation)
Assume the negation of the conclusion as `hh`. Use `push Not at hh`. Conclude with `hne (MonoidHom.ext hh)`.
-/
theorem exists_unit_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {μ ν : kˣ →* ℂˣ} (hne : res μ ≠ res ν) : ∃ u : 𝒪[k]ˣ, μ (unitIncl k u) ≠ ν (unitIncl k u) := by
  by_contra hh
  push Not at hh
  exact hne (MonoidHom.ext hh)

end DistinctCharacterUnits

/- English proof (translation)
Introduce `hA E Ω _ _ _ _ _ A w h a ha n G b c hbc`. Take `⟨u, hu⟩` from `DistinctCharacterUnits.exists_unit_ne (G.dist b c hbc)`. Take `⟨t, ht⟩` from `(hA E Ω A w h a ha).2 (unitIncl _ u) (valuation_eq_one_iff.mpr ⟨u, rfl⟩)`. Conclude with `⟨t, by rw [ht]; exact hu⟩`.
-/
theorem distinctOnInertia_holds : DistinctOnUnitsDistinctOnInertia := by
  intro hA E Ω _ _ _ _ _ A w h a ha n G b c hbc
  obtain ⟨u, hu⟩ := DistinctCharacterUnits.exists_unit_ne (G.dist b c hbc)
  obtain ⟨t, ht⟩ := (hA E Ω A w h a ha).2 (unitIncl _ u) (valuation_eq_one_iff.mpr ⟨u, rfl⟩)
  exact ⟨t, by rw [ht]; exact hu⟩

end UpperTheory.NonzeroTypeTheory
