import ReciprocityTheory.GroupCohomology.Transgression

namespace ReciprocityTheory.Coh

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem fiveTerm_holds : FiveTermStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ N _ hN Q P hP I hI
  obtain ⟨tg, -, -, h₁, h₂⟩ := transgression_holds R G M N hN Q P hP I hI
  exact ⟨tg, h₁, h₂⟩

end ReciprocityTheory.Coh
