import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SchemeDescendsToSubalgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.NoethApprox

/- English proof (translation)
Introduce `R _ Y f h₁ h₂ h₃`. Take `⟨R₀, i, φ, Y₀, f₀, π, a, b, c, d, e⟩` from `GlobalTheory.SpreadScheme.hasModel (V := R) f`. Conclude with `⟨R₀, i, φ, Y₀, f₀, π, a, b, d, c, e⟩`.
-/
theorem schemeModels : GlobalTheory.SpreadingModels.SchemeModels := by
  intro R _ Y f h₁ h₂ h₃
  obtain ⟨R₀, i, φ, Y₀, f₀, π, a, b, c, d, e⟩ := GlobalTheory.SpreadScheme.hasModel (V := R) f
  exact ⟨R₀, i, φ, Y₀, f₀, π, a, b, d, c, e⟩

end GlobalTheory.CompanionTheory.NoethApprox
