import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficientsStatement

open UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Introduce `Ω _ _ _ ε`. Take `⟨T, -⟩` from `GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients Ω ε`. Conclude with `⟨T⟩`.
-/
theorem UpperTheory.V.Z.Kato.Joint.towerEx :
    UpperTheory.V.Z.Kato.Joint.TowerEx := by
  intro Ω _ _ _ ε
  obtain ⟨T, -⟩ := GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients Ω ε
  exact ⟨T⟩
