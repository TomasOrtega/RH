import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.ramUnit : UpperTheory.V.Z.Sym.Loc.RamUnit := by
  intro O K _ _ _ _ _ Δ L D h0 hD
  obtain ⟨ε, hε⟩ := L.exists_nonsq
  refine ⟨ε, if_neg fun h => ?_⟩
  obtain ⟨a, b, e⟩ := nm_symm h0 L.two_ne h (ε.isUnit.map _).ne_zero
  exact hD (e ▸ L.even_of_norm ε hε (e ▸ h0))
