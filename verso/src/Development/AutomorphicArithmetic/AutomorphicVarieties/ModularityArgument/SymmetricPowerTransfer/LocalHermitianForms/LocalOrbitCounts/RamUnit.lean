import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ L D h0 hD`. Take `⟨ε, hε⟩` from `L.exists_nonsq`. Use `⟨ε, if_neg fun h => ?_⟩` and prove the remaining obligations. Take `⟨a, b, e⟩` from `nm_symm h0 L.two_ne h (ε.isUnit.map _).ne_zero`. Conclude with `hD (e ▸ L.even_of_norm ε hε (e ▸ h0))`.
-/
theorem UpperTheory.V.Z.Sym.Loc.ramUnit : UpperTheory.V.Z.Sym.Loc.RamUnit := by
  intro O K _ _ _ _ _ Δ L D h0 hD
  obtain ⟨ε, hε⟩ := L.exists_nonsq
  refine ⟨ε, if_neg fun h => ?_⟩
  obtain ⟨a, b, e⟩ := nm_symm h0 L.two_ne h (ε.isUnit.map _).ne_zero
  exact hD (e ▸ L.even_of_norm ε hε (e ▸ h0))
