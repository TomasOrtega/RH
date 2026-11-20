import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L j χ z _ hj h`. Assume the negation of the conclusion as `h'`. Take `⟨s, u, t, h1, -⟩` from `exists_of_gOrb_ne hj h'`. Conclude with `h ⟨u, s, s.ne_zero, h1⟩`.
-/
theorem UpperTheory.V.Z.Sym.Loc.gOdd : UpperTheory.V.Z.Sym.Loc.GOdd := by
  intro O K _ _ _ _ _ Δ τ L j χ z _ hj h
  by_contra h'
  obtain ⟨s, u, t, h1, -⟩ := exists_of_gOrb_ne hj h'
  exact h ⟨u, s, s.ne_zero, h1⟩
