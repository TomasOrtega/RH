import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.UniformDiscreteness.FgOfUnifDiscrete

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower`.
-/
theorem discriminant_of_product_lower : ReciprocityTheory.ChartRestriction.G.TB.DiscOfProdLowerSt :=
  PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc`.
-/
theorem formalGroup_of_discriminant : ReciprocityTheory.ChartRestriction.G.TB.FGOfDiscSt :=
  PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.TBDisc.isLatticeOfDisc`.
-/
theorem isLattice_of_discriminant : ReciprocityTheory.ChartRestriction.G.TB.IsLatticeOfDiscSt :=
  PI.UnitaryGroupMassFormula.TBDisc.isLatticeOfDisc
