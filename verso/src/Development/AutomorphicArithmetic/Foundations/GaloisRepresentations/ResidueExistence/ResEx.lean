import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.NormLtOneOfMemMax

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison

/- English proof (translation)
The claim follows from `CrystallineSemistableComparison.resEx`.
-/
theorem UpperTheory.Gal.CD.resEx :
    CrystallineSemistableComparison.ResEx := CrystallineSemistableComparison.resEx
