import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGStab

/- English proof (translation)
Introduce `F _ _ Δ D hD V _ _ ch B s hB`. Use `haveI := hD.real`. Use `⟨⟨?_, finG_stab' hD hB⟩, finG_test hD hB⟩` and prove the remaining obligations. Rewrite using `[hB.U]`. Conclude with `finG_cls_of hD B.ι (finG_cls hD.neg B.ι hB.ι)`.
-/
theorem UpperTheory.V.Z.Sym.Glob.finG :
    UpperTheory.V.Z.Sym.Glob.FinG := by
  intro F _ _ Δ D hD V _ _ ch B s hB
  haveI := hD.real
  refine ⟨⟨?_, finG_stab' hD hB⟩, finG_test hD hB⟩
  rw [hB.U]
  exact finG_cls_of hD B.ι (finG_cls hD.neg B.ι hB.ι)
