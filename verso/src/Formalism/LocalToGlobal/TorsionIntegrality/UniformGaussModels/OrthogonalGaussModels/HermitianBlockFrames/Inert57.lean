import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem cmOK_7 : Formalism.L2.Th1.Top.FrP.CmOK 1 1 2 7 := ⟨by norm_num, ⟨0, rfl⟩, by norm_num, by norm_num⟩

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem inert_5_7 : ¬ ∃ a : ZMod 5, a ^ 2 = -((7 : ℕ) : ZMod 5) := by decide

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
