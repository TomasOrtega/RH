import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGLStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredientStatement

namespace GlobalTheory.CompanionTheory.Published

/- English proof (translation)
Introduce `k _ _ _ _` and use `⟨GlobalTheory.T.irreducible_smooth_admissible_GL k, GlobalTheory.T.jacquet_module_finite_length k, GlobalTheory.T.parabolic_induction_finite_length k, GlobalTheory.T.parabolic_induction_contragredient k⟩`.
-/
theorem bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  fun k _ _ _ _ => ⟨GlobalTheory.T.irreducible_smooth_admissible_GL k, GlobalTheory.T.jacquet_module_finite_length k, GlobalTheory.T.parabolic_induction_finite_length k, GlobalTheory.T.parabolic_induction_contragredient k⟩

end GlobalTheory.CompanionTheory.Published
