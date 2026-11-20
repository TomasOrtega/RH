import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsScaledIsometry
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem GlobalTheory.SelfDualIsom.landherrSelfDual : Formalism.L2.Pj.LandherrSelfDual := by
  unfold Formalism.L2.Pj.LandherrSelfDual
  exact GlobalTheory.SelfDualIsom.exists_scaled_isometry GlobalTheory.QNorm.hasseNormSt
