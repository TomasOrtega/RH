import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DA

variable {D : D7} {n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply GlobalTheory.AdelicU.matHom_injective
  exact Units.ext e

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (A B : Mx D k k) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  unfold compAt
  exact Matrix.map_one _ (by simp) (by simp)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finMap_mul {k : ℕ} (A B : Mx D k k) : (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) :=
  Matrix.map_mul (f := finPart D)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem compAt_conjT (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {k : ℕ} (A : Mx D k k) :
    compAt θ τ (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) A) = (compAt θ τ A)ᴴ := by
  ext i j
  simp only [compAt, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Simplify using the standard rewrite rules.
-/
theorem compAt_Jst (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    compAt θ τ ((Jst D n).map (incA D)) = reidx (JJ n) := by
  ext i j
  simp only [compAt, Matrix.map_apply]
  rw [(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1]
  simp only [Jst, blk4, reidx, JJ, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with a | a <;> rcases h2 : finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite]

end PositivityTheory.Rg.Sw.Glob.DA
