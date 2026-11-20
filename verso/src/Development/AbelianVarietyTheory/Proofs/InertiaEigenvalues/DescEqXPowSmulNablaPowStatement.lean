import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescEqXPowSmulNablaPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDescEqXPowSmulNablaPow.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι), C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  first | exact @GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | exact GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | (intros; apply GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow <;> assumption)
