import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibniz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKReal.Conn.pow_apply_smul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNablaPowApplySmulLeibniz.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.nabla_pow_apply_smul_leibniz : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι), (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  first | exact @GlobalTheory.BKReal.Conn.pow_apply_smul | exact GlobalTheory.BKReal.Conn.pow_apply_smul | (intros; apply GlobalTheory.BKReal.Conn.pow_apply_smul <;> assumption)
