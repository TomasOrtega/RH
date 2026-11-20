import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg b`. Establish `h1` using `congrArg (fun y => (VS D).hT y (X.fY b)) hg`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, X.ef, map_zero, LinearMap.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`. Simplify using `using h1`.
-/
theorem linearIndependent_eX_of_dual {D : D7} (X : HidaSetting D) : LinearIndependent D.host.E X.eX := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have h1 := congrArg (fun y => (VS D).hT y (X.fY b)) hg
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, X.ef, map_zero,
    LinearMap.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  simpa using h1

/- English proof (translation)
Introduce `D X h t lam ht hl`. Use `set b := X.bas.reindex (finCongr (rank_eq X h)).symm with hb`. Establish `hc : ∀ z, cY X h z = b.equivFun z`. Introduce `z`. Use function extensionality and compare the values at `k`.

Simplify using `[cY, HidaSetting.crd, crdOf, hb, Module.Basis.repr_reindex]`. Establish `h0 : LinearIndependent D.host.E (fun a => b.equivFun (X.eX a))` using `(linearIndependent_eX_of_dual X).map' b.equivFun.toLinearMap b.equivFun.ker`. Establish `hs : ∀ a, scl t lam a ≠ 0` using `fun a => mul_ne_zero ht (pow_ne_zero _ hl)`. Establish `h1` using `h0.units_smul (fun a => Units.mk0 (scl t lam a) (hs a))`. Establish `he : (eM X h t lam).transpose = (fun a => Units.mk0 (scl t lam a) (hs a)) • fun a => b.equivFun (X.eX a)`.

Use function extensionality and compare the values at `a k`. Simplify using `[eM, hc, Matrix.transpose_apply, Units.smul_def]`. Rewrite using `[he]`. Conclude with `h1`.
-/
theorem eM_transpose_linearIndependent : ∀ {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → LinearIndependent D.host.E (GlobalTheory.Core.SBesEx.eM X h t lam).transpose := by
  intro D X h t lam ht hl
  set b := X.bas.reindex (finCongr (rank_eq X h)).symm with hb
  have hc : ∀ z, cY X h z = b.equivFun z := by
    intro z; funext k
    simp [cY, HidaSetting.crd, crdOf, hb, Module.Basis.repr_reindex]
  have h0 : LinearIndependent D.host.E (fun a => b.equivFun (X.eX a)) :=
    (linearIndependent_eX_of_dual X).map' b.equivFun.toLinearMap b.equivFun.ker
  have hs : ∀ a, scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have h1 := h0.units_smul (fun a => Units.mk0 (scl t lam a) (hs a))
  have he : (eM X h t lam).transpose =
      (fun a => Units.mk0 (scl t lam a) (hs a)) • fun a => b.equivFun (X.eX a) := by
    funext a k
    simp [eM, hc, Matrix.transpose_apply, Units.smul_def]
  rw [he]
  exact h1

end GlobalTheory.Core.SBesEx

end
