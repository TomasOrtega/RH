import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSF
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NMeasInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotNuSigma

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.S.Pv.HaarSubS

/- English proof (translation)
Use `conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]`. Unfold `Formalism.UG.hform crdOf`. Simplify using `only [map_sum, map_mul, X.ιE_conj, X.J_eq, RingEquiv.apply_symm_apply, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]`. Establish `hst : ∀ x : D.host.E, star x = D.host.conj x` using `fun x => Formalism.MainNotions.S.Inh.tie_star D x`. Simplify using `only [hst]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_crdX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  unfold Formalism.UG.hform crdOf
  simp only [map_sum, map_mul, X.ιE_conj, X.J_eq, RingEquiv.apply_symm_apply, LinearMap.map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
  have hst : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.MainNotions.S.Inh.tie_star D x
  simp only [hst]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[← hform_crdX X v w, RingEquiv.symm_apply_apply]`.
-/
theorem hform_eqX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) =
      X.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

/- English proof (translation)
Establish `h : ∀ v w, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) = X.ιE.symm ((VS D).hT v w)` using `fun v w => hform_eqX X v w`. Unfold `Formalism.L2.SG.HidaSetting.HidaSetting.eR Formalism.L2.SG.HidaSetting.HidaSetting.fR Formalism.L2.SG.HidaSetting.HidaSetting.zR`. Use `⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h, X.ee, map_zero]`. Rewrite using `[h, X.ff, map_zero]`.

Apply the tactic sequence `rw [h, X.ef] split_ifs <;> simp`. Rewrite using `[h, (X.zu_orth u a).1, map_zero]`. Rewrite using `[h, (X.zu_orth u a).2, map_zero]`. Rewrite using `[h, X.zu_norm, map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]`. Conclude with `(D.mem u).A.T_prime.ne_zero`.
-/
theorem frameRelX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    PI.NMeasInv.FrameRel X.B.I X.eR X.fR (X.zR u) := by
  have h : ∀ v w, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) =
      X.ιE.symm ((VS D).hT v w) := fun v w => hform_eqX X v w
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.eR Formalism.L2.SG.HidaSetting.HidaSetting.fR Formalism.L2.SG.HidaSetting.HidaSetting.zR
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [h, X.ee, map_zero]
  · rw [h, X.ff, map_zero]
  · rw [h, X.ef]
    split_ifs <;> simp
  · rw [h, (X.zu_orth u a).1, map_zero]
  · rw [h, (X.zu_orth u a).2, map_zero]
  · rw [h, X.zu_norm, map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact (D.mem u).A.T_prime.ne_zero

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `PI.n_measure_invariant`. Introduce `D X u`. Establish `hF` using `frameRelX X u`. Establish `hμ : PI.NMeasInv.IsHaarOnSet X.B.I (PI.NMeasInv.Ninf X.B.I X.eR (X.zR u)) (X.muN u)` using `X.muN_haar u`. Conclude with `⟨h1 _ _ _ _ _ hF _ hμ, h2 _ _ _ _ _ hF _ hμ, h3 _ _ _ _ _ hF _ hμ, h4 _ _ _ _ _ hF _ hμ⟩`.
-/
theorem measN_holds : MeasN := by
  obtain ⟨h1, h2, h3, h4⟩ := PI.n_measure_invariant
  intro D X u
  have hF := frameRelX X u
  have hμ : PI.NMeasInv.IsHaarOnSet X.B.I (PI.NMeasInv.Ninf X.B.I X.eR (X.zR u)) (X.muN u) := X.muN_haar u
  exact ⟨h1 _ _ _ _ _ hF _ hμ, h2 _ _ _ _ _ hF _ hμ, h3 _ _ _ _ _ hF _ hμ, h4 _ _ _ _ _ hF _ hμ⟩

/- English proof (translation)
Introduce `D X u`. Use `haveI : SigmaFinite (X.nuQ u) := quotient_sigma_finite X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ _ (X.muN u) (X.muH u) (X.nuQ u) (X.muN_haar u) (X.muH_haar u) (X.nuQ_weil u)`. Use `infer_instance`.
-/
theorem nuQSFinite_holds : NuQSFinite := by
  intro D X u
  haveI : SigmaFinite (X.nuQ u) :=
    quotient_sigma_finite X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ _ (X.muN u) (X.muH u) (X.nuQ u)
      (X.muN_haar u) (X.muH_haar u) (X.nuQ_weil u)
  infer_instance

/- English proof (translation)
The claim follows from `stepSubG_of_MN measN_holds nuQSFinite_holds`.
-/
theorem stepSubG_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := stepSubG_of_MN measN_holds nuQSFinite_holds

end Formalism.L2.S.Pv.HaarSubS
