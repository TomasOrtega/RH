import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf

noncomputable section

namespace MassDataLevelSSteps.FrameW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem host_star_conj : Formalism.BasicNotions.bridge_star := by
  intro R H x
  haveI : NumberField.IsCMField H.E := H.isCMField_hostE
  have hemb : ∀ y : H.E, H.φ₀ (star y) = starRingEnd ℂ (H.φ₀ y) := by
    intro y
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj H.φ₀ y
      | exact NumberField.IsCMField.complexEmbedding_complexConj (K := H.E) H.φ₀ y
      | (show H.φ₀ (NumberField.IsCMField.complexConj H.E y) = _
         simp)
      | done
  have h1 : ∀ y, H.φ₀ (H.conj y) = starRingEnd ℂ (H.φ₀ y) :=
    (H.der.conj_iff H.φ₀ H.conj).mpr (by
      unfold Formalism.HC.HostRaw.conj
      exact MulEquiv.apply_symm_apply _ _)
  exact H.φ₀.injective ((hemb x).trans (h1 x).symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sig_apply {D : D7} (X : HidaSetting D) (a : X.B.I.E) : X.B.I.cm.sig a = star a := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hE_crdOf {D : D7} (X : HidaSetting D) (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  unfold hE crdOf
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply]
  conv_rhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  have hs : ∀ a : D.host.E,
      X.ιE ((X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) (X.ιE.symm a)) = star a := by
    intro a
    show X.ιE (star (X.ιE.symm a)) = _
    rw [X.ιE_conj, RingEquiv.apply_symm_apply]
    exact (host_star_conj _ D.host a).symm
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, RingEquiv.apply_symm_apply, hs, X.J_eq, LinearMap.map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem frameOf_isStd {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) := by
  refine ⟨fun a b => (hE_crdOf X (X.eX a) (X.eX b)).trans ?_,
    fun a b => (hE_crdOf X (X.fY a) (X.fY b)).trans ?_,
    fun a b => (hE_crdOf X (X.eX a) (X.fY b)).trans ?_,
    fun a => (hE_crdOf X (X.eX a) (X.zu u)).trans ?_,
    fun a => (hE_crdOf X (X.fY a) (X.zu u)).trans ?_,
    (hE_crdOf X (X.zu u) (X.zu u)).trans ?_, ?_⟩
  · rw [X.ee, map_zero]
  · rw [X.ff, map_zero]
  · rw [X.ef]
    split_ifs <;> simp
  · rw [(X.zu_orth u a).1, map_zero]
  · rw [(X.zu_orth u a).2, map_zero]
  · rw [X.zu_norm]
    simp
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact (D.mem u).A.T_prime.ne_zero

end MassDataLevelSSteps.FrameW

namespace MassDataLevelSSteps

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem frameStd_holds : FrameStd := by
  intro D X w
  exact ⟨_, FrameW.frameOf_isStd X w⟩

end MassDataLevelSSteps
