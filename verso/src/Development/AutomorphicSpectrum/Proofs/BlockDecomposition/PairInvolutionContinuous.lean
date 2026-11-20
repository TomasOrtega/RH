import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalHypotheses

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem thetaGL_id_mem {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) {g : GLw n w}
    (hg : g ∈ GlobalTheory.LFun.KGL w n) : thetaGL n (RingHom.id _) g ∈ GlobalTheory.LFun.KGL w n := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) g = g :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) g) * (PhiU n _)⁻¹ ∈ _
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n)
    (GlobalTheory.BCT.LocGlue.intst E n w w (RingHom.id _) (fun _ => rfl) g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem sgP_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
    Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧
      ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  intro E _ _ a b w
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.LocTwist.continuous_thetaGL a (RingHom.id _) continuous_id).prodMap
      (GlobalTheory.LocTwist.continuous_thetaGL b (RingHom.id _) continuous_id)
  · rintro ⟨g₁, g₂⟩
    exact Prod.ext (GlobalTheory.LocTwist.thetaGL_thetaGL a (RingHom.id _) (fun _ => rfl) g₁)
      (GlobalTheory.LocTwist.thetaGL_thetaGL b (RingHom.id _) (fun _ => rfl) g₂)
  · rintro ⟨k₁, k₂⟩ hk
    exact ⟨thetaGL_id_mem a w hk.1, thetaGL_id_mem b w hk.2⟩

end GlobalTheory.CompanionTheory.LocalHypotheses

end
