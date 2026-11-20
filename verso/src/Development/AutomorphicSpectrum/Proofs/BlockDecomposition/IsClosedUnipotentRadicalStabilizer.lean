import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isClosed_radN : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  intro D B W t d
  have e : (radN d : Set (GlobalTheory.RegSW.stab d)) =
      (Subtype.val : GlobalTheory.RegSW.stab d → GA D B) ⁻¹' (GlobalTheory.MixPer.radX d : Set (GA D B)) := by
    ext q
    constructor
    · rintro ⟨c, b, h⟩
      exact (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨b, c, h.trans (d.nC_mul_nB b c)⟩
    · intro h
      obtain ⟨b, c, h⟩ := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).1 h
      exact ⟨c, b, h.trans (d.nC_mul_nB b c).symm⟩
  rw [e]
  exact (GlobalTheory.JacMeas.isClosed_radX d).preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.QKAvg
