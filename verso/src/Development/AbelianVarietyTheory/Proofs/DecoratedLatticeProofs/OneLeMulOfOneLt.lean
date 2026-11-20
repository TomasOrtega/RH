import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumLoc

variable {D : D7}

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem intAE_eq_hat :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mul_mem {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  rw [intAE_eq_hat] at hx hy ⊢
  exact GlobalTheory.AdIdem.mul_mem_hat _ _ hx hy

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem idem_mul_sum {es : Formalism.L2.DIV.Pl D.host.E → AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hes : ∀ Q ∈ S, Formalism.L2.NTheta.IsIdemAt (es Q) Q) (hc : (∑ Q ∈ S, es Q) * cA D (∑ Q ∈ S, es Q) = 0)
    {P : Formalism.L2.DIV.Pl D.host.E} (hP : P ∈ S) : es P * ∑ Q ∈ S, es Q = es P := by
  have h1 : ∀ i ∈ S, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ S, ∀ j ∈ S, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es S h1 hc
  rw [Finset.mul_sum, Finset.sum_eq_single P
    (fun Q hQ hQP => GlobalTheory.PlaceDatum.idemAt_mul (hes P hP) (hes Q hQ) (hcross P hP Q hQ) (hcross Q hQ P hP) hQP)
    (fun h => absurd hP h), h1 P hP]

end GlobalTheory.IdemSumLoc

namespace GlobalTheory.IdemSumLoc

end GlobalTheory.IdemSumLoc
