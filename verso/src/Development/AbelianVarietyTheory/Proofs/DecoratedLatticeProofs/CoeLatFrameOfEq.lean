import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumOrientedExists
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.AdForm.VacStd

/- English proof (translation)
Substitute using the available equality. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coe_latFrame_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) :
    (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank := by
  subst h
  ext x
  show x ∈ GlobalTheory.PlaceModel.latFrame _ ↔ ∀ k, IsIntegral ℤ (x k)
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  exact Formalism.IndefR.Seed.FrmC.stdLat_std hs N (fun _ => false) N 0 x

/- English proof (translation)
Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gram_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) : S.gram = 1 := by
  subst h
  refine Matrix.ext fun a b => ?_
  refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs N (fun _ => false) N 0 a b).trans ?_
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn])
  · rw [Matrix.one_apply_ne hab]
    exact if_neg hab

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem cartan_of_gram {D : D7} {S : HSp D} (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have e : gramAt D S τ = 1 := by rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e]
  exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩

end GlobalTheory.AdForm.VacStd
