import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIsotropicFixesVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXUnipotentMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XZeroColumnLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XLastColumnLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatUnitPf

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem idAt_mul_idOff {D : D7} (P : Pl D → Prop) (a b : AE D) (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) : a * b = 0 := by
  have h1 : a * b ∈ idAt D P := Ideal.mul_mem_right _ _ ha
  have h2 : a * b ∈ idOff D P := Ideal.mul_mem_left _ _ hb
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at h1
  rw [idOff, Ideal.mem_iInf] at h2
  obtain ⟨hinf, hfin⟩ := h1
  rw [RingHom.mem_ker] at hinf
  apply GlobalTheory.LatVac.eq_zero_of_parts
  · exact hinf
  · apply GlobalTheory.SelfDualAt.eq_zero_of_compFin
    intro w
    by_cases hw : P w
    · have := h2 ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this
    · have := hfin ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem psiE_add {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) : psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  unfold psiE; rw [map_add, AddChar.map_add_eq_mul]

end GlobalTheory.FinPl.FlatUnitPf

end
