import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfPrimesRel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeError
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProofStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatumStatement
import Development.AutomorphicArithmetic.CharacterBoxes.SmallestPrimePolynomialBound
import Development.AutomorphicArithmetic.CharacterBoxes.HostWW
import Development.AutomorphicArithmetic.CharacterBoxes.KitS
import Development.AutomorphicArithmetic.CharacterBoxes.DesignS

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

/- English proof (authored)
Retain the thresholds, context constants, and objects from the given object construction. The parameter identification makes its input conditions the required ones. Each object already has the prescribed structural properties, and the new final predicate is true for every object.
-/
theorem objC_true {Q : Par → PtProp} (h : ObjCP Q) : DC.ObjC (fun _ _ _ _ _ _ _ _ _ => True) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  refine ⟨x0, fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  obtain ⟨p, e1, e2, e3, e4, e5, -⟩ := h s R H q0 a b M c u0 d1 d2 d3 d4 (by rw [← b2] at d5; exact d5) d0 d6 d7 d8 d9
  exact ⟨p, e1, e2, e3, e4, e5, trivial⟩

/- English proof (authored)
Obtain the small-prime input from the prime relation theorem and use the supplied Minkowski divisibility to invoke the admissible-twist object construction. The resulting objects give the unrestricted object input for the host-window theorem. Combine its host windows with the stronger object properties to form kits. The design theorem converts those kits into the required design for the class.
-/
theorem recS (QO : Par → ∀ D : D7, Obj D → Prop) (cT : ℝ → ℝ → ℝ) (hR : DC.MinkDiv → RecExP (fun κ => DQ.withQD (QO κ)))
    (hM : DC.MinkDiv) : ExD (clsP QO) cT := by
  intro la G hla hH
  have hS : SmallPrimeOne := GlobalTheory.EX.smallPrimeOne_of_primesRel GlobalTheory.Lin.primesRel_holds
  have hO := GlobalTheory.T.existsObjects_of_admissibleTwistDatum _ GlobalTheory.EX.normPrimes_and_levelPrime_unconditional.2 (hR hM)
  have hW : DC.HostWW la G.req := hostWW _ la _ hla (hostQ hS la G hH) (objC_true hO) GlobalTheory.T.windowShareRequirementClosedForm_proof
  exact designS (fun κ => ptO (DQ.withQD (QO κ))) cT la G hla hM (kitS _ la G hW hO)

end UpperTheory.Top
