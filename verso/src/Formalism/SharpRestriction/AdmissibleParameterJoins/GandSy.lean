import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSm

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
The claim follows from `Formalism.MainNotions.WeightDegreeSizes.l2_bound_of_inputs hP hE hET ht hS hNT hN hGI (Formalism.MainNotions.WeightDegreeSizes.gainLe_of_fills hF hcs) hG h1 h5 hCL hSg hlin`.
-/
theorem period_conditions_of_pairing {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hET : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeSizes D L)
    (ht : Ties9 D L X Y c) (hS : c.NuServedDef X Y K) (hNT : NuAtTDef D L) (hN : Formalism.MainNotions.WeightDegreeSizes.NuInM D L)
    (hGI : Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K) (hF : ∀ w, ParametersFill X K w)
    (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop) (hG : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeCoprimeStabiliser D)
    (h1 : Formalism.MainNotions.WeilJacquetShalikaLaw.Conclusion1 D L X Y K c Dx T lev Xe ce 1) (h5 : Formalism.MainNotions.WeightDegreeSizes.ValuationAtLevelPrime D Dx T) {C1 C2 : ℝ}
    (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hSg : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1) (hlin : Formalism.MainNotions.WeightDegreeSizes.PerColSmul D) :
    Formalism.MainNotions.LocalQuadraticParts.adm2 D L :=
  Formalism.MainNotions.WeightDegreeSizes.l2_bound_of_inputs hP hE hET ht hS hNT hN hGI (Formalism.MainNotions.WeightDegreeSizes.gainLe_of_fills hF hcs) hG h1 h5 hCL hSg hlin

/- English proof (translation)
The claim follows from `Formalism.MainNotions.WeightDegreeSizes.fourth_complement_of_pairing hP hE hF h hCL hSg`.
-/
theorem no_gain_condition_of_pairing_sign {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hF : L.FDef)
    (h : Formalism.MainNotions.WeilJacquetShalikaLaw.ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce 1) {C1 C2 : ℝ} (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2)
    (hSg : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1) : Formalism.MainNotions.LocalQuadraticParts.adm12 D L :=
  Formalism.MainNotions.WeightDegreeSizes.fourth_complement_of_pairing hP hE hF h hCL hSg

/- English proof (translation)
Unfold `Formalism.MainNotions.WeightDegreeSizes.ServedHasModel`. Introduce `u w hw hV`. Use `Formalism.BasicNotions.gIdx_of_cand P K h3 u _ ?_ hw` and prove the remaining obligations. Unfold `VV at hV`. Assume the negation of the conclusion as `hc`.

Conclude with `hV (if_neg (fun h => hc h.1))`.
-/
theorem servedModel_of_params (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) :
    Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K := by
  unfold Formalism.MainNotions.WeightDegreeSizes.ServedHasModel
  intro u w hw hV
  refine Formalism.BasicNotions.gIdx_of_cand P K h3 u _ ?_ hw
  unfold VV at hV
  by_contra hc
  exact hV (if_neg (fun h => hc h.1))

end Formalism.MainNotions.J
