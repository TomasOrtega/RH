import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.ChartPlaces

variable {D : D7}

/- English proof (translation)
Use `(GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne ?_` and prove the remaining obligations. Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx]`. Conclude with `iff_of_true (zero_mem _) (zero_mem _)`.

Rewrite using `[(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]`.
-/
theorem mul_eq_zero_of_ne {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) {Q Q' : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (hQ' : Q' ∈ P)
    (hne : Q ≠ Q') : es Q * es Q' = 0 := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]

/- English proof (translation)
Introduce `D e P es hes hsum hec v hπ`. Establish `hsplit : ∀ Q ∈ P, Formalism.L2.Theta.IsSplitIdem D (es Q)` using `fun Q hQ => (hes Q hQ).1`. Establish `horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q' ≠ Q → es Q * es Q' = 0` using `fun Q hQ Q' hQ' hne => mul_eq_zero_of_ne hes hQ hQ' (Ne.symm hne)`. Establish `habs : ∀ Q ∈ P, es Q * e = es Q` using `fun Q hQ => by`. Rewrite using `[hsum]`.

Conclude with `GlobalTheory.PlaceModelSum.mul_sum_orth hsplit horth hQ`. Establish `hcross : ∀ Q ∈ P, ∀ Q' ∈ P, es Q' * cA D (es Q) = 0` using `fun Q hQ Q' hQ' => by`. Establish `h1 : cA D (es Q) * cA D e = cA D (es Q)` using `by rw [← map_mul, habs Q hQ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[habs Q' hQ', mul_comm (cA D e), h1]`.

Use `_ = es Q' * (e * cA D e) * cA D (es Q) := by ring`. Use `_ = 0 := by rw [hec, mul_zero, zero_mul]`. Introduce `Q Q' hvv`. Assume the negation of the conclusion as `hne`. Establish `hne' : (Q : Formalism.L2.DIV.Pl D.host.E) ≠ Q'` using `fun h => hne (Subtype.ext h)`.

Take `⟨π, hπc⟩` from `hπ Q`. Take `⟨π', hπc'⟩` from `hπ Q'`. Establish `hs' : Formalism.L2.Theta.IsSplitIdem D (cA D (es Q'))` using `GlobalTheory.PlaceModelSum.isSplitIdem_cA (hsplit Q' Q'.2)`. Take `⟨hid', hort', v', ε', ⟨α', rfl, hα1, hα0⟩, hsum'⟩` from `hs'`. Establish `hπ'1 : π' (cA D (es Q')) = 1`.

Use `(hπc'.2.1 (1 - cA D (es Q'))).2 (by rw [mul_sub, mul_one, hid', sub_self])` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero, eq_comm]`. Then use the resulting hypothesis. Establish `hπ'0 : π' (cA D (cA D (es Q'))) = 0` using `(hπc'.2.1 _).2 hort'`. Establish `hw1 : evalV D.host.F (v Q') α' = 1`. Use `hπc'.2.2.1 (pairA D.host.F 0 α')` as an intermediate fact.

Rewrite `this` using `[← hsum', map_add, hπ'1, hπ'0, add_zero]`. Conclude with `this.symm`. Establish `hwv : v Q' = v'`. Assume the negation of the conclusion as `h`. Rewrite `hw1` using `[hα0 _ h]`.

Conclude with `zero_ne_one hw1`. Establish `hA : π (cA D (es Q')) = 0` using `(hπc.2.1 _).2 (by`. Rewrite using `[← map_mul, mul_eq_zero_of_ne hes Q.2 Q'.2 hne', map_zero])`. Establish `hB : π (cA D (cA D (es Q'))) = 0` using `(hπc.2.1 _).2 (by`. Rewrite using `[cA_cA, mul_comm]`.

Conclude with `hcross Q Q.2 Q' Q'.2)`. Establish `hC` using `hπc.2.2.1 (pairA D.host.F 0 α')`. Rewrite `hC` using `[← hsum', map_add, hA, hB, add_zero]`. Establish `h0 : evalV D.host.F (v Q) α' = 0` using `hC.symm`. Rewrite `h0` using `[hvv.trans hwv, hα1]`.

Conclude with `one_ne_zero h0`.
-/
theorem chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  intro D e P es hes hsum hec v hπ
  have hsplit : ∀ Q ∈ P, Formalism.L2.Theta.IsSplitIdem D (es Q) := fun Q hQ => (hes Q hQ).1
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q' ≠ Q → es Q * es Q' = 0 :=
    fun Q hQ Q' hQ' hne => mul_eq_zero_of_ne hes hQ hQ' (Ne.symm hne)

  have habs : ∀ Q ∈ P, es Q * e = es Q := fun Q hQ => by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth hsplit horth hQ

  have hcross : ∀ Q ∈ P, ∀ Q' ∈ P, es Q' * cA D (es Q) = 0 := fun Q hQ Q' hQ' => by
    have h1 : cA D (es Q) * cA D e = cA D (es Q) := by rw [← map_mul, habs Q hQ]
    calc es Q' * cA D (es Q) = (es Q' * e) * (cA D e * cA D (es Q)) := by
          rw [habs Q' hQ', mul_comm (cA D e), h1]
      _ = es Q' * (e * cA D e) * cA D (es Q) := by ring
      _ = 0 := by rw [hec, mul_zero, zero_mul]
  intro Q Q' hvv
  by_contra hne
  have hne' : (Q : Formalism.L2.DIV.Pl D.host.E) ≠ Q' := fun h => hne (Subtype.ext h)
  obtain ⟨π, hπc⟩ := hπ Q
  obtain ⟨π', hπc'⟩ := hπ Q'
  have hs' : Formalism.L2.Theta.IsSplitIdem D (cA D (es Q')) := GlobalTheory.PlaceModelSum.isSplitIdem_cA (hsplit Q' Q'.2)
  obtain ⟨hid', hort', v', ε', ⟨α', rfl, hα1, hα0⟩, hsum'⟩ := hs'

  have hπ'1 : π' (cA D (es Q')) = 1 := by
    have := (hπc'.2.1 (1 - cA D (es Q'))).2 (by rw [mul_sub, mul_one, hid', sub_self])
    rwa [map_sub, map_one, sub_eq_zero, eq_comm] at this
  have hπ'0 : π' (cA D (cA D (es Q'))) = 0 := (hπc'.2.1 _).2 hort'
  have hw1 : evalV D.host.F (v Q') α' = 1 := by
    have := hπc'.2.2.1 (pairA D.host.F 0 α')
    rw [← hsum', map_add, hπ'1, hπ'0, add_zero] at this
    exact this.symm
  have hwv : v Q' = v' := by
    by_contra h
    rw [hα0 _ h] at hw1
    exact zero_ne_one hw1

  have hA : π (cA D (es Q')) = 0 := (hπc.2.1 _).2 (by
    rw [← map_mul, mul_eq_zero_of_ne hes Q.2 Q'.2 hne', map_zero])
  have hB : π (cA D (cA D (es Q'))) = 0 := (hπc.2.1 _).2 (by
    rw [cA_cA, mul_comm]; exact hcross Q Q.2 Q' Q'.2)
  have hC := hπc.2.2.1 (pairA D.host.F 0 α')
  rw [← hsum', map_add, hA, hB, add_zero] at hC
  have h0 : evalV D.host.F (v Q) α' = 0 := hC.symm
  rw [hvv.trans hwv, hα1] at h0
  exact one_ne_zero h0

end GlobalTheory.ChartPlaces
