import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefShiftPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatQCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEulerHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolyLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D a _ hV _ hN`. Set `_ : LinearOrder K` to `LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective`. Set `_ : ∀ k, LinearOrder (ι k)` to `fun k => LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective`. Take `⟨hQ, hdim⟩` from `ShiftDegreePolynomial.genericFibre hV`. Use `set Q := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hQdef`.

Take `⟨m, hm⟩` from `hF K ι (mCoordIdeal y) D a hV hN`. Take `⟨p, a₀, hpdeg, hp⟩` from `MultigradedHilbertPolynomial.proof EventualPolynomial.proof ℚ K ι Q D hQ hdim`. Take `⟨r, hrdeg, hrcoef, hr⟩` from `hL K D (hilbFn Q) p a₀ a (fun _ => (m : ℤ)) hpdeg hp`. Use `⟨m, r, hrdeg, ?_, Eventually.of_forall fun n => ?_⟩` and prove the remaining obligations. Establish `hH : ∀ i j : DecidableEq K, @hilbFn K i ι ℚ _ Q = @hilbFn K j ι ℚ _ Q` using `fun i j => by`.

Rewrite using `[Subsingleton.elim i j]`. Establish `hg : genDeg (mCoordIdeal y) D a = eventualValue (mixedDiff (fun _ : Fin D => a) (hilbFn Q))` using `congrArg (fun h => eventualValue (mixedDiff (fun _ : Fin D => a) h)) (hH _ _)`. Rewrite using `[hrcoef, hg]`. Take `⟨e⟩` from `hC K ι Ω y (D + 1) ((n : ℤ) • a + fun _ => (m : ℤ)) hV`. Rewrite using `[e.finrank_eq, ← hr n, ← hE ℚ K ι Q p a₀ hQ hp _ (hm n)]`.

Use `norm_cast`.
-/
theorem NefShiftPolynomial.proof (hF : FujitaGeneric.Statement) (hC : ChartLatQCech.Statement)
    (hE : EulerHilbert.Statement) (hL : EventualPolyLine.Statement) : NefShiftPolynomial.Statement := by
  intro K _ ι _ Ω _ _ y D a _ hV _ hN
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain ⟨hQ, hdim⟩ := ShiftDegreePolynomial.genericFibre hV
  set Q := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hQdef
  obtain ⟨m, hm⟩ := hF K ι (mCoordIdeal y) D a hV hN
  obtain ⟨p, a₀, hpdeg, hp⟩ :=
    MultigradedHilbertPolynomial.proof EventualPolynomial.proof ℚ K ι Q D hQ hdim
  obtain ⟨r, hrdeg, hrcoef, hr⟩ := hL K D (hilbFn Q) p a₀ a (fun _ => (m : ℤ)) hpdeg hp
  refine ⟨m, r, hrdeg, ?_, Eventually.of_forall fun n => ?_⟩
  · have hH : ∀ i j : DecidableEq K, @hilbFn K i ι ℚ _ Q = @hilbFn K j ι ℚ _ Q := fun i j => by
      rw [Subsingleton.elim i j]
    have hg : genDeg (mCoordIdeal y) D a = eventualValue (mixedDiff (fun _ : Fin D => a) (hilbFn Q)) :=
      congrArg (fun h => eventualValue (mixedDiff (fun _ : Fin D => a) h)) (hH _ _)
    rw [hrcoef, hg]
  · obtain ⟨e⟩ := hC K ι Ω y (D + 1) ((n : ℤ) • a + fun _ => (m : ℤ)) hV
    rw [e.finrank_eq, ← hr n, ← hE ℚ K ι Q p a₀ hQ hp _ (hm n)]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
