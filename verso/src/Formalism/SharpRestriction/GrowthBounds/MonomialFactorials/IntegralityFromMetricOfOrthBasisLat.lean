import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOrthogonalBasis
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CommCondition

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestWinE (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestWin C0 CE1 CE2 X CM

/- English proof (translation)
Unfold `RestWinE at h`. Unfold `SymmetryWindowOnAdmissible`. Unfold `Formalism.MainNotions.flipOneThree.TransportedAlt at h ⊢`. Introduce `Cc hCc`. Take `⟨T0, hT0, h0⟩` from `h Cc hCc`.

Use `⟨T0, hT0, fun C0 hC0 => ?_⟩` and prove the remaining obligations. Take `⟨T1, hT1, h1⟩` from `h0 C0 hC0`. Use `⟨T1, hT1, fun CE1 CE2 hE1 hE2 => ?_⟩` and prove the remaining obligations. Take `⟨T2, hT2, h2⟩` from `h1 CE1 CE2 hE1 hE2`. Use `⟨T2, hT2, fun CYb Cde Ck CD Cb ha hb hc hd he => ?_⟩` and prove the remaining obligations.

Introduce `Ckap Cs CM hCM X hX hHI`. Conclude with `⟨symmCondition C0 CE1 CE2 X, h2 CYb Cde Ck CD Cb ha hb hc hd he Ckap Cs CM hCM X hX hHI⟩`.
-/
theorem symmetric_dims_of_windows (D : Formalism.BasicNotions.D7) (h : RestWinE D) : SymmetryWindowOnAdmissible D := by
  unfold RestWinE at h
  unfold SymmetryWindowOnAdmissible
  unfold Formalism.MainNotions.flipOneThree.TransportedAlt at h ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 hE1 hE2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 hE1 hE2
  refine ⟨T2, hT2, fun CYb Cde Ck CD Cb ha hb hc hd he => ?_⟩
  intro Ckap Cs CM hCM X hX hHI
  exact ⟨symmCondition C0 CE1 CE2 X, h2 CYb Cde Ck CD Cb ha hb hc hd he Ckap Cs CM hCM X hX hHI⟩

/- English proof (translation)
The claim follows from `closed_of_orthogonal_basis D hB hG (symmetric_dims_of_windows D h)`.
-/
theorem integralityFromMetric_of_orthBasisLat (D : Formalism.BasicNotions.D7) (hB : OrthBasisLat) (hG : GoodLeSmall) (h : RestWinE D) :
    IntegralityFromMetricForLargeConstants D :=
  closed_of_orthogonal_basis D hB hG (symmetric_dims_of_windows D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
