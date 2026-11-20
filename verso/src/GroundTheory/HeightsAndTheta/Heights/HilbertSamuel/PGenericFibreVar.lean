import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D hP`. Take `⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩` from `hP`. Establish `: (mCoordIdeal y).IsPrime` using `hPp`. Establish `hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ mCoordIdeal y → m = 0`. Introduce `m hm`.

Establish `h1 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)` using `hm`. Rewrite `h1` using `[show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot]`. Conclude with `h1`. Take `⟨hqp, hcomap, hform⟩` from `ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hchar`. Establish `hq : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) = KH.genIdeal y` using `rfl`.

Rewrite using `[← hq]`. Use `⟨⟨hqp, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨b, hb⟩` from `hS f hf`.

Conclude with `⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩`. Use `show (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = _`. Rewrite using `[hPS, Ideal.map_span]`. Introduce `k`. Take `⟨i, hi⟩` from `hrel k`.

Use `⟨i, fun hX => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomap, Ideal.mem_comap, map_X]`. Conclude with `hX`. Use `GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + Fintype.card K) _ ?_` and prove the remaining obligations. Rewrite using `[hform, hdim, show D + 1 + Fintype.card K = (D + Fintype.card K) + 1 by omega]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem GenericFibreVar.proof : GenericFibreVar.Statement := by
  intro K _ ι _ Ω _ y D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (mCoordIdeal y).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ mCoordIdeal y → m = 0 := by
    intro m hm
    have h1 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) = KH.genIdeal y := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq
      (D + Fintype.card K) _ ?_
    rw [hform, hdim, show D + 1 + Fintype.card K = (D + Fintype.card K) + 1 by omega]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
