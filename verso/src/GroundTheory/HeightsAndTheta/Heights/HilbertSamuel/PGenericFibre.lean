import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `Ω _ _ κ _ x D hP`. Take `⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩` from `hP`. Establish `: (coordIdeal ℤ x).IsPrime` using `hPp`. Establish `hchar : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0`. Introduce `m hm`.

Establish `h1 : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ))` using `hm`. Rewrite `h1` using `[show (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) = ⊥ from hhor, Ideal.mem_bot]`. Conclude with `h1`. Take `⟨hqp, hcomap, hform⟩` from `ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hchar`. Establish `hq : ReciprocityTheory.AnForm.R.extQ (coordIdeal ℤ x) = (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))` using `rfl`.

Rewrite using `[← hq]`. Use `⟨⟨hqp, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]`. Use `⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Take `⟨b, hb⟩` from `hS f hf`. Conclude with `⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩`. Rewrite using `[hq, hPS, Ideal.map_span]`. Introduce `k`. Take `⟨i, hi⟩` from `hrel k`.

Use `⟨i, fun hX => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomap, Ideal.mem_comap, map_X]`. Conclude with `hX`. Rewrite `hform` using `[hdim]`. Simplify using `only [Fintype.card_unit] at hform`.

Use `GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + 1) _ ?_` and prove the remaining obligations. Rewrite using `[hform]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem GenericFibre.proof : GenericFibre.Statement := by
  intro Ω _ _ κ _ x D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (coordIdeal ℤ x).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0 := by
    intro m hm
    have h1 : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) := hm
    rw [show (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (coordIdeal ℤ x) =
      (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    simp only [Fintype.card_unit] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + 1) _ ?_
    rw [hform]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
