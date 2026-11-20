import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreBis

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.OrbitCoverLemmas

variable {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]

omit [Countable G] [MeasurableSpace Y] in

/- English proof (translation)
Simplify using `only [smul_smul]`. Conclude with `(Equiv.mulRight g).tsum_eq (fun h => u (h • y))`.
-/
theorem orbit_tsum_smul (u : Y → ℝ) (g : G) (y : Y) :
    ∑' h : G, u (h • g • y) = ∑' h : G, u (h • y) := by
  simp only [smul_smul]
  exact (Equiv.mulRight g).tsum_eq (fun h => u (h • y))

/- English proof (translation)
Establish `hsE : (fun y => ∑' g : G, u (g • y)) = fun y => (∑' g : G, ENNReal.ofReal (u (g • y))).toReal`. Use function extensionality and compare the values at `y`. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun g => h0 _) (hs y), ENNReal.toReal_ofReal]`. Conclude with `tsum_nonneg fun g => h0 _`. Establish `hsm : Measurable fun y => ∑' g : G, u (g • y)`.

Rewrite using `[hsE]`. Conclude with `(Measurable.ennreal_tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal`. Establish `hspos : ∀ y, 0 < ∑' g : G, u (g • y)`. Introduce `y`. Take `⟨g, hg⟩` from `hpos y`.

Conclude with `lt_of_lt_of_le hg ((hs y).le_tsum g fun h _ => h0 _)`. Use `⟨fun y => u y / ∑' g : G, u (g • y), ⟨hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le, fun y => ?_⟩⟩` and prove the remaining obligations. Establish `: (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) = fun g => u (g • y) / ∑' h : G, u (h • y)`. Use function extensionality and compare the values at `g`. Rewrite using `[orbit_tsum_smul]`.

Use `show HasSum (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) 1`. Rewrite using `[this, ← div_self (hspos y).ne']`. Conclude with `(hs y).hasSum.div_const _`.
-/
theorem exists_cut (hm : ∀ g : G, Measurable fun y : Y => g • y) (u : Y → ℝ) (hu : Measurable u)
    (h0 : ∀ y, 0 ≤ u y) (hpos : ∀ y, ∃ g : G, 0 < u (g • y))
    (hs : ∀ y, Summable fun g : G => u (g • y)) : ∃ b : Y → ℝ, IsCut G b := by
  have hsE : (fun y => ∑' g : G, u (g • y)) =
      fun y => (∑' g : G, ENNReal.ofReal (u (g • y))).toReal := by
    funext y
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun g => h0 _) (hs y), ENNReal.toReal_ofReal]
    exact tsum_nonneg fun g => h0 _
  have hsm : Measurable fun y => ∑' g : G, u (g • y) := by
    rw [hsE]
    exact (Measurable.ennreal_tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal
  have hspos : ∀ y, 0 < ∑' g : G, u (g • y) := by
    intro y
    obtain ⟨g, hg⟩ := hpos y
    exact lt_of_lt_of_le hg ((hs y).le_tsum g fun h _ => h0 _)
  refine ⟨fun y => u y / ∑' g : G, u (g • y),
    ⟨hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le, fun y => ?_⟩⟩
  have : (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) =
      fun g => u (g • y) / ∑' h : G, u (h • y) := by
    funext g; rw [orbit_tsum_smul]
  show HasSum (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) 1
  rw [this, ← div_self (hspos y).ne']
  exact (hs y).hasSum.div_const _

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf46.cover μ hP b hb S hS hc`.
-/
theorem cover (μ : Measure Y) (hP : Pres G μ) (b : Y → ℝ) (hb : IsCut G b) (S : Set Y)
    (hS : MeasurableSet S) (hc : ∀ y : Y, ∃ g : G, g • y ∈ S) :
    ∫⁻ y, ENNReal.ofReal (b y) ∂μ ≤ μ S :=
  _root_.UpperTheory.Reformulated.B.Qf46.cover μ hP b hb S hS hc

end UpperTheory.Esk.OrbitCoverLemmas

/- English proof (translation)
Introduce `G Y _ _ _ _`. Conclude with `⟨fun hm u hu h0 hpos hs => UpperTheory.Esk.OrbitCoverLemmas.exists_cut hm u hu h0 hpos hs, fun μ hP b hb S hS hc => UpperTheory.Esk.OrbitCoverLemmas.cover μ hP b hb S hS hc⟩`.
-/
theorem UpperTheory.Esk.orbit_cover_proof : UpperTheory.Esk.C2 := by
  intro G Y _ _ _ _
  exact ⟨fun hm u hu h0 hpos hs => UpperTheory.Esk.OrbitCoverLemmas.exists_cut hm u hu h0 hpos hs,
    fun μ hP b hb S hS hc => UpperTheory.Esk.OrbitCoverLemmas.cover μ hP b hb S hS hc⟩
