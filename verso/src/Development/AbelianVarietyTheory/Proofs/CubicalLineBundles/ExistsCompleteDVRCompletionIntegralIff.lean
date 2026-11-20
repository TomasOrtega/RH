import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Unfold `valV`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Conclude with `(IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one r`. Introduce `h`.

Take `⟨a, ha⟩` from `IsDiscreteValuationRing.exists_lift_of_le_one h`. Conclude with `⟨a, ha⟩`.
-/
private lemma mem_range_algebraMap_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  unfold valV
  constructor
  · rintro ⟨r, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one r
  · intro h
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
    exact ⟨a, ha⟩

/- English proof (translation)
Use `conv_lhs => rw [← WithZero.exp_log hx, ← WithZero.exp_zero]`. Conclude with `WithZero.exp_le_exp`.
-/
private lemma withZero_le_one_iff_log_nonpos {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : x ≤ 1 ↔ WithZero.log x ≤ 0 := by
  conv_lhs => rw [← WithZero.exp_log hx, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp

/- English proof (translation)
Introduce `K _ _ p`. Take `⟨T, k, e, hO, hfin⟩` from `locFld K K (RingHom.id K) p`. Unfold `OverLa vV vLa at hO`. Take `⟨he, hv⟩` from `hO`. Simplify using `only [RingHom.comp_id] at hv`.

Use `⟨T, k, hfin, fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Rewrite using `[map_zero, map_zero]`. Conclude with `⟨fun _ => zero_le, fun _ => ⟨0, map_zero _⟩⟩`.

Establish `hky : k y ≠ 0` using `(map_ne_zero k).2 hy`. Establish `ha : valV T.V (k y) ≠ 0`. Unfold `valV`. Conclude with `(Valuation.ne_zero_iff _).2 hky`. Establish `hb : p.valuation K y ≠ 0` using `(Valuation.ne_zero_iff _).2 hy`.

Rewrite using `[mem_range_algebraMap_iff_valV_le_one, withZero_le_one_iff_log_nonpos ha, withZero_le_one_iff_log_nonpos hb]`. Establish `h` using `hv y`. Establish `he' : (0 : ℤ) < e` using `by exact_mod_cast he`. Apply the tactic sequence `constructor <;> intro h' <;> nlinarith`.
-/
theorem exists_cdvr_completion_integral_iff :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)),
      ∃ (T : CDVR) (iK : K →+* T.Fr), T.FinRes ∧
        ∀ y : K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation K y ≤ 1 := by
  intro K _ _ p

  obtain ⟨T, k, e, hO, hfin⟩ := locFld K K (RingHom.id K) p
  unfold OverLa vV vLa at hO
  obtain ⟨he, hv⟩ := hO
  simp only [RingHom.comp_id] at hv
  refine ⟨T, k, hfin, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero]
    exact ⟨fun _ => zero_le, fun _ => ⟨0, map_zero _⟩⟩
  · have hky : k y ≠ 0 := (map_ne_zero k).2 hy
    have ha : valV T.V (k y) ≠ 0 := by
      unfold valV
      exact (Valuation.ne_zero_iff _).2 hky
    have hb : p.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy

    rw [mem_range_algebraMap_iff_valV_le_one, withZero_le_one_iff_log_nonpos ha, withZero_le_one_iff_log_nonpos hb]
    have h := hv y
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    constructor <;> intro h' <;> nlinarith

end GlobalTheory
