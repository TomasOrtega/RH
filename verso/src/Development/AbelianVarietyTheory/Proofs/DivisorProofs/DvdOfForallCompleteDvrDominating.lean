import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

/- English proof (translation)
Break down `ValuationRing.dvd_total a b with hab | hba` into its components or cases. Conclude with `hab`. Take `⟨c, hc⟩` from `hba`. Take `⟨d, hd⟩` from `h`. Establish `hb : b ≠ 0` using `by rintro rfl; exact ha (by simpa using hc)`.

Establish `hψb : ψ b ≠ 0` using `fun e => hb (hψ (e.trans (map_zero ψ).symm))`. Establish `h1 : ψ b * (ψ c * d) = ψ b * 1`. Rewrite using `[mul_one]`. Use `nth_rewrite 2 [hd]`. Rewrite using `[hc, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcu : IsUnit (ψ c)` using `IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hψb h1)`. Establish `hc' : IsUnit c` using `isUnit_of_map_unit ψ c hcu`. Conclude with `(Units.dvd_mul_right (u := hc'.unit)).mp (by rw [IsUnit.unit_spec, ← hc])`.
-/
theorem dvd_of_map_dvd_of_valuationRing {V T : Type} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing T] [IsDomain T] (ψ : V →+* T) (hψ : Function.Injective ψ) [IsLocalHom ψ] {a b : V}
    (ha : a ≠ 0) (h : ψ a ∣ ψ b) : a ∣ b := by
  rcases ValuationRing.dvd_total a b with hab | hba
  · exact hab
  · obtain ⟨c, hc⟩ := hba
    obtain ⟨d, hd⟩ := h
    have hb : b ≠ 0 := by rintro rfl; exact ha (by simpa using hc)
    have hψb : ψ b ≠ 0 := fun e => hb (hψ (e.trans (map_zero ψ).symm))
    have h1 : ψ b * (ψ c * d) = ψ b * 1 := by
      rw [mul_one]; nth_rewrite 2 [hd]; rw [hc, map_mul]; ring
    have hcu : IsUnit (ψ c) := IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hψb h1)
    have hc' : IsUnit c := isUnit_of_map_unit ψ c hcu
    exact (Units.dvd_mul_right (u := hc'.unit)).mp (by rw [IsUnit.unit_spec, ← hc])

/- English proof (translation)
Introduce `R _ _ _ _ _ _ f g hg H`. Set `K` to `FractionRing R`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hg' : algebraMap R K g ≠ 0` using `fun e => hg (hinj (e.trans (map_zero _).symm))`. Assume the negation of the conclusion as `hnd`.

Establish `hx : ¬ ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) → (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) → algebraMap R K f / algebraMap R K g ∈ V`. Introduce `hall`. Take `⟨r, hr⟩` from `GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring hall`. Apply `hnd` to reduce the goal to its premises. Use `⟨r, hinj ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hr, mul_div_cancel₀ _ hg']`. Use `push_neg at hx`. Take `⟨V, hV, h1, h2, hxV⟩` from `hx`. Establish `hdom : LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring` using `(GlobalTheory.localSubring_range_le_valuationSubring_iff _ _).mpr ⟨h1, h2⟩`. Take `⟨-, hc, -, h, hρi, hρl⟩` from `(GlobalTheory.discreteValuationRing_dominating_noetherian_local R K K).2.2 V hdom`.

Establish `hd` using `H (AdicCompletion (maximalIdeal V) V) hc _ hρi hρl`. Set `a : V` to `⟨algebraMap R K g, h g⟩`. Set `b : V` to `⟨algebraMap R K f, h f⟩`. Establish `ha : a ≠ 0` using `fun e => hg' (congrArg Subtype.val e)`. Take `⟨c, hcab⟩` from `dvd_of_map_dvd_of_valuationRing (algebraMap V (AdicCompletion (maximalIdeal V) V)) (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V) ha hd`.

Apply `hxV` to reduce the goal to its premises. Establish `: algebraMap R K f = algebraMap R K g * (c : K)` using `congrArg Subtype.val hcab`. Rewrite using `[this, mul_div_cancel_left₀ _ hg']`. Conclude with `c.2`.
-/
theorem dvd_of_forall_complete_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] (f g : R), g ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
      ∀ ρ : R →+* V, Function.Injective ρ → IsLocalHom ρ → ρ g ∣ ρ f) → g ∣ f := by
  intro R _ _ _ _ _ _ f g hg H
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hg' : algebraMap R K g ≠ 0 := fun e => hg (hinj (e.trans (map_zero _).symm))
  by_contra hnd
  have hx : ¬ ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) →
      (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) →
      algebraMap R K f / algebraMap R K g ∈ V := by
    intro hall
    obtain ⟨r, hr⟩ := GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring hall
    apply hnd
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hg']
  push_neg at hx
  obtain ⟨V, hV, h1, h2, hxV⟩ := hx
  have hdom : LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring :=
    (GlobalTheory.localSubring_range_le_valuationSubring_iff _ _).mpr ⟨h1, h2⟩
  obtain ⟨-, hc, -, h, hρi, hρl⟩ :=
    (GlobalTheory.discreteValuationRing_dominating_noetherian_local R K K).2.2 V hdom
  have hd := H (AdicCompletion (maximalIdeal V) V) hc _ hρi hρl
  let a : V := ⟨algebraMap R K g, h g⟩
  let b : V := ⟨algebraMap R K f, h f⟩
  have ha : a ≠ 0 := fun e => hg' (congrArg Subtype.val e)
  obtain ⟨c, hcab⟩ := dvd_of_map_dvd_of_valuationRing (algebraMap V (AdicCompletion (maximalIdeal V) V))
    (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V) ha hd
  apply hxV
  have : algebraMap R K f = algebraMap R K g * (c : K) := congrArg Subtype.val hcab
  rw [this, mul_div_cancel_left₀ _ hg']
  exact c.2

end GlobalTheory.Poinc
