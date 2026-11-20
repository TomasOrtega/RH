import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocAwaySpec
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Classical in

/- English proof (translation)
Introduce `R _ Φ _ φ S hrep`. Use `choose f g hg hfg using hrep`. Establish `hE0 : IsUnit (φ (∏ c ∈ S, g c))`. Rewrite using `[map_prod]`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit`.

Use `⟨∏ c ∈ S, g c, hE0, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc set E := ∏ d ∈ S, g d with hEdef`. Establish `hE : IsUnit (φ E)`. Rewrite using `[hEdef, map_prod]`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit`.

Establish `hunitE : IsUnit (algebraMap R (Localization.Away E) E)` using `IsLocalization.Away.algebraMap_isUnit E`. Establish `hu : IsUnit (algebraMap R (Localization.Away E) (g c))` using `isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hc)) hunitE`. Use `⟨algebraMap R (Localization.Away E) (f c) * ↑hu.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit = φ (g c)`. Rewrite using `[IsUnit.unit_spec, IsLocalization.Away.lift_eq]`.

Establish `h2 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit⁻¹ = (φ (g c))⁻¹`. Rewrite using `[← h1, ← map_units_inv]`. Rewrite using `[map_mul, IsLocalization.Away.lift_eq, h2, ← div_eq_mul_inv]`. Conclude with `(hfg c).symm`. Introduce `B _ ψ hψ hker z hz`.

Rewrite `hz`, the goal using `[RingHom.mem_ker]`. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers (∏ c ∈ S, g c)) z`. Establish `hsφ` using `congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hE0 : Localization.Away (∏ c ∈ S, g c) →+* Φ) hs`. Simplify using `only [map_mul, IsLocalization.Away.lift_eq, hz, zero_mul] at hsφ`. Establish `ha : ψ a = 0` using `hker (RingHom.mem_ker.mpr hsφ.symm)`.

Establish `hsψ` using `congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hψ : Localization.Away (∏ c ∈ S, g c) →+* B) hs`. Simplify using `only [map_mul, IsLocalization.Away.lift_eq, ha] at hsψ`. Take `⟨n, hn⟩` from `Submonoid.mem_powers_iff _ _ |>.mp s.2`. Establish `hsu : IsUnit (ψ (s : R))`. Rewrite using `[← hn, map_pow]`.

Conclude with `hψ.pow n`. Conclude with `(hsu.mul_left_eq_zero).mp hsψ`.
-/
theorem LocAwaySpec.proof : LocAwaySpec.Statement := by
  intro R _ Φ _ φ S hrep
  choose f g hg hfg using hrep
  have hE0 : IsUnit (φ (∏ c ∈ S, g c)) := by
    rw [map_prod]
    exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
  refine ⟨∏ c ∈ S, g c, hE0, ?_, ?_⟩
  · intro c hc
    set E := ∏ d ∈ S, g d with hEdef
    have hE : IsUnit (φ E) := by
      rw [hEdef, map_prod]
      exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
    have hunitE : IsUnit (algebraMap R (Localization.Away E) E) :=
      IsLocalization.Away.algebraMap_isUnit E
    have hu : IsUnit (algebraMap R (Localization.Away E) (g c)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hc)) hunitE
    refine ⟨algebraMap R (Localization.Away E) (f c) * ↑hu.unit⁻¹, ?_⟩
    have h1 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit = φ (g c) := by
      rw [IsUnit.unit_spec, IsLocalization.Away.lift_eq]
    have h2 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit⁻¹ = (φ (g c))⁻¹ := by
      rw [← h1, ← map_units_inv]
    rw [map_mul, IsLocalization.Away.lift_eq, h2, ← div_eq_mul_inv]
    exact (hfg c).symm
  · intro B _ ψ hψ hker z hz
    rw [RingHom.mem_ker] at hz ⊢
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (∏ c ∈ S, g c)) z
    have hsφ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hE0 : Localization.Away (∏ c ∈ S, g c) →+* Φ) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, hz, zero_mul] at hsφ
    have ha : ψ a = 0 := hker (RingHom.mem_ker.mpr hsφ.symm)
    have hsψ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hψ :
      Localization.Away (∏ c ∈ S, g c) →+* B) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, ha] at hsψ
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hsu : IsUnit (ψ (s : R)) := by
      rw [← hn, map_pow]
      exact hψ.pow n
    exact (hsu.mul_left_eq_zero).mp hsψ

end GroundTheory.Heights₂.Heights.Inter
