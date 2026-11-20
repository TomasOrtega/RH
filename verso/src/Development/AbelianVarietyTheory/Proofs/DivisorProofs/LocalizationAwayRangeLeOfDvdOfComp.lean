import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hu : IsUnit (algebraMap R (Localization.Away c') c)` using `isUnit_of_dvd_unit (map_dvd _ hcc) (IsLocalization.Away.algebraMap_isUnit c')`. Set `φ : Localization.Away c →+* Localization.Away c'` to `IsLocalization.Away.lift c hu`. Establish `hφ : (κ'.comp φ) = κ`. Apply `IsLocalization.ringHom_ext (Submonoid.powers c)` to reduce the goal to its premises. Rewrite using `[hκ, RingHom.comp_assoc]`.

Establish `: φ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away c')` using `IsLocalization.Away.lift_comp c hu`. Rewrite using `[this, hκ']`. Introduce and unpack `y ⟨x, rfl⟩`. Conclude with `⟨φ x, by rw [← hφ]; rfl⟩`.
-/
theorem away_range_le_of_dvd (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R)
    (hcc : c ∣ c') (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P)
    (hκ : κ.comp (algebraMap R (Localization.Away c)) = g)
    (hκ' : κ'.comp (algebraMap R (Localization.Away c')) = g) : κ.range ≤ κ'.range := by
  have hu : IsUnit (algebraMap R (Localization.Away c') c) :=
    isUnit_of_dvd_unit (map_dvd _ hcc) (IsLocalization.Away.algebraMap_isUnit c')
  let φ : Localization.Away c →+* Localization.Away c' := IsLocalization.Away.lift c hu
  have hφ : (κ'.comp φ) = κ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [hκ, RingHom.comp_assoc]
    have : φ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away c') :=
      IsLocalization.Away.lift_comp c hu
    rw [this, hκ']
  rintro y ⟨x, rfl⟩
  exact ⟨φ x, by rw [← hφ]; rfl⟩

/- English proof (translation)
Introduce `R _ P _ g c c' h κ κ' hκ hκ'` and use `away_range_le_of_dvd R P g c c' h κ κ' hκ hκ'`.
-/
theorem away_range_le_of_dvd' : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range :=
  fun R _ P _ g c c' h κ κ' hκ hκ' => away_range_le_of_dvd R P g c c' h κ κ' hκ hκ'

end GlobalTheory
