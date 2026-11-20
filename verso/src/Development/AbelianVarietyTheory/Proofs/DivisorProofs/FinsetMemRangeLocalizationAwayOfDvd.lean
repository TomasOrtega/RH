import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `choose p hp using fun x : Localization.AtPrime 𝔭 => IsLocalization.mk'_surjective 𝔭.primeCompl x`. Set `sx : Localization.AtPrime 𝔭 → 𝔭.primeCompl` to `fun x => (p x).2`. Use `⟨((∏ x ∈ F, sx x : 𝔭.primeCompl) : R), (∏ x ∈ F, sx x).2, ?_⟩` and prove the remaining obligations. Introduce `c hc κ hκ x hx`. Establish `hdvd : ((sx x : 𝔭.primeCompl) : R) ∣ c`.

Use `dvd_trans ?_ hc` and prove the remaining obligations. Rewrite using `[Submonoid.coe_finset_prod]`. Conclude with `Finset.dvd_prod_of_mem (fun y => ((sx y : 𝔭.primeCompl) : R)) hx`. Take `⟨m, hm⟩` from `hdvd`. Establish `hκa : ∀ r : R, κ (algebraMap R (Localization.Away c) r) = algebraMap R (Localization.AtPrime 𝔭) r` using `fun r => by`.

Rewrite using `[← RingHom.comp_apply, hκ]`. Use `⟨algebraMap R _ (p x).1 * algebraMap R _ m * IsLocalization.Away.invSelf c, ?_⟩` and prove the remaining obligations. Establish `hinv : algebraMap R (Localization.AtPrime 𝔭) c * κ (IsLocalization.Away.invSelf (S` using `Localization.Away c) c) = 1 := by`. Rewrite using `[← hκa, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]`. Use `(?_ : _ = IsLocalization.mk' (Localization.AtPrime 𝔭) (p x).1 (p x).2).trans (hp x)` and prove the remaining obligations.

Rewrite using `[IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_mul, hκa, hκa]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = algebraMap R (Localization.AtPrime 𝔭) (p x).1 := by`.

Rewrite using `[← hm, hinv, mul_one]`.
-/
theorem finset_mem_range_of_away_dvd (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (F : Finset (Localization.AtPrime 𝔭)) :
    ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
        ∀ x ∈ F, x ∈ κ.range := by
  classical
  choose p hp using fun x : Localization.AtPrime 𝔭 =>
    IsLocalization.mk'_surjective 𝔭.primeCompl x
  let sx : Localization.AtPrime 𝔭 → 𝔭.primeCompl := fun x => (p x).2
  refine ⟨((∏ x ∈ F, sx x : 𝔭.primeCompl) : R), (∏ x ∈ F, sx x).2, ?_⟩
  intro c hc κ hκ x hx
  have hdvd : ((sx x : 𝔭.primeCompl) : R) ∣ c := by
    refine dvd_trans ?_ hc
    rw [Submonoid.coe_finset_prod]
    exact Finset.dvd_prod_of_mem (fun y => ((sx y : 𝔭.primeCompl) : R)) hx
  obtain ⟨m, hm⟩ := hdvd
  have hκa : ∀ r : R, κ (algebraMap R (Localization.Away c) r) =
      algebraMap R (Localization.AtPrime 𝔭) r := fun r => by
    rw [← RingHom.comp_apply, hκ]
  refine ⟨algebraMap R _ (p x).1 * algebraMap R _ m * IsLocalization.Away.invSelf c, ?_⟩
  have hinv : algebraMap R (Localization.AtPrime 𝔭) c *
      κ (IsLocalization.Away.invSelf (S := Localization.Away c) c) = 1 := by
    rw [← hκa, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  refine (?_ : _ = IsLocalization.mk' (Localization.AtPrime 𝔭) (p x).1 (p x).2).trans (hp x)
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_mul, hκa, hκa]
  calc algebraMap R (Localization.AtPrime 𝔭) (p x).1 * algebraMap R _ m *
        κ (IsLocalization.Away.invSelf c) * algebraMap R _ ((p x).2 : R)
      = algebraMap R (Localization.AtPrime 𝔭) (p x).1 *
        (algebraMap R _ (((p x).2 : R) * m) * κ (IsLocalization.Away.invSelf c)) := by
        rw [map_mul]; ring
    _ = algebraMap R (Localization.AtPrime 𝔭) (p x).1 := by
        rw [← hm, hinv, mul_one]

end GlobalTheory
