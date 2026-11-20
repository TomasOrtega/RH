import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

/- English proof (translation)
Establish `h1 : ((p : ℕ) : WW p) ≠ 0` using `WittVector.p_nonzero p (kb p)`. Establish `h2 : algebraMap (WW p) (K0 p) ((p : ℕ) : WW p) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).2 h1`. Simplify using `using h2`.
-/
theorem prime_cast_ne_zero : ((p : ℕ) : K0 p) ≠ 0 := by
  have h1 : ((p : ℕ) : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 : algebraMap (WW p) (K0 p) ((p : ℕ) : WW p) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).2 h1
  simpa using h2

/- English proof (translation)
Introduce `h`. Establish `h1 : algebraMap X.G.Kf Y.Kc ((p : ℕ) : X.G.Kf) = 0` using `by rw [h, map_zero]`. Establish `h2 : algebraMap (K0 p) Y.Kc ((p : ℕ) : K0 p) = 0`. Rewrite `h1`, the goal using `[map_natCast]`. Conclude with `h1`.

Conclude with `prime_cast_ne_zero ((map_eq_zero _).1 h2)`.
-/
theorem pKf_ne (Y : Pend X) : ((p : ℕ) : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap X.G.Kf Y.Kc ((p : ℕ) : X.G.Kf) = 0 := by rw [h, map_zero]
  have h2 : algebraMap (K0 p) Y.Kc ((p : ℕ) : K0 p) = 0 := by
    rw [map_natCast] at h1 ⊢
    exact h1
  exact prime_cast_ne_zero ((map_eq_zero _).1 h2)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible ha0 X.unif`. Take `⟨u, hu⟩` from `hn`.

Establish `h1 : algebraMap X.G.O X.G.Kf (X.vp ^ n) = 0` using `by rw [← hu, map_mul, ha, zero_mul]`. Establish `h2 : algebraMap X.G.O X.G.Kf X.vp = 0`. Rewrite `h1` using `[map_pow]`. Assume the negation of the conclusion as `h`. Conclude with `pow_ne_zero n h h1`.

Take `⟨u', hu'⟩` from `X.eO_spec`. Establish `h3 : algebraMap X.G.O X.G.Kf ((p : X.G.O) * u') = 0`. Rewrite using `[hu', map_pow, h2, zero_pow (by omega)]`. Rewrite `h3` using `[map_mul, map_natCast]`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases.

Conclude with `pKf_ne Y h`. Establish `: algebraMap X.G.O X.G.Kf ((u' : X.G.O) * ((u'⁻¹ : X.G.Oˣ) : X.G.O)) = 0` using `by rw [map_mul, h, zero_mul]`. Simplify using `at this`.
-/
theorem algebraMap_inj (Y : Pend X) (he : 0 < X.eO) : Function.Injective (algebraMap X.G.O X.G.Kf) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 X.unif
  obtain ⟨u, hu⟩ := hn

  have h1 : algebraMap X.G.O X.G.Kf (X.vp ^ n) = 0 := by rw [← hu, map_mul, ha, zero_mul]
  have h2 : algebraMap X.G.O X.G.Kf X.vp = 0 := by
    rw [map_pow] at h1
    by_contra h
    exact pow_ne_zero n h h1
  obtain ⟨u', hu'⟩ := X.eO_spec
  have h3 : algebraMap X.G.O X.G.Kf ((p : X.G.O) * u') = 0 := by
    rw [hu', map_pow, h2, zero_pow (by omega)]
  rw [map_mul, map_natCast] at h3
  rcases mul_eq_zero.1 h3 with h | h
  · exact pKf_ne Y h
  · have : algebraMap X.G.O X.G.Kf ((u' : X.G.O) * ((u'⁻¹ : X.G.Oˣ) : X.G.O)) = 0 := by rw [map_mul, h, zero_mul]
    simp at this

/- English proof (translation)
Establish `: FaithfulSMul X.G.O X.G.Kf` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_inj Y he)`. Apply `IsFractionRing.of_field` to reduce the goal to its premises. Introduce `z`. Break down `Y.Oc_val (algebraMap X.G.Kf Y.Kc z) with h | h` into its components or cases. Take `⟨a, ha⟩` from `(mem_intK X).1 ((Y.Oc_K z).1 h)`.

Conclude with `⟨a, 1, by simp [ha]⟩`. Rewrite `h` using `[← map_inv₀]`. Take `⟨a, ha⟩` from `(mem_intK X).1 ((Y.Oc_K z⁻¹).1 h)`. Conclude with `⟨1, a, by simp [ha]⟩`.
-/
theorem isFractionRing_of_pos_eO (Y : Pend X) (he : 0 < X.eO) : IsFractionRing X.G.O X.G.Kf := by
  have : FaithfulSMul X.G.O X.G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_inj Y he)
  apply IsFractionRing.of_field
  intro z
  rcases Y.Oc_val (algebraMap X.G.Kf Y.Kc z) with h | h
  · obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z).1 h)
    exact ⟨a, 1, by simp [ha]⟩
  · rw [← map_inv₀] at h
    obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z⁻¹).1 h)
    exact ⟨1, a, by simp [ha]⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
