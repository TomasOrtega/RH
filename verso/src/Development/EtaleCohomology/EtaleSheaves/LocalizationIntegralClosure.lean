import Development.EtaleCohomology.EtaleSheaves.HensCut

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LocalizationIntegralClosure

/- English proof (translation)
Introduce `p hp hd`. Use `set L := Localization M`. Take `⟨s, hs⟩` from `IsLocalization.exist_integer_multiples_of_finset (R := B) M ((Finset.range (p.natDegree + 1)).image p.coeff) (S := L)`. Use `set t : L := algebraMap B L (s : B) with ht`. Establish `hlift : scaleRoots p t ∈ lifts (algebraMap B L)`.

Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `i`. Rewrite using `[coeff_scaleRoots]`. Break down `lt_or_ge i p.natDegree with hi | hi` into its components or cases. Take `⟨c, hc⟩` from `hs (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)`.

Take `⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1` from `⟨p.natDegree - i - 1, by omega⟩`. Use `⟨c * (s : B) ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, map_mul, map_pow, hc, pow_succ, Algebra.smul_def, ← ht]`. Expand and normalize the polynomial expressions, which then agree. Break down `eq_or_lt_of_le hi with h | h` into its components or cases.

Substitute `h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩` using the available equality. Rewrite using `[coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩`. Take `⟨q, hq, hqd, hqm⟩` from `lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).2 hp)`. Take `⟨b, hb⟩` from `hB q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)`. Take `⟨u, hu⟩` from `IsLocalization.map_units L s`.

Use `⟨algebraMap B L b * ((u⁻¹ : Lˣ) : L), ?_⟩` and prove the remaining obligations. Establish `h1 : (scaleRoots p t).eval (algebraMap B L b) = 0`. Rewrite using `[← hq, eval_map, eval₂_at_apply, hb, map_zero]`. Establish `h2 : (scaleRoots p t).eval (t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L))) = t ^ p.natDegree * p.eval (algebraMap B L b * ((u⁻¹ : Lˣ) : L))` using `scaleRoots_eval₂_mul (p := p) (RingHom.id L) (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) t`. Establish `h3 : t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) = algebraMap B L b`.

Rewrite using `[ht, ← hu, mul_comm (algebraMap B L b), ← mul_assoc, Units.mul_inv, one_mul]`. Rewrite `h2` using `[h3, h1]`. Establish `hunit : IsUnit (t ^ p.natDegree)` using `(hu ▸ u.isUnit).pow _`. Conclude with `(hunit.mul_right_eq_zero).1 h2.symm`.
-/
theorem aic_loc (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B) (hB : AIC B) :
    AIC (Localization M) := by
  classical
  intro p hp hd
  set L := Localization M
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (R := B) M
    ((Finset.range (p.natDegree + 1)).image p.coeff) (S := L)
  set t : L := algebraMap B L (s : B) with ht
  have hlift : scaleRoots p t ∈ lifts (algebraMap B L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_or_ge i p.natDegree with hi | hi
    · obtain ⟨c, hc⟩ := hs (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (s : B) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, pow_succ, Algebra.smul_def, ← ht]
      ring
    · rcases eq_or_lt_of_le hi with h | h
      · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
      · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).2 hp)
  obtain ⟨b, hb⟩ := hB q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := IsLocalization.map_units L s
  refine ⟨algebraMap B L b * ((u⁻¹ : Lˣ) : L), ?_⟩
  have h1 : (scaleRoots p t).eval (algebraMap B L b) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, hb, map_zero]
  have h2 : (scaleRoots p t).eval (t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L))) =
      t ^ p.natDegree * p.eval (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) :=
    scaleRoots_eval₂_mul (p := p) (RingHom.id L) (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) t
  have h3 : t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) = algebraMap B L b := by
    rw [ht, ← hu, mul_comm (algebraMap B L b), ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1] at h2
  have hunit : IsUnit (t ^ p.natDegree) := (hu ▸ u.isUnit).pow _
  exact (hunit.mul_right_eq_zero).1 h2.symm

/- English proof (translation)
Introduce `B _ _ M h0 hB`. Establish `hle : M ≤ nonZeroDivisors B` using `fun x hx => mem_nonZeroDivisors_of_ne_zero (fun h => h0 (h ▸ hx))`. Conclude with `⟨IsLocalization.isDomain_localization hle, aic_loc B M hB⟩`.
-/
theorem LocAIC_of : LateralTheory.E.HensCut.LocAIC := by
  intro B _ _ M h0 hB
  have hle : M ≤ nonZeroDivisors B := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero (fun h => h0 (h ▸ hx))
  exact ⟨IsLocalization.isDomain_localization hle, aic_loc B M hB⟩

end LateralTheory.E.LocalizationIntegralClosure
