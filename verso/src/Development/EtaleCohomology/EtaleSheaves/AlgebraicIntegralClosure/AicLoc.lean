import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.BaseAICPf.Loc

/- English proof (translation)
Introduce `p hm hd`. Use `set n := p.natDegree`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (n + 1)).image p.coeff)`. Use `set u := algebraMap A L b`. Establish `hlift : p.scaleRoots u ∈ lifts (algebraMap A L)`.

Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `i`. Rewrite using `[coeff_scaleRoots]`. Break down `lt_trichotomy i n with h | h | h` into its components or cases. Take `⟨a, ha⟩` from `hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)`.

Take `⟨k, hk⟩ : ∃ k, n - i = k + 1` from `⟨n - i - 1, by omega⟩`. Use `⟨a * (b : A) ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, map_mul, map_pow, ha, Algebra.smul_def, pow_succ]`. Simplify using `only [u]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `h; rw [tsub_self, pow_zero, mul_one]; exact ⟨1, by rw [map_one]; exact hm.symm⟩` using the available equality. Rewrite using `[coeff_eq_zero_of_natDegree_lt h, zero_mul]`. Conclude with `⟨0, map_zero _⟩`. Take `⟨q, hq, hqd, hqm⟩` from `lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff u).2 hm)`. Take `⟨a, ha⟩` from `hA q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)`.

Establish `hu : IsUnit u` using `IsLocalization.map_units L b`. Take `⟨v, hv⟩` from `id hu`. Use `⟨(↑v⁻¹ : L) * algebraMap A L a, ?_⟩` and prove the remaining obligations. Establish `h1 : (p.scaleRoots u).eval (algebraMap A L a) = 0`. Rewrite using `[← hq, eval_map, eval₂_at_apply, ha, map_zero]`.

Establish `h2 : (p.scaleRoots u).eval (u * ((↑v⁻¹ : L) * algebraMap A L a)) = u ^ n * p.eval ((↑v⁻¹ : L) * algebraMap A L a)` using `scaleRoots_eval₂_mul (RingHom.id L) _ u`. Establish `hur : u * ((↑v⁻¹ : L) * algebraMap A L a) = algebraMap A L a`. Rewrite using `[← hv, ← mul_assoc, Units.mul_inv, one_mul]`. Rewrite `h2` using `[hur, h1]`. Establish `hun : IsUnit (u ^ n)` using `hu.pow n`.

Conclude with `(hun.mul_right_eq_zero).1 h2.symm`.
-/
theorem aic_loc {A L : Type} [CommRing A] [CommRing L] [Algebra A L] (M : Submonoid A) [IsLocalization M L]
    (hA : AIC A) : AIC L := by
  classical
  intro p hm hd
  set n := p.natDegree
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (n + 1)).image p.coeff)
  set u := algebraMap A L b
  have hlift : p.scaleRoots u ∈ lifts (algebraMap A L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i n with h | h | h
    · obtain ⟨a, ha⟩ := hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
      refine ⟨a * (b : A) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, ha, Algebra.smul_def, pow_succ]
      simp only [u]; ring
    · subst h; rw [tsub_self, pow_zero, mul_one]; exact ⟨1, by rw [map_one]; exact hm.symm⟩
    · rw [coeff_eq_zero_of_natDegree_lt h, zero_mul]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff u).2 hm)
  obtain ⟨a, ha⟩ := hA q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  have hu : IsUnit u := IsLocalization.map_units L b
  obtain ⟨v, hv⟩ := id hu
  refine ⟨(↑v⁻¹ : L) * algebraMap A L a, ?_⟩
  have h1 : (p.scaleRoots u).eval (algebraMap A L a) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : (p.scaleRoots u).eval (u * ((↑v⁻¹ : L) * algebraMap A L a)) = u ^ n * p.eval ((↑v⁻¹ : L) * algebraMap A L a) :=
    scaleRoots_eval₂_mul (RingHom.id L) _ u
  have hur : u * ((↑v⁻¹ : L) * algebraMap A L a) = algebraMap A L a := by
    rw [← hv, ← mul_assoc, Units.mul_inv, one_mul]
  rw [hur, h1] at h2
  have hun : IsUnit (u ^ n) := hu.pow n
  exact (hun.mul_right_eq_zero).1 h2.symm

end LateralTheory.E.BaseAICPf.Loc
