import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks

open Polynomial

namespace LateralTheory.E.FracAICPf

open Classical in
/- English proof (translation)
Introduce `T K _ _ _ _ _ hT p hp hdeg`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T) (p.support.image p.coeff)`. Use `set s : K := algebraMap T K b with hs`. Establish `hs0 : s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Use `set q := p.scaleRoots s with hq`.

Establish `hqm : q.Monic` using `(monic_scaleRoots_iff _).mpr hp`. Establish `hqd : q.natDegree = p.natDegree` using `natDegree_scaleRoots _ _`. Establish `hlift : q ∈ lifts (algebraMap T K)`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `i`.

Rewrite using `[hq, coeff_scaleRoots]`. Distinguish the cases in `hi : p.coeff i = 0`. Rewrite using `[hi, zero_mul]`. Conclude with `⟨0, map_zero _⟩`. Establish `hile : i ≤ p.natDegree` using `le_natDegree_of_ne_zero hi`.

Break down `lt_or_eq_of_le hile with hlt | heq` into its components or cases. Take `⟨c, hc⟩` from `hb (p.coeff i) (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))`. Take `⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1` from `⟨p.natDegree - i - 1, by omega⟩`. Use `⟨c * (b : T) ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, map_mul, map_pow, hc, Algebra.smul_def, pow_succ, hs]`.

Expand and normalize the polynomial expressions, which then agree. Substitute `heq` using the available equality. Rewrite using `[Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree]`. Conclude with `⟨1, map_one _⟩`. Take `⟨q', hq'map, hq'deg, hq'm⟩` from `lifts_and_natDegree_eq_and_monic hlift hqm`.

Take `⟨r, hr⟩` from `hT q' hq'm (by rw [hq'deg, hqd]; exact hdeg)`. Use `⟨algebraMap T K r / s, ?_⟩` and prove the remaining obligations. Establish `h1 : q.eval (algebraMap T K r) = 0`. Rewrite using `[← hq'map, eval_map, eval₂_at_apply, hr, map_zero]`. Establish `h2` using `scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap T K r / s) s`.

Simplify using `only [RingHom.id_apply, eval₂_id] at h2`. Rewrite `h2` using `[mul_div_cancel₀ _ hs0, ← hq, h1]`. Conclude with `(mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hs0)`.
-/
theorem FracAIC_of : LateralTheory.E.ULAStalkPf.FracAIC := by
  intro T K _ _ _ _ _ hT p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
    (p.support.image p.coeff)
  set s : K := algebraMap T K b with hs
  have hs0 : s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  set q := p.scaleRoots s with hq
  have hqm : q.Monic := (monic_scaleRoots_iff _).mpr hp
  have hqd : q.natDegree = p.natDegree := natDegree_scaleRoots _ _
  have hlift : q ∈ lifts (algebraMap T K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [hq, coeff_scaleRoots]
    by_cases hi : p.coeff i = 0
    · rw [hi, zero_mul]; exact ⟨0, map_zero _⟩
    have hile : i ≤ p.natDegree := le_natDegree_of_ne_zero hi
    rcases lt_or_eq_of_le hile with hlt | heq
    · obtain ⟨c, hc⟩ := hb (p.coeff i) (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (b : T) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, Algebra.smul_def, pow_succ, hs]
      ring
    · subst heq
      rw [Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree]
      exact ⟨1, map_one _⟩
  obtain ⟨q', hq'map, hq'deg, hq'm⟩ := lifts_and_natDegree_eq_and_monic hlift hqm
  obtain ⟨r, hr⟩ := hT q' hq'm (by rw [hq'deg, hqd]; exact hdeg)
  refine ⟨algebraMap T K r / s, ?_⟩
  have h1 : q.eval (algebraMap T K r) = 0 := by
    rw [← hq'map, eval_map, eval₂_at_apply, hr, map_zero]
  have h2 := scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap T K r / s) s
  simp only [RingHom.id_apply, eval₂_id] at h2
  rw [mul_div_cancel₀ _ hs0, ← hq, h1] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hs0)

end LateralTheory.E.FracAICPf
