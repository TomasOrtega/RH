import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.QAClosedPf

open LateralTheory.E.t_E1Cut

/- English proof (translation)
Introduce `p hp hdeg`. Establish `hl : p ∈ lifts π` using `(lifts_iff_coeff_lifts p).2 fun n => hπ _`. Take `⟨q, hq, hqd, hqm⟩` from `lifts_and_natDegree_eq_and_monic hl hp`. Take `⟨a, ha⟩` from `hT q hqm (hqd ▸ hdeg)`. Use `⟨π a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hq, eval_map, eval₂_at_apply, ha, map_zero]`.
-/
theorem aic_of_surj {T S : Type} [CommRing T] [CommRing S] (π : T →+* S) (hT : AIC T)
    (hπ : Function.Surjective π) : AIC S := by
  intro p hp hdeg
  have hl : p ∈ lifts π := (lifts_iff_coeff_lifts p).2 fun n => hπ _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨π a, ?_⟩
  rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]

/- English proof (translation)
Establish `: IsDomain (Localization.Away t)` using `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)`. Introduce `p hp hdeg`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers t) (p.support.image p.coeff)`. Use `set c : Localization.Away t := algebraMap T _ b`. Establish `hcu : IsUnit c` using `IsLocalization.map_units _ b`.

Establish `hl : p.scaleRoots c ∈ lifts (algebraMap T (Localization.Away t))`. Use `(lifts_iff_coeff_lifts _).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[coeff_scaleRoots]`. Distinguish the cases in `hi : i ∈ p.support`. Establish `hle : i ≤ p.natDegree` using `le_natDegree_of_mem_supp i hi`.

Break down `lt_or_eq_of_le hle with hlt | heq` into its components or cases. Take `⟨z, hz⟩` from `hb _ (Finset.mem_image_of_mem _ hi)`. Use `⟨z * b ^ (p.natDegree - i - 1), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hz, Algebra.smul_def, map_pow]`. Rewrite using `[show c ^ (p.natDegree - i) = c * c ^ (p.natDegree - i - 1) by`.

Rewrite using `[← pow_succ']`. Use `congr 1`. Use the proof step `omega]`. Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `heq` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[hp.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]`. Rewrite using `[Polynomial.notMem_support_iff.1 hi]`. Conclude with `⟨0, by simp⟩`.

Take `⟨q, hq, hqd, hqm⟩` from `lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff c).2 hp)`. Rewrite `hqd` using `[natDegree_scaleRoots]`. Take `⟨a, ha⟩` from `hT q hqm (hqd ▸ hdeg)`. Use `⟨hcu.unit⁻¹ * algebraMap T _ a, ?_⟩` and prove the remaining obligations. Establish `h1 : eval (algebraMap T _ a) (p.scaleRoots c) = 0`.

Rewrite using `[← hq, eval_map, eval₂_at_apply, ha, map_zero]`. Establish `h2 : algebraMap T (Localization.Away t) a = (RingHom.id _) c * (hcu.unit⁻¹ * algebraMap T _ a)`. Rewrite using `[RingHom.id_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]`. Rewrite `h1` using `[eval, h2, scaleRoots_eval₂_mul]`. Rewrite using `[eval]`.

Conclude with `(mul_eq_zero.1 h1).resolve_left (by simpa using (hcu.pow _).ne_zero)`.
-/
theorem aic_away {T : Type} [CommRing T] [IsDomain T] (hT : AIC T) (t : T) (ht : t ≠ 0) :
    AIC (Localization.Away t) := by
  classical
  have : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  intro p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers t)
    (p.support.image p.coeff)
  set c : Localization.Away t := algebraMap T _ b
  have hcu : IsUnit c := IsLocalization.map_units _ b
  have hl : p.scaleRoots c ∈ lifts (algebraMap T (Localization.Away t)) := by
    refine (lifts_iff_coeff_lifts _).2 fun i => ?_
    rw [coeff_scaleRoots]
    by_cases hi : i ∈ p.support
    · have hle : i ≤ p.natDegree := le_natDegree_of_mem_supp i hi
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨z, hz⟩ := hb _ (Finset.mem_image_of_mem _ hi)
        refine ⟨z * b ^ (p.natDegree - i - 1), ?_⟩
        rw [map_mul, hz, Algebra.smul_def, map_pow]
        rw [show c ^ (p.natDegree - i) = c * c ^ (p.natDegree - i - 1) by
          rw [← pow_succ']; congr 1; omega]
        simp only [c]
        ring
      · subst heq
        refine ⟨1, ?_⟩
        rw [hp.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]
    · rw [Polynomial.notMem_support_iff.1 hi]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff c).2 hp)
  rw [natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨hcu.unit⁻¹ * algebraMap T _ a, ?_⟩
  have h1 : eval (algebraMap T _ a) (p.scaleRoots c) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : algebraMap T (Localization.Away t) a = (RingHom.id _) c * (hcu.unit⁻¹ * algebraMap T _ a) := by
    rw [RingHom.id_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [eval, h2, scaleRoots_eval₂_mul] at h1
  rw [eval]
  exact (mul_eq_zero.1 h1).resolve_left (by simpa using (hcu.pow _).ne_zero)

/- English proof (translation)
Introduce `S _ hS`. Take `⟨T, _, _, π, hT, hπ⟩` from `hS`. Use `⟨aic_of_surj π hT hπ, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Take `⟨t, rfl⟩` from `hπ f`.

Distinguish the cases in `ht : t = 0`. Establish `hu : IsUnit (algebraMap S (Localization.Away (π t)) (π t))` using `IsLocalization.Away.algebraMap_isUnit _`. Rewrite `hu` using `[show algebraMap S (Localization.Away (π t)) (π t) = 0 by rw [ht, map_zero, map_zero]]`. Establish `: Subsingleton (Localization.Away (π t))` using `subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)`. Conclude with `⟨T, inferInstance, inferInstance, (algebraMap S _).comp π, hT, fun y => ⟨0, Subsingleton.elim _ _⟩⟩`.

Establish `: IsDomain (Localization.Away t)` using `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)`. Establish `: IsLocalization (Submonoid.map π (Submonoid.powers t)) (Localization.Away (π t))`. Rewrite using `[Submonoid.map_powers]`. Use `infer_instance`. Conclude with `⟨Localization.Away t, inferInstance, inferInstance, _, aic_away hT t ht, IsLocalization.map_surjective_of_surjective (Submonoid.powers t) (Localization.Away t) (Localization.Away (π t)) hπ⟩`.

Introduce `J`. Conclude with `⟨T, inferInstance, inferInstance, (Ideal.Quotient.mk J).comp π, hT, (Ideal.Quotient.mk_surjective).comp hπ⟩`.
-/
theorem QAClosed_of : QAClosed := by
  intro S _ hS
  obtain ⟨T, _, _, π, hT, hπ⟩ := hS
  refine ⟨aic_of_surj π hT hπ, ?_, ?_⟩
  · intro f
    obtain ⟨t, rfl⟩ := hπ f
    by_cases ht : t = 0
    · have hu : IsUnit (algebraMap S (Localization.Away (π t)) (π t)) :=
        IsLocalization.Away.algebraMap_isUnit _
      rw [show algebraMap S (Localization.Away (π t)) (π t) = 0 by rw [ht, map_zero, map_zero]] at hu
      have : Subsingleton (Localization.Away (π t)) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
      exact ⟨T, inferInstance, inferInstance, (algebraMap S _).comp π, hT, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · have : IsDomain (Localization.Away t) :=
        IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
      have : IsLocalization (Submonoid.map π (Submonoid.powers t)) (Localization.Away (π t)) := by
        rw [Submonoid.map_powers]; infer_instance
      exact ⟨Localization.Away t, inferInstance, inferInstance, _, aic_away hT t ht,
        IsLocalization.map_surjective_of_surjective (Submonoid.powers t) (Localization.Away t)
          (Localization.Away (π t)) hπ⟩
  · intro J
    exact ⟨T, inferInstance, inferInstance, (Ideal.Quotient.mk J).comp π, hT,
      (Ideal.Quotient.mk_surjective).comp hπ⟩

end LateralTheory.E.QAClosedPf
