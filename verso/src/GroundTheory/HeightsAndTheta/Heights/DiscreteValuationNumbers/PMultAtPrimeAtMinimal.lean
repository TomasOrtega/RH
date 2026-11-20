import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

/- English proof (translation)
Take `⟨q, hqQ, hqW⟩` from `Set.not_subset.mp h`. Rewrite using `[LocalizedModule.subsingleton_iff]`. Introduce `m`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Use `⟨q, hqW, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Q.mul_mem_right a hqQ`.
-/
theorem localizedQuotient_subsingleton_of_not_le (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by
  obtain ⟨q, hqQ, hqW⟩ := Set.not_subset.mp h
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨q, hqW, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Q.mul_mem_right a hqQ

/- English proof (translation)
Rewrite `h` using `[← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `h`. Rewrite `hu` using `[smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `(‹W.IsPrime›.mem_or_mem hu).resolve_left u.2`.
-/
theorem localizedQuotient_mk_eq_zero (W : Ideal A) [W.IsPrime] (a : A) (s : W.primeCompl)
    (h : LocalizedModule.mk (Ideal.Quotient.mk W a) s = 0) : a ∈ W := by
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
  exact (‹W.IsPrime›.mem_or_mem hu).resolve_left u.2

/- English proof (translation)
Rewrite using `[isSimpleModule_iff_toSpanSingleton_surjective]`. Use `⟨⟨LocalizedModule.mk (Ideal.Quotient.mk W 1) 1, 0, fun h => ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).mpr (localizedQuotient_mk_eq_zero W 1 1 h))`. Introduce `x hx z`. Proceed by induction on `x using LocalizedModule.induction_on with | h m s => ?_`.

Proceed by induction on `z using LocalizedModule.induction_on with | h m' t => ?_`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective m'`. Establish `ha : a ∈ W.primeCompl` using `fun haW => hx (by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr haW, LocalizedModule.zero_mk])`.

Use `⟨Localization.mk ((s : A) * b) (⟨a, ha⟩ * t), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify using `only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem localizedQuotient_isSimpleModule (W : Ideal A) [W.IsPrime] :
    IsSimpleModule (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ W)) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk W 1) 1, 0, fun h => ?_⟩, ?_⟩
  · exact ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).mpr (localizedQuotient_mk_eq_zero W 1 1 h))
  intro x hx z
  induction x using LocalizedModule.induction_on with | h m s => ?_
  induction z using LocalizedModule.induction_on with | h m' t => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m'
  have ha : a ∈ W.primeCompl := fun haW => hx (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haW, LocalizedModule.zero_mk])
  refine ⟨Localization.mk ((s : A) * b) (⟨a, ha⟩ * t), ?_⟩
  rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul]
  congr 1
  ring

end General

/- English proof (translation)
Introduce `R _ K ι J Q W _ _ hJQ hW`. Unfold `multAt`. Distinguish the cases in `hQW : Q ≤ W`. Establish `hEq : Q = W` using `le_antisymm hQW (hW.2 ⟨‹Q.IsPrime›, hJQ⟩ hQW)`. Substitute `hEq` using the available equality.

Rewrite using `[if_pos rfl, Module.length_eq_one_iff]`. Conclude with `localizedQuotient_isSimpleModule Q`. Establish `hne : Q ≠ W` using `fun h => hQW h.le`. Rewrite using `[if_neg hne, Module.length_eq_zero_iff]`. Conclude with `localizedQuotient_subsingleton_of_not_le Q W hQW`.
-/
theorem MultAtPrimeAtMinimal.proof : MultAtPrimeAtMinimal.Statement := by
  intro R _ K ι J Q W _ _ hJQ hW
  unfold multAt
  by_cases hQW : Q ≤ W
  · have hEq : Q = W := le_antisymm hQW (hW.2 ⟨‹Q.IsPrime›, hJQ⟩ hQW)
    subst hEq
    rw [if_pos rfl, Module.length_eq_one_iff]
    exact localizedQuotient_isSimpleModule Q
  · have hne : Q ≠ W := fun h => hQW h.le
    rw [if_neg hne, Module.length_eq_zero_iff]
    exact localizedQuotient_subsingleton_of_not_le Q W hQW

end GroundTheory.Heights₂.Heights.NumbersDVR
