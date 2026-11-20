import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `set L := Localization.AtPrime P`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Take `⟨n, hn⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := L)`. Establish `hJ : (⊥ : Ideal L).jacobson = IsLocalRing.maximalIdeal L` using `IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top`.

Establish `han : a ^ n = 0`. Establish `: a ^ n ∈ (⊥ : Ideal L).jacobson ^ n` using `Ideal.pow_mem_pow (hJ ▸ ha) n`. Rewrite `this` using `[hn]`. Simplify using `using this`. Take `⟨⟨d, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl a`.

Simplify using `only at han ⊢`. Rewrite `han` using `[← IsLocalization.mk'_pow, IsLocalization.mk'_eq_zero_iff]`. Take `⟨t, ht⟩` from `han`. Establish `hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {x}) ((t : D) * d))`. Use `⟨n + 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, mul_pow, pow_succ d, ← mul_assoc, pow_succ (t : D), mul_assoc _ (t : D), ht]`. Simplify using the standard rewrite rules. Establish `hmem : (t : D) * d ∈ Ideal.span {x}` using `Ideal.Quotient.eq_zero_iff_mem.mp (hnil.eq_zero)`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Use `Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' L c (t * s), ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one d s, mul_right_comm, ← map_mul, hc, ← IsLocalization.mk'_eq_mul_mk'_one, ← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_iff_eq]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Use `(IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `hx.map (algebraMap D L)`. Conclude with `not_isUnit_zero (hm ▸ hu.pow m)`.
-/
theorem localization_maximalIdeal_eq_span_of_nilpotent
    (D : Type) [CommRing D] [IsArtinianRing D] (x : D) (hx : IsNilpotent x)
    (hred : IsReduced (D ⧸ Ideal.span {x})) (P : Ideal D) [P.IsMaximal] :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap D (Localization.AtPrime P) x} := by
  set L := Localization.AtPrime P
  apply le_antisymm
  · intro a ha

    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := L)
    have hJ : (⊥ : Ideal L).jacobson = IsLocalRing.maximalIdeal L :=
      IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top
    have han : a ^ n = 0 := by
      have : a ^ n ∈ (⊥ : Ideal L).jacobson ^ n := Ideal.pow_mem_pow (hJ ▸ ha) n
      rw [hn] at this
      simpa using this
    obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    simp only at han ⊢
    rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_zero_iff] at han
    obtain ⟨t, ht⟩ := han
    have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {x}) ((t : D) * d)) := by
      refine ⟨n + 1, ?_⟩
      rw [← map_pow, mul_pow, pow_succ d, ← mul_assoc, pow_succ (t : D), mul_assoc _ (t : D), ht]
      simp
    have hmem : (t : D) * d ∈ Ideal.span {x} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hnil.eq_zero)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' L c (t * s), ?_⟩
    rw [IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one d s,
      mul_right_comm, ← map_mul, hc, ← IsLocalization.mk'_eq_mul_mk'_one,
      ← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_iff_eq]
    congr 1
    push_cast
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    obtain ⟨m, hm⟩ := hx.map (algebraMap D L)
    exact not_isUnit_zero (hm ▸ hu.pow m)

end GlobalTheory
