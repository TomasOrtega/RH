import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
