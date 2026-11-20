import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem isExcisionNbhd_away_of_isUnit_mod : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B),
    IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) →
    IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  intro B A' _ _ _ f s hA hs
  obtain ⟨hEt, h2, h3⟩ := hA
  obtain ⟨σ, hσ⟩ : ∃ σ : A', σ = algebraMap B A' s := ⟨_, rfl⟩
  rw [← hσ]

  obtain ⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ Ideal.span {f} := by
    obtain ⟨v, hv⟩ := hs.exists_right_inv
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  have hpow : ∀ n : ℕ, (s * t) ^ n - 1 ∈ Ideal.span {f} := by
    intro n
    obtain ⟨c, hc⟩ := (sub_dvd_pow_sub_pow (s * t) 1 n)
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ ht
  haveI : Algebra.Etale A' (Localization.Away σ) := Algebra.Etale.of_isLocalizationAway σ
  haveI : Algebra.Etale B (Localization.Away σ) := Algebra.Etale.comp B A' (Localization.Away σ)
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a', m⟩, hx⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) x
    have hxs : x * algebraMap A' (Localization.Away σ) m = algebraMap A' _ a' := by
      rw [← hx]; exact IsLocalization.mk'_spec _ _ _
    obtain ⟨n, hn⟩ := m.2
    rw [← hn] at hxs
    obtain ⟨b, hb⟩ := h2 (a' * algebraMap B A' t ^ n)
    refine ⟨b, ?_⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hpow n)
    have hc' := congrArg (algebraMap A' (Localization.Away σ)) hc
    have hv' := congrArg (algebraMap A' (Localization.Away σ)) (congrArg (algebraMap B A') hv)
    rw [Ideal.mem_span_singleton']
    refine ⟨-(x * algebraMap A' _ (algebraMap B A' v)) + algebraMap A' _ c, ?_⟩
    simp only [IsScalarTower.algebraMap_apply B A' (Localization.Away σ), map_mul, map_sub, map_pow, map_one,
      ← hσ] at hxs hc' hv' ⊢
    linear_combination hc' - x * hv' - (algebraMap A' (Localization.Away σ) (algebraMap B A' t)) ^ n * hxs
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨⟨c, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) y
    have hys := IsLocalization.mk'_spec (Localization.Away σ) c (⟨σ ^ n, n, rfl⟩ : Submonoid.powers σ)
    have key : algebraMap A' (Localization.Away σ) (algebraMap B A' a * σ ^ n) =
        algebraMap A' (Localization.Away σ) (c * algebraMap B A' f) := by
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hy]
      simp only at hys
      rw [← hys]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers σ) _).1 key
    have hmem : algebraMap B A' (s ^ (k + n) * a) ∈ Ideal.span {algebraMap B A' f} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨σ ^ k * c, ?_⟩
      simp only at hk
      rw [map_mul, map_pow, ← hσ, pow_add]
      linear_combination -hk
    have h1 := h3 _ hmem
    have h4 := hpow (k + n)
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h4
    rw [Ideal.mem_span_singleton']
    refine ⟨t ^ (k + n) * p - a * q, ?_⟩
    linear_combination t ^ (k + n) * hp - a * hq

end GlobalTheory.EtC
