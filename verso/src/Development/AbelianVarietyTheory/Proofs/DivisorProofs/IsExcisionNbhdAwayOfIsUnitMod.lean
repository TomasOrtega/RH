import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `B A' _ _ _ f s hA hs`. Take `⟨hEt, h2, h3⟩` from `hA`. Take `⟨σ, hσ⟩ : ∃ σ : A', σ = algebraMap B A' s` from `⟨_, rfl⟩`. Rewrite using `[← hσ]`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ Ideal.span {f} := by`.

Take `⟨v, hv⟩` from `hs.exists_right_inv`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]`. Establish `hpow : ∀ n : ℕ, (s * t) ^ n - 1 ∈ Ideal.span {f}`.

Introduce `n`. Take `⟨c, hc⟩` from `(sub_dvd_pow_sub_pow (s * t) 1 n)`. Rewrite `hc` using `[one_pow]`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right _ _ ht`.

Use `haveI : Algebra.Etale A' (Localization.Away σ) := Algebra.Etale.of_isLocalizationAway σ`. Use `haveI : Algebra.Etale B (Localization.Away σ) := Algebra.Etale.comp B A' (Localization.Away σ)`. Use `⟨inferInstance, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨⟨a', m⟩, hx⟩` from `IsLocalization.mk'_surjective (Submonoid.powers σ) x`.

Establish `hxs : x * algebraMap A' (Localization.Away σ) m = algebraMap A' _ a'`. Rewrite using `[← hx]`. Conclude with `IsLocalization.mk'_spec _ _ _`. Take `⟨n, hn⟩` from `m.2`. Rewrite `hxs` using `[← hn]`.

Take `⟨b, hb⟩` from `h2 (a' * algebraMap B A' t ^ n)`. Use `⟨b, ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hb`. Take `⟨v, hv⟩` from `Ideal.mem_span_singleton'.1 (hpow n)`. Establish `hc'` using `congrArg (algebraMap A' (Localization.Away σ)) hc`.

Establish `hv'` using `congrArg (algebraMap A' (Localization.Away σ)) (congrArg (algebraMap B A') hv)`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨-(x * algebraMap A' _ (algebraMap B A' v)) + algebraMap A' _ c, ?_⟩` and prove the remaining obligations. Simplify using `only [IsScalarTower.algebraMap_apply B A' (Localization.Away σ), map_mul, map_sub, map_pow, map_one, ← hσ] at hxs hc' hv' ⊢`. Take the linear combination `hc' - x * hv' - (algebraMap A' (Localization.Away σ) (algebraMap B A' t)) ^ n * hxs`.

Introduce `a ha`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 ha`. Take `⟨⟨c, _, n, rfl⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers σ) y`. Establish `hys` using `IsLocalization.mk'_spec (Localization.Away σ) c (⟨σ ^ n, n, rfl⟩ : Submonoid.powers σ)`. Establish `key : algebraMap A' (Localization.Away σ) (algebraMap B A' a * σ ^ n) = algebraMap A' (Localization.Away σ) (c * algebraMap B A' f)`.

Rewrite using `[map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hy]`. Simplify using `only at hys`. Rewrite using `[← hys]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨⟨_, k, rfl⟩, hk⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers σ) _).1 key`.

Establish `hmem : algebraMap B A' (s ^ (k + n) * a) ∈ Ideal.span {algebraMap B A' f}`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨σ ^ k * c, ?_⟩` and prove the remaining obligations. Simplify using `only at hk`. Rewrite using `[map_mul, map_pow, ← hσ, pow_add]`.

Take the linear combination `-hk`. Establish `h1` using `h3 _ hmem`. Establish `h4` using `hpow (k + n)`. Take `⟨p, hp⟩` from `Ideal.mem_span_singleton'.1 h1`. Take `⟨q, hq⟩` from `Ideal.mem_span_singleton'.1 h4`.

Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨t ^ (k + n) * p - a * q, ?_⟩` and prove the remaining obligations. Take the linear combination `t ^ (k + n) * hp - a * hq`.
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
