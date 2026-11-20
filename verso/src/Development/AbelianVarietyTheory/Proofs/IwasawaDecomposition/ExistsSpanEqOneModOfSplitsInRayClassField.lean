import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.Mem.RaySplit

open GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

/- English proof (translation)
Use `hR.1` as an intermediate fact. Use `𝔭.isPrime` as an intermediate fact. Use `𝔭.isMaximal` as an intermediate fact. Establish `hcop : IsCoprime 𝔭.asIdeal 𝔮`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`.

Assume the negation of the conclusion as `h`. Conclude with `hnd (Ideal.dvd_iff_le.2 (le_sup_right.trans (𝔭.isMaximal.eq_of_le h le_sup_left).symm.le))`. Take `⟨σ, P, hP, hPo, hσ⟩` from `exists_isFrob L 𝔭`. Establish `hne : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P`. Establish `hPm : P.IsMaximal` using `hP.isMaximal hne`.

Establish `hef` using `(GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭).1 hs P ⟨hP, hPo⟩`. Establish `hf : 𝔭.asIdeal.inertiaDeg' P = 1`. Rewrite using `[Ideal.inertiaDeg'_eq_inertiaDeg]`. Conclude with `Nat.eq_one_of_mul_eq_one_left hef`. Establish `hN : Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal`.

Rewrite using `[Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot, hf, pow_one]`. Establish `: Finite (𝓞 L ⧸ P)` using `Ideal.finiteQuotientOfFreeOfNeBot _ hne`. Use `letI := Ideal.Quotient.field P`. Use `letI := Fintype.ofFinite (𝓞 L ⧸ P)`. Establish `hpow : ∀ x : 𝓞 L, x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P` using `fun x => by`.

Rewrite using `[← Ideal.Quotient.eq, map_pow, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`. Conclude with `FiniteField.pow_card _`. Establish `hin : InInertia L 𝔭 σ` using `⟨P, hP, hPo, fun x => by`. Use `add_mem (hσ x) (hpow x)` as an intermediate fact. Rewrite using `[sub_add_sub_cancel] at this⟩` and apply the resulting hypothesis.

Establish `hσ1 : σ = 1` using `hR.2.1 𝔭 hnd σ hin`. Establish `hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ 𝔭.asIdeal = 1` using `fun χ => by`. Rewrite using `[heckeIdeal_asIdeal, heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ⟨P, hP, hPo, hσ⟩, hσ1, map_one, Units.val_one]`. Take `⟨α, β, hab, he⟩` from `(hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).1 hχ`. Establish `hα : α ∈ 𝔭.asIdeal * Ideal.span {β}` using `he ▸ Ideal.mem_span_singleton_self α`.

Take `⟨π, hπ, rfl⟩` from `Ideal.mem_mul_span_singleton.1 hα`. Establish `hβ0 : Ideal.span {β} ≠ (0 : Ideal (𝓞 K))`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hab.2.1`. Establish `hsp : 𝔭.asIdeal = Ideal.span {π}`.

Use `mul_right_cancel₀ hβ0 ?_` and prove the remaining obligations. Rewrite using `[he, Ideal.span_singleton_mul_span_singleton]`. Use `⟨π, hsp, ?_⟩` and prove the remaining obligations. Take `⟨i, hi, j, hj, hij⟩` from `Ideal.isCoprime_iff_exists.1 hab.2.2.2.1`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hi`.

Establish `h1 : (π - 1) * β ∈ 𝔮`. Use `hab.2.2.2.2.1` as an intermediate fact. Rewrite `this` using `[show π * β - β = (π - 1) * β by ring]`. Then use the resulting hypothesis. Establish `h2 : π - 1 = c * ((π - 1) * β) + (π - 1) * j`. Take the linear combination `(π - 1) * hij.symm`.

Rewrite using `[h2]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hj)`.
-/
theorem exists_span_eq_of_splits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)) (hR : GlobalTheory.Mem.Fld.IsRayField K L 𝔮) (𝔭 : HeightOneSpectrum (𝓞 K)) (hnd : ¬ 𝔭.asIdeal ∣ 𝔮)
    (hs : (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  have := hR.1
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hnd (Ideal.dvd_iff_le.2 (le_sup_right.trans (𝔭.isMaximal.eq_of_le h le_sup_left).symm.le))
  obtain ⟨σ, P, hP, hPo, hσ⟩ := exists_isFrob L 𝔭
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hef := (GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭).1 hs P ⟨hP, hPo⟩
  have hf : 𝔭.asIdeal.inertiaDeg' P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  have hN : Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot, hf, pow_one]
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI := Ideal.Quotient.field P
  letI := Fintype.ofFinite (𝓞 L ⧸ P)
  have hpow : ∀ x : 𝓞 L, x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := fun x => by
    rw [← Ideal.Quotient.eq, map_pow, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hin : InInertia L 𝔭 σ := ⟨P, hP, hPo, fun x => by
    have := add_mem (hσ x) (hpow x)
    rwa [sub_add_sub_cancel] at this⟩
  have hσ1 : σ = 1 := hR.2.1 𝔭 hnd σ hin
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ 𝔭.asIdeal = 1 := fun χ => by
    rw [heckeIdeal_asIdeal, heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ⟨P, hP, hPo, hσ⟩, hσ1, map_one, Units.val_one]
  obtain ⟨α, β, hab, he⟩ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).1 hχ
  have hα : α ∈ 𝔭.asIdeal * Ideal.span {β} := he ▸ Ideal.mem_span_singleton_self α
  obtain ⟨π, hπ, rfl⟩ := Ideal.mem_mul_span_singleton.1 hα
  have hβ0 : Ideal.span {β} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hab.2.1
  have hsp : 𝔭.asIdeal = Ideal.span {π} := by
    refine mul_right_cancel₀ hβ0 ?_
    rw [he, Ideal.span_singleton_mul_span_singleton]
  refine ⟨π, hsp, ?_⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hab.2.2.2.1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have h1 : (π - 1) * β ∈ 𝔮 := by
    have := hab.2.2.2.2.1
    rwa [show π * β - β = (π - 1) * β by ring] at this
  have h2 : π - 1 = c * ((π - 1) * β) + (π - 1) * j := by
    linear_combination (π - 1) * hij.symm
  rw [h2]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hj)

end GlobalTheory.Mem.RaySplit
