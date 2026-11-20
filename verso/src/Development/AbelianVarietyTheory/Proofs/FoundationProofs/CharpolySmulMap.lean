import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm

noncomputable section

open Polynomial

namespace GlobalTheory.TwAtt

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
theorem normV_eq (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

/- English proof (translation)
Rewrite using `[normV_eq]`. Use `⟨fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)`. Rewrite `h1` using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]`. Then use the resulting hypothesis. Introduce and unpack `⟨c, rfl⟩`.

Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)`.
-/
theorem mem_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1
  · rintro ⟨c, rfl⟩
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

/- English proof (translation)
Establish `h1 : 1 < normV v` using `NumberField.HeightOneSpectrum.one_lt_absNorm v`. Use `Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hm`. Establish `h2` using `(mem_iff v _).2 dvd_rfl`. Rewrite `h2` using `[hc, Nat.cast_mul]`.

Break down `v.isPrime.mem_or_mem h2 with h | h` into its components or cases. Conclude with `Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))`. Establish `h3` using `Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)`. Rewrite `hc` using `[h3]`. Conclude with `Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))`.
-/
theorem normV_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (normV v).Prime := by
  have h1 : 1 < normV v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

/- English proof (translation)
Establish `hle : v.asIdeal ≤ v'.asIdeal`. Introduce `x hx`. Take `⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x` from `⟨Rat.ringOfIntegersEquiv x, by`. Apply `Rat.ringOfIntegersEquiv.injective` to reduce the goal to its premises. Use the proof step `simp⟩`.

Establish `key : ∀ I : Ideal (𝓞 ℚ), (m : 𝓞 ℚ) ∈ I ↔ ((m.natAbs : ℕ) : 𝓞 ℚ) ∈ I` using `fun I => by`. Break down `Int.natAbs_eq m with e | e` into its components or cases. Use `conv_lhs => rw [e]`. Rewrite using `[Int.cast_natCast]`. Use `conv_lhs => rw [e]`.

Rewrite using `[Int.cast_neg, Int.cast_natCast, neg_mem_iff]`. Rewrite `hx`, the goal using `[key, mem_iff]`. Conclude with `((mem_iff _ _).1 h).trans hx`. Conclude with `(HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm`.
-/
theorem eq_of_normV {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : ((normV v : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := by
    intro x hx
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x := ⟨Rat.ringOfIntegersEquiv x, by
      apply Rat.ringOfIntegersEquiv.injective; simp⟩
    have key : ∀ I : Ideal (𝓞 ℚ), (m : 𝓞 ℚ) ∈ I ↔ ((m.natAbs : ℕ) : 𝓞 ℚ) ∈ I := fun I => by
      rcases Int.natAbs_eq m with e | e
      · conv_lhs => rw [e]
        rw [Int.cast_natCast]
      · conv_lhs => rw [e]
        rw [Int.cast_neg, Int.cast_natCast, neg_mem_iff]
    rw [key, mem_iff] at hx ⊢
    exact ((mem_iff _ _).1 h).trans hx
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm

/- English proof (translation)
Introduce `v v' h`. Use `(eq_of_normV (v := v') (v' := v) ?_)` and prove the remaining obligations. Rewrite using `[← h]`. Conclude with `(mem_iff v _).2 dvd_rfl`.
-/
theorem normV_injective : Function.Injective (normV : HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v v' h
  refine (eq_of_normV (v := v') (v' := v) ?_)
  rw [← h]
  exact (mem_iff v _).2 dvd_rfl

end GlobalTheory.TwAtt

end
