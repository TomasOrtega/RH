import Mathlib
import GroundTheory.LocalFields.BrauerInductionPrime

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
/- English proof (translation)
The claim follows from `let ⟨p, hp, hHp⟩ := hH ⟨p, hp, hHp.mono hLH⟩`.
-/
theorem IsElementary.mono {H L : Subgroup G} (hH : IsElementary H) (hLH : L ≤ H) : IsElementary L :=
  let ⟨p, hp, hHp⟩ := hH
  ⟨p, hp, hHp.mono hLH⟩

variable (hmono : ∀ K : Subgroup G, IsElementary K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hmono

/- English proof (translation)
Set `T : ℤ →ₗ[ℤ] (G → ℂ)` to `LinearMap.toSpanSingleton ℤ (G → ℂ) 1`. Set `I : Submodule ℤ ℤ` to `(spanZ (IsElementary (G := G))).comap T`. Establish `hmem : ∀ k : ℤ, k ∈ I ↔ k • (1 : G → ℂ) ∈ spanZ (IsElementary (G` using `G)) := fun k ↦ Iff.rfl`. Establish `hprimes : ∀ p : ℕ, p.Prime → ∃ m : ℕ, ¬ p ∣ m ∧ (m : ℤ) ∈ I`. Introduce `p hp`.

Establish `: Fact p.Prime` using `⟨hp⟩`. Take `⟨m, hpm, hm⟩` from `exists_smul_one_mem_spanZ (p := p) (Complex.isPrimitiveRoot_exp _ Nat.card_pos.ne') (fun K hK χ hχ ↦ hmono K ⟨p, hp, hK⟩ χ hχ)`. Conclude with `⟨m, hpm, (hmem _).mpr (spanZ_mono (fun K hK ↦ ⟨p, hp, hK⟩) hm)⟩`. Use `set d := Submodule.IsPrincipal.generator I`. Establish `hdvd : ∀ k ∈ I, d ∣ k` using `fun k hk ↦ by`.

Take `⟨s, hs⟩` from `(Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hk`. Conclude with `⟨s, by rw [hs, smul_eq_mul, mul_comm]⟩`. Establish `hd : d.natAbs = 1`. Assume the negation of the conclusion as `hd`. Take `⟨p, hp, hpd⟩` from `Nat.exists_prime_and_dvd hd`.

Take `⟨m, hpm, hm⟩` from `hprimes p hp`. Apply `hpm` to reduce the goal to its premises. Establish `h1 : (p : ℤ) ∣ d` using `Int.natCast_dvd.mpr hpd`. Conclude with `Int.natCast_dvd_natCast.mp (h1.trans (hdvd _ hm))`. Establish `hd1 : (1 : ℤ) ∈ I`.

Establish `hdI : d ∈ I` using `Submodule.IsPrincipal.generator_mem I`. Break down `Int.natAbs_eq d with h | h` into its components or cases. Rewrite `h` using `[hd]`. Rewrite `hdI` using `[h]`. Then use the resulting hypothesis. Rewrite `h` using `[hd]`.

Use `I.smul_mem (-1) hdI` as an intermediate fact. Rewrite `this` using `[h, smul_eq_mul, Nat.cast_one, neg_mul_neg, one_mul]`. Then use the resulting hypothesis. Simplify using `using (hmem 1).mp hd1`.
-/
theorem one_mem_spanZ_of_mono : (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := by
  let T : ℤ →ₗ[ℤ] (G → ℂ) := LinearMap.toSpanSingleton ℤ (G → ℂ) 1
  let I : Submodule ℤ ℤ := (spanZ (IsElementary (G := G))).comap T
  have hmem : ∀ k : ℤ, k ∈ I ↔ k • (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := fun k ↦ Iff.rfl
  have hprimes : ∀ p : ℕ, p.Prime → ∃ m : ℕ, ¬ p ∣ m ∧ (m : ℤ) ∈ I := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hpm, hm⟩ := exists_smul_one_mem_spanZ (p := p) (Complex.isPrimitiveRoot_exp _
      Nat.card_pos.ne') (fun K hK χ hχ ↦ hmono K ⟨p, hp, hK⟩ χ hχ)
    exact ⟨m, hpm, (hmem _).mpr (spanZ_mono (fun K hK ↦ ⟨p, hp, hK⟩) hm)⟩
  set d := Submodule.IsPrincipal.generator I
  have hdvd : ∀ k ∈ I, d ∣ k := fun k hk ↦ by
    obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hk
    exact ⟨s, by rw [hs, smul_eq_mul, mul_comm]⟩
  have hd : d.natAbs = 1 := by
    by_contra hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    obtain ⟨m, hpm, hm⟩ := hprimes p hp
    apply hpm
    have h1 : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
    exact Int.natCast_dvd_natCast.mp (h1.trans (hdvd _ hm))
  have hd1 : (1 : ℤ) ∈ I := by
    have hdI : d ∈ I := Submodule.IsPrincipal.generator_mem I
    rcases Int.natAbs_eq d with h | h
    · rw [hd] at h
      rwa [h] at hdI
    · rw [hd] at h
      have := I.smul_mem (-1) hdI
      rwa [h, smul_eq_mul, Nat.cast_one, neg_mul_neg, one_mul] at this
  simpa using (hmem 1).mp hd1

/- English proof (translation)
Establish `h` using `mul_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono hχ (one_mem_spanZ_of_mono hmono)`. Rewrite `h` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem mem_spanZ_of_mono {χ : G → ℂ} (hχ : IsCharacter χ) : χ ∈ spanZ (IsElementary (G := G)) := by
  have h := mul_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono hχ (one_mem_spanZ_of_mono hmono)
  rwa [mul_one] at h

end GroundTheory.LocalField
