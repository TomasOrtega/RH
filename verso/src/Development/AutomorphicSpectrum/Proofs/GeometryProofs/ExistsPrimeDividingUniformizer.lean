import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Rescar

/- English proof (translation)
Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => exact absurd rfl hn`. Consider the case `one`. Conclude with `absurd (by simpa using hmem : (1 : R) ∈ P) (fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h))`. Consider the case `prime p hp => exact ⟨p, hp, hmem⟩`.

Consider the case `mul a b iha ihb`. Establish `ha : a ≠ 0` using `fun h => hn (by simp [h])`. Establish `hb : b ≠ 0` using `fun h => hn (by simp [h])`. Rewrite `hmem` using `[Nat.cast_mul]`. Break down `hP.mem_or_mem hmem with h | h` into its components or cases.

Conclude with `iha ha h`. Conclude with `ihb hb h`.
-/
theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (n : ℕ) (hn : n ≠ 0) (hmem : (n : R) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : R) ∈ P := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    exact absurd (by simpa using hmem : (1 : R) ∈ P) (fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h))
  | prime p hp => exact ⟨p, hp, hmem⟩
  | mul a b iha ihb =>
    have ha : a ≠ 0 := fun h => hn (by simp [h])
    have hb : b ≠ 0 := fun h => hn (by simp [h])
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact iha ha h
    · exact ihb hb h

/- English proof (translation)
Establish `hne : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F') ∈ v.asIdeal`. Simplify using `using Ideal.absNorm_mem v.asIdeal`.

Take `⟨ℓ, hℓ, hℓmem⟩` from `exists_prime_natCast_mem v.asIdeal _ hne hmem`. Use `⟨ℓ, hℓ, ?_⟩` and prove the remaining obligations. Establish `hlt : v.valuation F' (ℓ : F') < 1`. Use `(v.valuation_lt_one_iff_mem (K := F') (ℓ : 𝓞 F')).2 hℓmem` as an intermediate fact. Simplify using `using this`.

Establish `hle : v.valuation F' (ℓ : F') ≤ WithZero.exp (-1 : ℤ)`. Break down `eq_or_ne (v.valuation F' (ℓ : F')) 0 with h0 | h0` into its components or cases. Rewrite using `[h0]`. Conclude with `zero_le'`. Take `⟨a, ha⟩ : ∃ a : ℤ, v.valuation F' (ℓ : F') = WithZero.exp a` from `⟨WithZero.log _, (WithZero.exp_log h0).symm⟩`.

Rewrite `hlt`, the goal using `[ha]`. Establish `h1 : a < 0`. Rewrite `hlt` using `[← WithZero.exp_zero]`. Conclude with `WithZero.exp_lt_exp.1 hlt`. Conclude with `WithZero.exp_le_exp.2 (by omega)`.

Rewrite using `[map_div₀, hπ]`. Conclude with `div_le_one_of_le₀ hle zero_le'`.
-/
theorem exists_prime_div_uniformiser (F' : Type) [Field F'] [NumberField F']
    (v : HeightOneSpectrum (𝓞 F')) (π : F') (hπ : v.valuation F' π = WithZero.exp (-1 : ℤ)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F') ∈ v.asIdeal := by
    simpa using Ideal.absNorm_mem v.asIdeal
  obtain ⟨ℓ, hℓ, hℓmem⟩ := exists_prime_natCast_mem v.asIdeal _ hne hmem
  refine ⟨ℓ, hℓ, ?_⟩
  have hlt : v.valuation F' (ℓ : F') < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F') (ℓ : 𝓞 F')).2 hℓmem
    simpa using this
  have hle : v.valuation F' (ℓ : F') ≤ WithZero.exp (-1 : ℤ) := by
    rcases eq_or_ne (v.valuation F' (ℓ : F')) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, v.valuation F' (ℓ : F') = WithZero.exp a :=
        ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
      rw [ha] at hlt ⊢
      have h1 : a < 0 := by
        rw [← WithZero.exp_zero] at hlt
        exact WithZero.exp_lt_exp.1 hlt
      exact WithZero.exp_le_exp.2 (by omega)
  rw [map_div₀, hπ]
  exact div_le_one_of_le₀ hle zero_le'

end GlobalTheory.CompanionTheory.Ar.Rescar
