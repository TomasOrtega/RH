import Formalism.WindowSums.Statement

namespace Formalism.WindowSums

open Polynomial

/- English proof (translation)
Introduce `ℓ _ c ell JJ V _ _ T`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨i, hi, hx⟩`. Establish `hsplit : PP ℓ c ell JJ = ((∏ k ∈ (JJ.erase 0).erase i, (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (k * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) * ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k) * (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) …`. Unfold `PP`.

Rewrite using `[← Finset.mul_prod_erase _ _ hi]`. Expand and normalize the polynomial expressions, which then agree. Establish `hk : Polynomial.aeval T (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) x = 0`. Simplify using `[hx]`. Rewrite using `[hsplit, map_mul, Module.End.mul_apply, hk, map_zero]`.

Introduce `v hv`. Establish `hS : Polynomial.aeval T (∑ k ∈ Finset.range (ℓ ^ ell), (Polynomial.X : Polynomial ℤ_[ℓ]) ^ k) (T v - v) = 0`. Establish `h1 : T v - v = Polynomial.aeval T (Polynomial.X - 1 : Polynomial ℤ_[ℓ]) v` using `by simp`. Rewrite using `[h1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul]`. Simplify using `[hv]`.

Unfold `PP`. Rewrite using `[map_mul, Module.End.mul_apply, hS, map_zero]`.
-/
theorem annihilatorPoly_kills : KillerKills := by
  intro ℓ _ c ell JJ V _ _ T
  refine ⟨?_, ?_⟩
  · rintro x ⟨i, hi, hx⟩
    have hsplit : PP ℓ c ell JJ = ((∏ k ∈ (JJ.erase 0).erase i, (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (k * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k) * (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
      unfold PP
      rw [← Finset.mul_prod_erase _ _ hi]
      ring
    have hk : Polynomial.aeval T (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) x = 0 := by
      simp [hx]
    rw [hsplit, map_mul, Module.End.mul_apply, hk, map_zero]
  · intro v hv
    have hS : Polynomial.aeval T (∑ k ∈ Finset.range (ℓ ^ ell), (Polynomial.X : Polynomial ℤ_[ℓ]) ^ k)
        (T v - v) = 0 := by
      have h1 : T v - v = Polynomial.aeval T (Polynomial.X - 1 : Polynomial ℤ_[ℓ]) v := by simp
      rw [h1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul]
      simp [hv]
    unfold PP
    rw [map_mul, Module.End.mul_apply, hS, map_zero]

end Formalism.WindowSums
