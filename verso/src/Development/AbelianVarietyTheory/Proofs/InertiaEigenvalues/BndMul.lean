import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

variable {E : Type} [Field E] [NumberField E]

def Bnd (p : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Prop :=
  ∃ m : ℕ, m.Coprime p ∧ ∀ (i j : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
    Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * A i j)) Q) ≤ 1

/- English proof (translation)
Take `⟨a, ha, hA⟩` from `hA`. Take `⟨b, hb, hB⟩` from `hB`. Use `⟨a * b, Nat.Coprime.mul_left ha hb, fun i j Q => ?_⟩` and prove the remaining obligations. Set `φ : FiniteAdeleRing (𝓞 E) E →+* _` to `RestrictedProduct.evalRingHom _ Q`. Establish `hφ : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = φ x` using `fun _ => rfl`.

Rewrite using `[hφ, Matrix.mul_apply, Finset.mul_sum, map_sum]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `k _`. Establish `hsplit : ((a * b : ℕ) : FiniteAdeleRing (𝓞 E) E) * (A i k * B k j) = ((a : FiniteAdeleRing (𝓞 E) E) * A i k) * ((b : FiniteAdeleRing (𝓞 E) E) * B k j)` using `by push_cast; ring`. Rewrite using `[hsplit, map_mul, Valuation.map_mul, ← hφ, ← hφ]`.

Conclude with `mul_le_one' (hA i k Q) (hB k j Q)`.
-/
theorem bnd_mul (p n : ℕ) (A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hA : Bnd p A) (hB : Bnd p B) :
    Bnd p (A * B) := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨b, hb, hB⟩ := hB
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun i j Q => ?_⟩
  let φ : FiniteAdeleRing (𝓞 E) E →+* _ := RestrictedProduct.evalRingHom _ Q
  have hφ : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = φ x := fun _ => rfl
  rw [hφ, Matrix.mul_apply, Finset.mul_sum, map_sum]
  apply Valuation.map_sum_le
  intro k _
  have hsplit : ((a * b : ℕ) : FiniteAdeleRing (𝓞 E) E) * (A i k * B k j) =
      ((a : FiniteAdeleRing (𝓞 E) E) * A i k) * ((b : FiniteAdeleRing (𝓞 E) E) * B k j) := by
    push_cast; ring
  rw [hsplit, map_mul, Valuation.map_mul, ← hφ, ← hφ]
  exact mul_le_one' (hA i k Q) (hB k j Q)

end GlobalTheory.StdAtPrime
