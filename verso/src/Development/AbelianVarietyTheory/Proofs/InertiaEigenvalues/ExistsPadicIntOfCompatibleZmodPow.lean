import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ c hc`. Set `f : ∀ n : ℕ, Polynomial ℤ →+* ZMod (p ^ n)` to `fun n => Polynomial.eval₂RingHom (Int.castRingHom _) (c n)`. Establish `hf : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (f k₂) = f k₁`. Introduce `k₁ k₂ hk`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Simplify using `[f]`. Simplify `hc k₁ k₂ hk` using `[f]`. Use `⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun g : Polynomial ℤ →+* ZMod (p ^ n) => g Polynomial.X) (PadicInt.lift_spec hf n)`.

Simplify `h` using `[f]`.
-/
theorem exists_padicInt_of_compatible_zmod_pow :
    ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)),
      (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) →
      ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  intro p _ c hc
  let f : ∀ n : ℕ, Polynomial ℤ →+* ZMod (p ^ n) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) (c n)
  have hf : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply Polynomial.ringHom_ext
    · intro a
      simp [f]
    · simpa [f] using hc k₁ k₂ hk
  refine ⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩
  have h := congrArg (fun g : Polynomial ℤ →+* ZMod (p ^ n) => g Polynomial.X)
    (PadicInt.lift_spec hf n)
  simpa [f] using h

end GlobalTheory
