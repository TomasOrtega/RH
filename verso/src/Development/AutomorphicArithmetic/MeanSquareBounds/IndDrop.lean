import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim
import Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Introduce `N₀ q M ξ N _ χ hN₀ hq hq2 hqN₀ hM hχ`. Take `⟨hχp, hind⟩` from `hχ`. Use `haveI : NeZero N₀ := ⟨hN₀.ne'⟩`. Use `haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩`. Use `haveI : NeZero q := ⟨hq.ne_zero⟩`.

Establish `hqf : ¬ q ∣ ξ.conductor` using `fun h => hqN₀ (h.trans ξ.conductor_dvd_level)`. Take `⟨ψ, hψ, -, hψeq⟩` from `twist_prim ξ.conductor q ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqf`. Establish `hprim : ∀ n : ℕ, n.Coprime N₀ → ξ n = ξ.primitiveCharacter n`. Introduce `n hn`. Establish `h` using `DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)`.

Rewrite `h` using `[DirichletCharacter.changeLevel_primitiveCharacter]`. Rewrite `h` using `[Int.cast_natCast, Int.cast_natCast]`. Conclude with `h`. Establish `heq` using `ind_unique N (ξ.conductor * q) (M * N₀ * q) χ ψ (mul_ne_zero (mul_ne_zero hM hN₀.ne') hq.ne_zero) hχp hψ (fun n hn => by`. Rewrite using `[hind n (Nat.Coprime.coprime_dvd_right (Dvd.intro (N₀ * q) (by ring)) hn), hψeq]`.

Simplify using `only`. Rewrite using `[hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (M * q) (by ring)) hn)])`. Take `⟨hN, hχψ⟩` from `Sigma.mk.inj_iff.1 heq`. Substitute `hN` using the available equality. Establish `hc : χ = ψ` using `eq_of_heq hχψ`.

Substitute `hc` using the available equality. Use `⟨hχp, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[hψeq]`. Simplify using `only`. Rewrite using `[hprim n (Nat.Coprime.coprime_dvd_right (dvd_mul_right N₀ q) hn)]`.
-/
theorem ind_drop :
    ∀ (N₀ q M : ℕ) (ξ : DirichletCharacter ℂ N₀) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 0 < N₀ → q.Prime → q ≠ 2 → ¬ q ∣ N₀ → M ≠ 0 →
      Ind χ (fun n => ξ n * J q n) M → Ind χ (fun n => ξ n * J q n) (N₀ * q) := by
  intro N₀ q M ξ N _ χ hN₀ hq hq2 hqN₀ hM hχ
  obtain ⟨hχp, hind⟩ := hχ
  haveI : NeZero N₀ := ⟨hN₀.ne'⟩
  haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqf : ¬ q ∣ ξ.conductor := fun h => hqN₀ (h.trans ξ.conductor_dvd_level)
  obtain ⟨ψ, hψ, -, hψeq⟩ :=
    twist_prim ξ.conductor q ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqf
  have hprim : ∀ n : ℕ, n.Coprime N₀ → ξ n = ξ.primitiveCharacter n := by
    intro n hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter
      ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have heq := ind_unique N (ξ.conductor * q) (M * N₀ * q) χ ψ
    (mul_ne_zero (mul_ne_zero hM hN₀.ne') hq.ne_zero) hχp hψ (fun n hn => by
      rw [hind n (Nat.Coprime.coprime_dvd_right (Dvd.intro (N₀ * q) (by ring)) hn), hψeq]
      dsimp only
      rw [hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (M * q) (by ring)) hn)])
  obtain ⟨hN, hχψ⟩ := Sigma.mk.inj_iff.1 heq
  subst hN
  have hc : χ = ψ := eq_of_heq hχψ
  subst hc
  refine ⟨hχp, fun n hn => ?_⟩
  rw [hψeq]
  dsimp only
  rw [hprim n (Nat.Coprime.coprime_dvd_right (dvd_mul_right N₀ q) hn)]

end QH
