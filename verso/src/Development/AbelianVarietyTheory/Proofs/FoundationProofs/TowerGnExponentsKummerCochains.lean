import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumExpo

/- English proof (translation)
Introduce `p _ Ω _ _ T n m hm lz lq hz hq g hg`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Establish `h1 : (g (T.ζ (2 * n + k))) ^ (p ^ (2 * n + k)) = 1`. Rewrite using `[← map_pow, (T.prim _).pow_eq_one, map_one]`. Take `⟨i, -, hi⟩` from `(T.prim _).eq_pow_of_pow_eq_one h1`.

Establish `hqne` using `qq_ne T (2 * n + k)`. Establish `h2 : (g (T.qq (2 * n + k)) / T.qq (2 * n + k)) ^ (p ^ (2 * n + k)) = 1`. Rewrite using `[div_pow, ← map_pow, kummerTower_qq_pow_level_eq_q, AlgEquiv.commutes, ← kummerTower_qq_pow_level_eq_q T (2 * n + k), div_self (pow_ne_zero _ hqne)]`. Take `⟨j, -, hj⟩` from `(T.prim _).eq_pow_of_pow_eq_one h2`. Establish `hj' : g (T.qq (2 * n + k)) = T.ζ (2 * n + k) ^ j * T.qq (2 * n + k)`.

Rewrite using `[hj, div_mul_cancel₀ _ hqne]`. Establish `ez : T.ζ (2 * n + k) ^ (p ^ k) = T.ζ (2 * n)` using `zeta_pow T (2 * n) k`. Establish `eq' : T.qq (2 * n + k) ^ (p ^ k) = T.qq (2 * n)` using `qq_pow T (2 * n) k`. Establish `ezn : T.ζ (2 * n) ^ (p ^ n) = T.ζ n`. Use `zeta_pow T n n` as an intermediate fact.

Rewrite `this` using `[← two_mul]`. Then use the resulting hypothesis. Establish `gz : g (T.ζ (2 * n)) = T.ζ (2 * n) ^ i`. Rewrite using `[← ez, map_pow, ← hi, ← pow_mul, ← pow_mul, Nat.mul_comm i]`. Establish `gq : g (T.qq (2 * n)) = T.ζ (2 * n) ^ j * T.qq (2 * n)`. Rewrite using `[← eq', map_pow, hj', mul_pow, ← pow_mul, mul_comm j, pow_mul, ez]`.

Establish `kz` using `hz g hg`. Establish `kq` using `hq g hg`. Rewrite `kz` using `[gz, ← ezn, ← pow_mul, ← pow_succ]`. Rewrite `kq` using `[gq, ← ezn, ← pow_mul]`. Establish `kq'` using `mul_right_cancel₀ (qq_ne T (2 * n)) kq`.

Rewrite `kz`, `kq'` using `[GlobalTheory.K5.Basic.zeta_pow_eq_iff]`. Rewrite `kz`, `kq'` using `[Nat.modEq_iff_dvd]`. Take `⟨s, hs⟩` from `kz`. Take `⟨t, ht⟩` from `kq'`. Use `⟨i, j, -s, -t, hi.symm, hj', ?_, ?_⟩` and prove the remaining obligations.

Move the coercions through the operations in `at hs ⊢`. Take the linear combination `-hs`. Move the coercions through the operations in `at ht ⊢`. Take the linear combination `-ht`.
-/
theorem exponents : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  intro p _ Ω _ _ T n m hm lz lq hz hq g hg
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm

  have h1 : (g (T.ζ (2 * n + k))) ^ (p ^ (2 * n + k)) = 1 := by
    rw [← map_pow, (T.prim _).pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := (T.prim _).eq_pow_of_pow_eq_one h1
  have hqne := qq_ne T (2 * n + k)
  have h2 : (g (T.qq (2 * n + k)) / T.qq (2 * n + k)) ^ (p ^ (2 * n + k)) = 1 := by
    rw [div_pow, ← map_pow, kummerTower_qq_pow_level_eq_q, AlgEquiv.commutes, ← kummerTower_qq_pow_level_eq_q T (2 * n + k),
      div_self (pow_ne_zero _ hqne)]
  obtain ⟨j, -, hj⟩ := (T.prim _).eq_pow_of_pow_eq_one h2
  have hj' : g (T.qq (2 * n + k)) = T.ζ (2 * n + k) ^ j * T.qq (2 * n + k) := by
    rw [hj, div_mul_cancel₀ _ hqne]

  have ez : T.ζ (2 * n + k) ^ (p ^ k) = T.ζ (2 * n) := zeta_pow T (2 * n) k
  have eq' : T.qq (2 * n + k) ^ (p ^ k) = T.qq (2 * n) := qq_pow T (2 * n) k
  have ezn : T.ζ (2 * n) ^ (p ^ n) = T.ζ n := by
    have := zeta_pow T n n
    rwa [← two_mul] at this
  have gz : g (T.ζ (2 * n)) = T.ζ (2 * n) ^ i := by
    rw [← ez, map_pow, ← hi, ← pow_mul, ← pow_mul, Nat.mul_comm i]
  have gq : g (T.qq (2 * n)) = T.ζ (2 * n) ^ j * T.qq (2 * n) := by
    rw [← eq', map_pow, hj', mul_pow, ← pow_mul, mul_comm j, pow_mul, ez]
  have kz := hz g hg
  have kq := hq g hg
  rw [gz, ← ezn, ← pow_mul, ← pow_succ] at kz
  rw [gq, ← ezn, ← pow_mul] at kq
  have kq' := mul_right_cancel₀ (qq_ne T (2 * n)) kq
  rw [GlobalTheory.K5.Basic.zeta_pow_eq_iff] at kz kq'
  rw [Nat.modEq_iff_dvd] at kz kq'
  obtain ⟨s, hs⟩ := kz
  obtain ⟨t, ht⟩ := kq'
  refine ⟨i, j, -s, -t, hi.symm, hj', ?_, ?_⟩
  · push_cast at hs ⊢
    linear_combination -hs
  · push_cast at ht ⊢
    linear_combination -ht

end GlobalTheory.KumExpo
