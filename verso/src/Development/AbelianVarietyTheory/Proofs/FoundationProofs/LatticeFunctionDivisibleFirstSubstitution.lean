import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Introduce `N l ν φ a b c d hdet hN hl y`. Take `⟨y1, y2⟩` from `y`. Establish `hNz : (N : ℤ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hcop : IsCoprime ((N : ℤ) * d) (l : ℤ)` using `⟨a, -(b * c), by linear_combination hdet⟩`. Simplify using `only [latF]`.

Distinguish the cases in `h1 : (N : ℤ) ∣ y1`. Take `⟨m, rfl⟩` from `h1`. Rewrite using `[if_pos (dvd_mul_right _ _)]`. Establish `hdiv : (N : ℤ) * m / N = m` using `Int.mul_ediv_cancel_left m hNz`. Simplify using `only [hdiv]`.

Establish `key : ((N : ℤ) * l ∣ N * m) ↔ ((l : ℤ) ∣ m)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(mul_dvd_mul_iff_left hNz).mp h`. Introduce `h`.

Conclude with `mul_dvd_mul_left _ h`. Establish `key2 : ((l : ℤ) ∣ m * (N * d) - y2 * (l * c)) ↔ ((l : ℤ) ∣ m)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : (l : ℤ) ∣ m * (N * d)`.

Use `dvd_add h (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)` as an intermediate fact. Simplify using `using this`. Conclude with `hcop.symm.dvd_of_dvd_mul_right h'`. Introduce `h`. Conclude with `dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)`.

Use `push_cast`. Distinguish the cases in `h2 : (l : ℤ) ∣ m`. Take `⟨m2, rfl⟩` from `h2`. Rewrite using `[if_pos ((key2).mpr (dvd_mul_right _ _)), if_pos (key.mpr (dvd_mul_right _ _))]`. Establish `hlz : (l : ℤ) ≠ 0` using `by exact_mod_cast hl.ne'`.

Establish `e1 : (l : ℤ) * m2 * (N * d) - y2 * (l * c) = l * (m2 * N * d - y2 * c)` using `by ring`. Rewrite using `[e1, Int.mul_ediv_cancel_left _ hlz]`. Simplify using `only [ch, one_mul, map_intCast]`. Use `congr 2`. Use `push_cast`.

Simplify using `[mul_comm]`. Use `push_cast`. Simplify using `[mul_comm]`. Rewrite using `[if_neg (fun h => h2 (key2.mp h)), if_neg (fun h => h2 (key.mp h))]`. Rewrite using `[if_neg h1, if_neg]`.

Introduce `h`. Move the coercions through the operations in `at h`. Conclude with `h1 (dvd_trans (dvd_mul_right _ _) h)`.
-/
theorem latF_rows_subst : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  intro N l ν φ a b c d hdet hN hl y
  obtain ⟨y1, y2⟩ := y
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcop : IsCoprime ((N : ℤ) * d) (l : ℤ) := ⟨a, -(b * c), by linear_combination hdet⟩
  simp only [latF]
  by_cases h1 : (N : ℤ) ∣ y1
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right _ _)]
    have hdiv : (N : ℤ) * m / N = m := Int.mul_ediv_cancel_left m hNz
    simp only [hdiv]
    have key : ((N : ℤ) * l ∣ N * m) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h; exact (mul_dvd_mul_iff_left hNz).mp h
      · intro h; exact mul_dvd_mul_left _ h
    have key2 : ((l : ℤ) ∣ m * (N * d) - y2 * (l * c)) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h
        have h' : (l : ℤ) ∣ m * (N * d) := by
          have := dvd_add h (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
          simpa using this
        exact hcop.symm.dvd_of_dvd_mul_right h'
      · intro h
        exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
    push_cast
    by_cases h2 : (l : ℤ) ∣ m
    · obtain ⟨m2, rfl⟩ := h2
      rw [if_pos ((key2).mpr (dvd_mul_right _ _)), if_pos (key.mpr (dvd_mul_right _ _))]
      have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      have e1 : (l : ℤ) * m2 * (N * d) - y2 * (l * c) = l * (m2 * N * d - y2 * c) := by ring
      rw [e1, Int.mul_ediv_cancel_left _ hlz]
      simp only [ch, one_mul, map_intCast]
      congr 2
      · push_cast
        simp [mul_comm]
      · push_cast
        simp [mul_comm]
    · rw [if_neg (fun h => h2 (key2.mp h)), if_neg (fun h => h2 (key.mp h))]
  · rw [if_neg h1, if_neg]
    intro h
    push_cast at h
    exact h1 (dvd_trans (dvd_mul_right _ _) h)

end GlobalTheory
