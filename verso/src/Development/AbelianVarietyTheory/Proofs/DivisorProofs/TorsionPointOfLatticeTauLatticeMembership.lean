import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.TorsMem

/- English proof (translation)
Establish `hN : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (NeZero.ne N)`. Establish `h1 : (tauPair τ).ω₁ = (τ : ℂ)` using `rfl`. Establish `h2 : (tauPair τ).ω₂ = 1` using `rfl`. Rewrite using `[PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, n, h⟩`. Rewrite `h` using `[h1, h2, eq_div_iff hN]`. Take `⟨k1, k2⟩` from `LinearIndependent.pair_iff.mp (tauPair τ).indep (((N : ℤ) * m - a : ℤ) : ℝ) (((N : ℤ) * n - b : ℤ) : ℝ) (by`. Rewrite using `[h1, h2, Complex.real_smul, Complex.real_smul]`. Use `push_cast`.

Take the linear combination `h)`. Normalize the coercions in `at k1 k2`. Conclude with `⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩`. Introduce and unpack `⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩`. Use `⟨m, n, ?_⟩` and prove the remaining obligations.

Rewrite using `[h1, h2, eq_div_iff hN]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem div_N_mem_tauPair_lattice_iff_dvd (N : ℕ) [NeZero N] (τ : ℍ) (a b : ℤ) :
    ((a : ℂ) * τ + (b : ℂ)) / N ∈ (tauPair τ).lattice ↔ (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    rw [h1, h2, eq_div_iff hN] at h
    obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.mp (tauPair τ).indep
      (((N : ℤ) * m - a : ℤ) : ℝ) (((N : ℤ) * n - b : ℤ) : ℝ) (by
        rw [h1, h2, Complex.real_smul, Complex.real_smul]
        push_cast
        linear_combination h)
    norm_cast at k1 k2
    exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    refine ⟨m, n, ?_⟩
    rw [h1, h2, eq_div_iff hN]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[div_N_mem_tauPair_lattice_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]`.
-/
theorem div_mem_iff (N : ℕ) [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + (v : ℂ)) / N ∈ (tauPair τ).lattice ↔ (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by
  rw [div_N_mem_tauPair_lattice_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

/- English proof (translation)
Introduce `N _ τ`. Establish `hN : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (NeZero.ne N)`. Establish `ht : ∀ x : Fin 2 → ZMod N, tors N τ x = ((((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ)) / N`. Introduce `x`. Simplify using `only [tors, Int.cast_natCast]`.

Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Establish `e : tors N τ x - tors N τ y = (((((x 0).val : ℤ) - (y 0).val : ℤ) : ℂ) * τ + ((((x 1).val : ℤ) - (y 1).val : ℤ) : ℂ)) / N`. Rewrite using `[ht, ht]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, div_mem_iff, funext_iff, Fin.forall_fin_two]`. Simplify using `[sub_eq_zero]`. Introduce `x y`. Establish `e : tors N τ (x + y) - (tors N τ x + tors N τ y) = (((((x + y) 0).val : ℤ) - (x 0).val - (y 0).val : ℤ) * (τ : ℂ) + (((((x + y) 1).val : ℤ) - (x 1).val - (y 1).val : ℤ) : ℂ)) / N`.

Rewrite using `[ht, ht, ht]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, div_mem_iff]`. Simplify using the standard rewrite rules.

Introduce `x`. Rewrite using `[ht, div_mem_iff, funext_iff, Fin.forall_fin_two]`. Simplify using the standard rewrite rules. Introduce `x`. Rewrite using `[PeriodPair.mem_lattice]`.

Use `⟨(x 0).val, (x 1).val, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ) * 1 = _`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts. Introduce `z hz`.

Take `⟨m, n, h⟩` from `PeriodPair.mem_lattice.mp hz`. Express the relevant statement in the definitionally equal form `(m : ℂ) * τ + n * 1 = N * z at h`. Use `⟨![(m : ZMod N), (n : ZMod N)], ?_⟩` and prove the remaining obligations. Establish `hz' : z = ((m : ℂ) * τ + (n : ℂ)) / N`. Rewrite using `[eq_div_iff hN]`.

Take the linear combination `-h`. Establish `e : z - tors N τ ![(m : ZMod N), (n : ZMod N)] = (((m - ((m : ZMod N)).val : ℤ) : ℂ) * τ + ((n - ((n : ZMod N)).val : ℤ) : ℂ)) / N`. Rewrite using `[hz', ht]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, div_mem_iff]`. Simplify using the standard rewrite rules.
-/
theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  intro N _ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : ∀ x : Fin 2 → ZMod N,
      tors N τ x = ((((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ)) / N := by
    intro x
    simp only [tors, Int.cast_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have e : tors N τ x - tors N τ y = (((((x 0).val : ℤ) - (y 0).val : ℤ) : ℂ) * τ
        + ((((x 1).val : ℤ) - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht]; push_cast; ring
    rw [e, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp [sub_eq_zero]
  · intro x y
    have e : tors N τ (x + y) - (tors N τ x + tors N τ y) =
        (((((x + y) 0).val : ℤ) - (x 0).val - (y 0).val : ℤ) * (τ : ℂ)
        + (((((x + y) 1).val : ℤ) - (x 1).val - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht, ht]; push_cast; ring
    rw [e, div_mem_iff]
    simp
  · intro x
    rw [ht, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp
  · intro x
    rw [PeriodPair.mem_lattice]
    refine ⟨(x 0).val, (x 1).val, ?_⟩
    change (((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ) * 1 = _
    rw [ht]
    field_simp
  · intro z hz
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hz
    change (m : ℂ) * τ + n * 1 = N * z at h
    refine ⟨![(m : ZMod N), (n : ZMod N)], ?_⟩
    have hz' : z = ((m : ℂ) * τ + (n : ℂ)) / N := by
      rw [eq_div_iff hN]
      linear_combination -h
    have e : z - tors N τ ![(m : ZMod N), (n : ZMod N)] =
        (((m - ((m : ZMod N)).val : ℤ) : ℂ) * τ + ((n - ((n : ZMod N)).val : ℤ) : ℂ)) / N := by
      rw [hz', ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    rw [e, div_mem_iff]
    simp

end GlobalTheory.WpFam.TorsMem
