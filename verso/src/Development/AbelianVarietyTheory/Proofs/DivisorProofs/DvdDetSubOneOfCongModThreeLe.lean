import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open GlobalTheory.Poinc
open GlobalTheory
open Classical

/- English proof (translation)
Use `set b := Module.Free.chooseBasis ℤ X`. Establish `hdet : LinearMap.det (γ : X →ₗ[ℤ] X) = (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)).det` using `(LinearMap.det_toMatrix b _).symm`. Establish `hmap : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)) = 1`. Use extensionality with `i j`. Take `⟨w, hw⟩` from `hγ (b j)`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hw, map_add, map_nsmul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Matrix.one_apply]`. Rewrite using `[Finsupp.single_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, add_zero]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Establish `hcast : ((LinearMap.det (γ : X →ₗ[ℤ] X) : ℤ) : ZMod L) = 1`. Rewrite using `[hdet]`. Use `RingHom.map_det (Int.castRingHom (ZMod L)) (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X))` as an intermediate fact. Simplify using `only [eq_intCast] at this`.

Rewrite using `[this, hmap, Matrix.det_one]`. Establish `hdvd : (L : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[hcast, sub_self]`.

Break down `Int.isUnit_iff.mp (LinearEquiv.isUnit_det' γ) with h | h` into its components or cases. Rewrite using `[h, sub_self]`. Conclude with `dvd_zero _`. It suffices to derive a contradiction. Rewrite `hdvd` using `[h]`.

Establish `h2 : (L : ℤ) ∣ 2`. Establish `: (2 : ℤ) = -(-1 - 1)` using `by norm_num`. Rewrite using `[this]`. Conclude with `(dvd_neg).2 hdvd`. Establish `: L ∣ 2` using `by exact_mod_cast h2`.

Use `Nat.le_of_dvd (by norm_num) this` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L N : ℕ) (hL : 3 ≤ L)
    (γ : X ≃ₗ[ℤ] X) (hγ : ∀ x, CongMod L (γ x) x) : (N : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
  set b := Module.Free.chooseBasis ℤ X
  have hdet : LinearMap.det (γ : X →ₗ[ℤ] X) = (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)).det :=
    (LinearMap.det_toMatrix b _).symm
  have hmap : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)) = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hγ (b j)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hw,
      map_add, map_nsmul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Matrix.one_apply]
    rw [Finsupp.single_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, add_zero]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcast : ((LinearMap.det (γ : X →ₗ[ℤ] X) : ℤ) : ZMod L) = 1 := by
    rw [hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod L)) (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X))
    simp only [eq_intCast] at this
    rw [this, hmap, Matrix.det_one]
  have hdvd : (L : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast, sub_self]
  rcases Int.isUnit_iff.mp (LinearEquiv.isUnit_det' γ) with h | h
  · rw [h, sub_self]; exact dvd_zero _
  · exfalso
    rw [h] at hdvd
    have h2 : (L : ℤ) ∣ 2 := by
      have : (2 : ℤ) = -(-1 - 1) := by norm_num
      rw [this]; exact (dvd_neg).2 hdvd
    have : L ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
