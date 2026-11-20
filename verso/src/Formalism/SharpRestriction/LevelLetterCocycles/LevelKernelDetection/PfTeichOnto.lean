import Formalism.SharpRestriction.LevelLetterCocycles.TeichOnto
import Mathlib.NumberTheory.Padics.Hensel

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.MainNotions.N.Ln03 Polynomial

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← PadicInt.mem_nonunits, mem_nonunits_iff]`.
-/
theorem teichOnto_toZMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← PadicInt.mem_nonunits, mem_nonunits_iff]

/- English proof (translation)
The claim follows from `le_antisymm (PadicInt.norm_le_one x) (not_lt.mp fun h' => h ((teichOnto_toZMod_eq_zero_iff x).mpr h'))`.
-/
theorem teichOnto_norm_eq_one {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) (h : PadicInt.toZMod x ≠ 0) :
    ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x) (not_lt.mp fun h' => h ((teichOnto_toZMod_eq_zero_iff x).mpr h'))

/- English proof (translation)
Introduce `a ha`. Establish `hp : p.Prime` using `Fact.out`. Use `set a₀ : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) with ha₀`. Establish `hres : PadicInt.toZMod a₀ = a` using `by rw [ha₀, map_natCast, ZMod.natCast_zmod_val]`. Use `set F : Polynomial ℤ_[p] := X ^ (p - 1) - 1 with hF`.

Establish `hFa : F.aeval a₀ = a₀ ^ (p - 1) - 1` using `by simp [hF]`. Establish `hF'a : F.derivative.aeval a₀ = ((p - 1 : ℕ) : ℤ_[p]) * a₀ ^ (p - 1 - 1)`. Simplify using `[hF, Polynomial.derivative_X_pow]`. Establish `h1 : ‖F.aeval a₀‖ < 1`. Rewrite using `[← teichOnto_toZMod_eq_zero_iff, hFa, map_sub, map_pow, hres, map_one, ZMod.pow_card_sub_one_eq_one ha, sub_self]`.

Establish `h2 : ‖F.derivative.aeval a₀‖ = 1`. Apply `teichOnto_norm_eq_one` to reduce the goal to its premises. Rewrite using `[hF'a, map_mul, map_pow, hres, map_natCast]`. Use `mul_ne_zero ?_ (pow_ne_zero _ ha)` and prove the remaining obligations. Rewrite using `[Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, neg_ne_zero]`.

Conclude with `one_ne_zero`. Take `⟨z, hz, hza, -, -⟩` from `hensels_lemma (F := F) (a := a₀) (by rw [h2, one_pow]; exact h1)`. Rewrite `hza` using `[h2]`. Establish `hzp : z ^ (p - 1) = 1`. Establish `: F.aeval z = z ^ (p - 1) - 1` using `by simp [hF]`.

Rewrite `hz` using `[this, sub_eq_zero]`. Conclude with `hz`. Establish `hzz : z * z ^ (p - 2) = 1`. Establish `h2p` using `hp.two_le`. Rewrite using `[← pow_succ', show p - 2 + 1 = p - 1 by omega, hzp]`.

Set `u : ℤ_[p]ˣ` to `⟨z, z ^ (p - 2), hzz, by rw [mul_comm]; exact hzz⟩`. Use `⟨⟨u, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hzp)⟩, ?_⟩` and prove the remaining obligations. Use `show PadicInt.toZMod z = a`. Establish `h3 : PadicInt.toZMod (z - a₀) = 0` using `(teichOnto_toZMod_eq_zero_iff _).mpr hza`. Rewrite `h3` using `[map_sub, sub_eq_zero, hres]`.

Conclude with `h3`.
-/
theorem teichOnto_holds (p : ℕ) [Fact p.Prime] : TeichOnto p := by
  intro a ha
  have hp : p.Prime := Fact.out
  set a₀ : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) with ha₀
  have hres : PadicInt.toZMod a₀ = a := by rw [ha₀, map_natCast, ZMod.natCast_zmod_val]
  set F : Polynomial ℤ_[p] := X ^ (p - 1) - 1 with hF
  have hFa : F.aeval a₀ = a₀ ^ (p - 1) - 1 := by simp [hF]
  have hF'a : F.derivative.aeval a₀ = ((p - 1 : ℕ) : ℤ_[p]) * a₀ ^ (p - 1 - 1) := by
    simp [hF, Polynomial.derivative_X_pow]
  have h1 : ‖F.aeval a₀‖ < 1 := by
    rw [← teichOnto_toZMod_eq_zero_iff, hFa, map_sub, map_pow, hres, map_one,
      ZMod.pow_card_sub_one_eq_one ha, sub_self]
  have h2 : ‖F.derivative.aeval a₀‖ = 1 := by
    apply teichOnto_norm_eq_one
    rw [hF'a, map_mul, map_pow, hres, map_natCast]
    refine mul_ne_zero ?_ (pow_ne_zero _ ha)
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, neg_ne_zero]
    exact one_ne_zero
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a₀) (by rw [h2, one_pow]; exact h1)
  rw [h2] at hza
  have hzp : z ^ (p - 1) = 1 := by
    have : F.aeval z = z ^ (p - 1) - 1 := by simp [hF]
    rw [this, sub_eq_zero] at hz
    exact hz
  have hzz : z * z ^ (p - 2) = 1 := by
    have h2p := hp.two_le
    rw [← pow_succ', show p - 2 + 1 = p - 1 by omega, hzp]
  let u : ℤ_[p]ˣ := ⟨z, z ^ (p - 2), hzz, by rw [mul_comm]; exact hzz⟩
  refine ⟨⟨u, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hzp)⟩, ?_⟩
  show PadicInt.toZMod z = a
  have h3 : PadicInt.toZMod (z - a₀) = 0 := (teichOnto_toZMod_eq_zero_iff _).mpr hza
  rw [map_sub, sub_eq_zero, hres] at h3
  exact h3

end Formalism.MainNotions.N.Ln03.Pf
