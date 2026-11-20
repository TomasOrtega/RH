import Formalism.PeriodIntegrals.GoodTwo
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPA

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo.ChainBetweenPairs

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.F (scalePair MulStable)

/- English proof (translation)
Establish `hdiv : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4`. Establish `h4 : 4 ∣ d + 1` using `by omega`. Rewrite using `[Nat.cast_div h4 (by norm_num)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hI : Complex.I ^ 2 = -1` using `Complex.I_sq`.

Unfold `omegaK`. Rewrite using `[hdiv]`. Take the linear combination `(((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hs`.
-/
theorem omega_sq (d : ℕ) (hd : d % 4 = 3) :
    omegaK d ^ 2 = omegaK d - (((d + 1) / 4 : ℕ) : ℂ) := by
  have hdiv : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    have h4 : 4 ∣ d + 1 := by omega
    rw [Nat.cast_div h4 (by norm_num)]
    push_cast
    ring
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    rfl
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omegaK
  rw [hdiv]
  linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hs

/- English proof (translation)
Unfold `omegaK`. Simplify using `[map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_omega (d : ℕ) : conj (omegaK d) = 1 - omegaK d := by
  unfold omegaK
  simp [map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/- English proof (translation)
Rewrite using `[← zsmul_eq_mul]`. Conclude with `zsmul_mem hz n`.
-/
theorem int_mul_mem (L : PeriodPair) (n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    (n : ℂ) * z ∈ L.lattice := by
  rw [← zsmul_eq_mul]
  exact zsmul_mem hz n

/- English proof (translation)
Establish `h` using `int_mul_mem L (2 ^ i) hz`. Move the coercions through the operations in `at h`. Conclude with `h`.
-/
theorem pow_two_mul_mem (L : PeriodPair) (i : ℕ) {z : ℂ} (hz : z ∈ L.lattice) :
    (2 : ℂ) ^ i * z ∈ L.lattice := by
  have h := int_mul_mem L (2 ^ i) hz
  push_cast at h
  exact h

/- English proof (translation)
Rewrite using `[add_mul, mul_assoc]`. Conclude with `add_mem (int_mul_mem L m hz) (int_mul_mem L n (hL z hz))`.
-/
theorem stab (d : ℕ) (L : PeriodPair) (hL : HasCMBy d L) (m n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    ((m : ℂ) + n * omegaK d) * z ∈ L.lattice := by
  rw [add_mul, mul_assoc]
  exact add_mem (int_mul_mem L m hz) (int_mul_mem L n (hL z hz))

/- English proof (translation)
Introduce `hS`. Take `⟨t, N, ht, -, -⟩` from `Formalism.L2.Th1.F.mulStableIntegral L _ hS`. Simplify using `only [map_div₀, map_add, map_mul, map_intCast, map_ofNat, conj_omega] at ht`. Establish `h2 : ((2 * m + n : ℤ) : ℂ) = ((2 * t : ℤ) : ℂ)`. Use `push_cast`.

Take the linear combination `2 * ht`. Establish `h3 : 2 * m + n = 2 * t` using `by exact_mod_cast h2`. Take `⟨k, rfl⟩` from `hn`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_half (d : ℕ) (L : PeriodPair) (m n : ℤ) (hn : Odd n) :
    ¬ MulStable L (((m : ℂ) + n * omegaK d) / 2) := by
  intro hS
  obtain ⟨t, N, ht, -, -⟩ := Formalism.L2.Th1.F.mulStableIntegral L _ hS
  simp only [map_div₀, map_add, map_mul, map_intCast, map_ofNat, conj_omega] at ht
  have h2 : ((2 * m + n : ℤ) : ℂ) = ((2 * t : ℤ) : ℂ) := by
    push_cast
    linear_combination 2 * ht
  have h3 : 2 * m + n = 2 * t := by exact_mod_cast h2
  obtain ⟨k, rfl⟩ := hn
  omega

/- English proof (translation)
Take `⟨hp, hq⟩` from `h`. Take `⟨p', rfl⟩ : (2 : ℤ) ∣ p` from `(ZMod.intCast_zmod_eq_zero_iff_dvd p 2).mp hp`. Take `⟨q', rfl⟩ : (2 : ℤ) ∣ q` from `(ZMod.intCast_zmod_eq_zero_iff_dvd q 2).mp hq`. Establish `hw' : w = (p' : ℂ) * L.ω₁ + q' * L.ω₂`. Move the coercions through the operations in `at hw`.

Take the linear combination `(-1 / 2 : ℂ) * hw`. Rewrite using `[hw']`. Conclude with `add_mem (int_mul_mem L p' L.ω₁_mem_lattice) (int_mul_mem L q' L.ω₂_mem_lattice)`.
-/
theorem half_mem (L : PeriodPair) (w : ℂ) (p q : ℤ) (hw : (p : ℂ) * L.ω₁ + q * L.ω₂ = 2 * w)
    (h : (p : ZMod 2) = 0 ∧ (q : ZMod 2) = 0) : w ∈ L.lattice := by
  obtain ⟨hp, hq⟩ := h
  obtain ⟨p', rfl⟩ : (2 : ℤ) ∣ p := (ZMod.intCast_zmod_eq_zero_iff_dvd p 2).mp hp
  obtain ⟨q', rfl⟩ : (2 : ℤ) ∣ q := (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).mp hq
  have hw' : w = (p' : ℂ) * L.ω₁ + q' * L.ω₂ := by
    push_cast at hw
    linear_combination (-1 / 2 : ℂ) * hw
  rw [hw']
  exact add_mem (int_mul_mem L p' L.ω₁_mem_lattice) (int_mul_mem L q' L.ω₂_mem_lattice)

/- English proof (translation)
Assume the negation of the conclusion as `huv`. Apply `hπ` to reduce the goal to its premises. Take `⟨a, b, hab⟩` from `PeriodPair.mem_lattice.1 hu2`. Take `⟨c, e, hce⟩` from `PeriodPair.mem_lattice.1 hv2`. Establish `key : ∀ p q r s : ZMod 2, ¬ (p = 0 ∧ q = 0) → ¬ (r = 0 ∧ s = 0) → ¬ (p - r = 0 ∧ q - s = 0) → p * s - q * r ≠ 0` using `by decide`.

Establish `hdet : ((a * e - b * c : ℤ) : ZMod 2) ≠ 0`. Use `push_cast`. Use `key _ _ _ _ (fun h => hu3 (half_mem L u a b hab h)) (fun h => hv3 (half_mem L v c e hce h)) (fun h => huv (half_mem L (u - v) (a - c) (b - e) ?_ ?_))` and prove the remaining obligations. Use `push_cast`. Take the linear combination `hab - hce`.

Use `push_cast`. Conclude with `h`. Establish `hodd : Odd (a * e - b * c)`. Rewrite using `[← Int.not_even_iff_odd, even_iff_two_dvd]`. Introduce `h2`.

Conclude with `hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by exact_mod_cast h2))`. Take `⟨m, hm⟩` from `hodd`. Establish `hmC : (a : ℂ) * e - b * c = 2 * m + 1` using `by exact_mod_cast hm`. Establish `e1 : L.ω₁ / 2 = (e : ℂ) * u - b * v - m * L.ω₁`. Take the linear combination `((e : ℂ) / 2) * hab - ((b : ℂ) / 2) * hce - (L.ω₁ / 2) * hmC`.

Establish `e2 : L.ω₂ / 2 = (a : ℂ) * v - c * u - m * L.ω₂`. Take the linear combination `((a : ℂ) / 2) * hce - ((c : ℂ) / 2) * hab - (L.ω₂ / 2) * hmC`. Establish `h1 : π * (L.ω₁ / 2) ∈ L.lattice`. Establish `f : π * ((e : ℂ) * u - b * v - m * L.ω₁) = (e : ℂ) * (π * u) - b * (π * v) - m * (π * L.ω₁)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, f]`. Conclude with `sub_mem (sub_mem (int_mul_mem L e hu1) (int_mul_mem L b hv1)) (int_mul_mem L m (hπL _ L.ω₁_mem_lattice))`. Establish `h2 : π * (L.ω₂ / 2) ∈ L.lattice`. Establish `f : π * ((a : ℂ) * v - c * u - m * L.ω₂) = (a : ℂ) * (π * v) - c * (π * u) - m * (π * L.ω₂)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, f]`. Conclude with `sub_mem (sub_mem (int_mul_mem L a hv1) (int_mul_mem L c hu1)) (int_mul_mem L m (hπL _ L.ω₂_mem_lattice))`. Introduce `w hw`. Take `⟨p, q, rfl⟩` from `PeriodPair.mem_lattice.1 hw`. Establish `f : π / 2 * ((p : ℂ) * L.ω₁ + q * L.ω₂) = (p : ℂ) * (π * (L.ω₁ / 2)) + q * (π * (L.ω₂ / 2))`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[f]`. Conclude with `add_mem (int_mul_mem L p h1) (int_mul_mem L q h2)`.
-/
theorem two_tors (L : PeriodPair) (π : ℂ) (hπ : ¬ MulStable L (π / 2)) (hπL : MulStable L π)
    {u v : ℂ} (hu1 : π * u ∈ L.lattice) (hu2 : 2 * u ∈ L.lattice) (hu3 : u ∉ L.lattice)
    (hv1 : π * v ∈ L.lattice) (hv2 : 2 * v ∈ L.lattice) (hv3 : v ∉ L.lattice) :
    u - v ∈ L.lattice := by
  by_contra huv
  apply hπ
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 hu2
  obtain ⟨c, e, hce⟩ := PeriodPair.mem_lattice.1 hv2
  have key : ∀ p q r s : ZMod 2, ¬ (p = 0 ∧ q = 0) → ¬ (r = 0 ∧ s = 0) →
      ¬ (p - r = 0 ∧ q - s = 0) → p * s - q * r ≠ 0 := by decide
  have hdet : ((a * e - b * c : ℤ) : ZMod 2) ≠ 0 := by
    push_cast
    refine key _ _ _ _ (fun h => hu3 (half_mem L u a b hab h)) (fun h => hv3 (half_mem L v c e hce h))
      (fun h => huv (half_mem L (u - v) (a - c) (b - e) ?_ ?_))
    · push_cast
      linear_combination hab - hce
    · push_cast
      exact h
  have hodd : Odd (a * e - b * c) := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    exact hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by exact_mod_cast h2))
  obtain ⟨m, hm⟩ := hodd
  have hmC : (a : ℂ) * e - b * c = 2 * m + 1 := by exact_mod_cast hm
  have e1 : L.ω₁ / 2 = (e : ℂ) * u - b * v - m * L.ω₁ := by
    linear_combination ((e : ℂ) / 2) * hab - ((b : ℂ) / 2) * hce - (L.ω₁ / 2) * hmC
  have e2 : L.ω₂ / 2 = (a : ℂ) * v - c * u - m * L.ω₂ := by
    linear_combination ((a : ℂ) / 2) * hce - ((c : ℂ) / 2) * hab - (L.ω₂ / 2) * hmC
  have h1 : π * (L.ω₁ / 2) ∈ L.lattice := by
    have f : π * ((e : ℂ) * u - b * v - m * L.ω₁) = (e : ℂ) * (π * u) - b * (π * v) - m * (π * L.ω₁) := by
      ring
    rw [e1, f]
    exact sub_mem (sub_mem (int_mul_mem L e hu1) (int_mul_mem L b hv1))
      (int_mul_mem L m (hπL _ L.ω₁_mem_lattice))
  have h2 : π * (L.ω₂ / 2) ∈ L.lattice := by
    have f : π * ((a : ℂ) * v - c * u - m * L.ω₂) = (a : ℂ) * (π * v) - c * (π * u) - m * (π * L.ω₂) := by
      ring
    rw [e2, f]
    exact sub_mem (sub_mem (int_mul_mem L a hv1) (int_mul_mem L c hu1))
      (int_mul_mem L m (hπL _ L.ω₂_mem_lattice))
  intro w hw
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 hw
  have f : π / 2 * ((p : ℂ) * L.ω₁ + q * L.ω₂) = (p : ℂ) * (π * (L.ω₁ / 2)) + q * (π * (L.ω₂ / 2)) := by
    ring
  rw [f]
  exact add_mem (int_mul_mem L p h1) (int_mul_mem L q h2)

def S (L : PeriodPair) (π : ℂ) (i : ℕ) : Submodule ℤ ℂ where
  carrier := {z | π * z ∈ L.lattice ∧ (2 : ℂ) ^ i * z ∈ L.lattice}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [mul_add]; exact add_mem h1 h3, by rw [mul_add]; exact add_mem h2 h4⟩
  zero_mem' := by
    show π * 0 ∈ L.lattice ∧ (2 : ℂ) ^ i * 0 ∈ L.lattice
    simp
  smul_mem' := by
    rintro c z ⟨h1, h2⟩
    exact ⟨by rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1,
      by rw [mul_smul_comm]; exact Submodule.smul_mem _ c h2⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_S {L : PeriodPair} {π : ℂ} {i : ℕ} {z : ℂ} :
    z ∈ S L π i ↔ π * z ∈ L.lattice ∧ (2 : ℂ) ^ i * z ∈ L.lattice := Iff.rfl

end PI.GoodTwo.ChainBetweenPairs
