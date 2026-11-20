import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.CountA

open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Establish `hint : IsIntegral (ZMod g) x` using `Algebra.IsIntegral.isIntegral x`. Establish `hfr` using `IntermediateField.adjoin.finrank hint`. Establish `: FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {x})` using `IntermediateField.adjoin.finiteDimensional hint`. Establish `: Finite (IntermediateField.adjoin (ZMod g) {x})` using `Module.finite_of_finite (ZMod g)`. Set `_` to `Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})`.

Establish `hc : Fintype.card (IntermediateField.adjoin (ZMod g) {x}) = g ^ (minpoly (ZMod g) x).natDegree`. Rewrite using `[Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod g), Nat.card_zmod, hfr]`. Establish `h` using `FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self (ZMod g) x⟩ : IntermediateField.adjoin (ZMod g) {x})`. Rewrite `h` using `[hc]`. Conclude with `congrArg Subtype.val h`.
-/
theorem frob_fix (x : Fbar g) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hfr := IntermediateField.adjoin.finrank hint
  have : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let _ := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  have hc : Fintype.card (IntermediateField.adjoin (ZMod g) {x}) =
      g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod g), Nat.card_zmod, hfr]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self (ZMod g) x⟩ :
      IntermediateField.adjoin (ZMod g) {x})
  rw [hc] at h
  exact congrArg Subtype.val h

def Good (c : (ZMod g)ˣ) (P : (ZMod g)[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ j : ℕ,
    P ∣ X ^ (ℓ ^ j) - C ((c : ZMod g) ^ (ℓ ^ j))

/- English proof (translation)
Take `⟨q, rfl⟩` from `h`. Simplify using `[hz]`.
-/
theorem aeval_eq_zero_of_dvd' {P Q : (ZMod g)[X]} (h : P ∣ Q) {z : Fbar g}
    (hz : aeval z P = 0) : aeval z Q = 0 := by
  obtain ⟨q, rfl⟩ := h
  simp [hz]

/- English proof (translation)
Take `⟨hmon, hirr, ℓ, hℓ, j, hdvd⟩` from `hP`. Use `set c' := algebraMap (ZMod g) (Fbar g) (c : ZMod g) with hc'`. Establish `hc0 : c' ≠ 0`. Rewrite using `[hc']`. Conclude with `(_root_.map_ne_zero _).2 c.ne_zero`.

Establish `hz0 : aeval z P = 0`. Rewrite `hz` using `[mem_roots_map hmon.ne_zero]`. Rewrite using `[aeval_def]` and apply the resulting hypothesis. Establish `hmin : P = minpoly (ZMod g) z` using `minpoly.eq_of_irreducible_of_monic hirr hz0 hmon`. Establish `hfix : z ^ (g ^ P.natDegree) = z` using `by rw [hmin]; exact frob_fix z`.

Establish `hℓj : z ^ (ℓ ^ j) = c' ^ (ℓ ^ j)`. Use `aeval_eq_zero_of_dvd' hdvd hz0` as an intermediate fact. Simplify using `only [map_sub, map_pow, aeval_X, aeval_C] at this`. Rewrite `this` using `[sub_eq_zero]`. Conclude with `this`.

Establish `hzne : z ≠ 0`. Introduce `h0`. Rewrite `hℓj` using `[h0, zero_pow (pow_pos hℓ.pos j).ne']`. Conclude with `pow_ne_zero _ hc0 hℓj.symm`. Establish `hcfix : c' ^ (g ^ P.natDegree) = c'`.

Rewrite using `[hc', ← map_pow, ZMod.pow_card_pow]`. Use `set y := z * c'⁻¹ with hy`. Establish `hy0 : y ≠ 0` using `mul_ne_zero hzne (inv_ne_zero hc0)`. Establish `hyfix : y ^ (g ^ P.natDegree) = y`. Rewrite using `[hy, mul_pow, inv_pow, hfix, hcfix]`.

Establish `hpos : 1 ≤ g ^ P.natDegree` using `Nat.one_le_pow _ _ (Fact.out : g.Prime).pos`. Use `⟨?_, ℓ, hℓ, j, ?_⟩` and prove the remaining obligations. Establish `h2 : y ^ (g ^ P.natDegree - 1) * y = 1 * y`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hpos, hyfix, one_mul]`. Conclude with `mul_right_cancel₀ hy0 h2`.

Rewrite using `[hy, mul_pow, inv_pow, hℓj, mul_inv_cancel₀ (pow_ne_zero _ hc0)]`.
-/
theorem good_root (c : (ZMod g)ˣ) (P : (ZMod g)[X]) (hP : Good c P) (z : Fbar g)
    (hz : z ∈ (P.map (algebraMap (ZMod g) (Fbar g))).roots) :
    (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (g ^ P.natDegree - 1) = 1 ∧
      ∃ ℓ, ℓ.Prime ∧ ∃ j, (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (ℓ ^ j) = 1 := by
  obtain ⟨hmon, hirr, ℓ, hℓ, j, hdvd⟩ := hP
  set c' := algebraMap (ZMod g) (Fbar g) (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := by
    rw [hc']; exact (_root_.map_ne_zero _).2 c.ne_zero
  have hz0 : aeval z P = 0 := by
    rw [mem_roots_map hmon.ne_zero] at hz
    rwa [aeval_def]
  have hmin : P = minpoly (ZMod g) z := minpoly.eq_of_irreducible_of_monic hirr hz0 hmon
  have hfix : z ^ (g ^ P.natDegree) = z := by rw [hmin]; exact frob_fix z
  have hℓj : z ^ (ℓ ^ j) = c' ^ (ℓ ^ j) := by
    have := aeval_eq_zero_of_dvd' hdvd hz0
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    rw [sub_eq_zero] at this
    exact this
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hℓ.pos j).ne'] at hℓj
    exact pow_ne_zero _ hc0 hℓj.symm
  have hcfix : c' ^ (g ^ P.natDegree) = c' := by
    rw [hc', ← map_pow, ZMod.pow_card_pow]
  set y := z * c'⁻¹ with hy
  have hy0 : y ≠ 0 := mul_ne_zero hzne (inv_ne_zero hc0)
  have hyfix : y ^ (g ^ P.natDegree) = y := by
    rw [hy, mul_pow, inv_pow, hfix, hcfix]
  have hpos : 1 ≤ g ^ P.natDegree := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
  refine ⟨?_, ℓ, hℓ, j, ?_⟩
  · have h2 : y ^ (g ^ P.natDegree - 1) * y = 1 * y := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hyfix, one_mul]
    exact mul_right_cancel₀ hy0 h2
  · rw [hy, mul_pow, inv_pow, hℓj, mul_inv_cancel₀ (pow_ne_zero _ hc0)]

end PI.SqfRootShift.W
