import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsUnitAddMem

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Take `⟨z, rfl⟩` from `h`. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)`.
-/
private theorem norm_le_of_dvd' {l : ℕ} [Fact l.Prime] {x y : ℤ_[l]} (h : x ∣ y) : ‖y‖ ≤ ‖x‖ := by
  obtain ⟨z, rfl⟩ := h
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)

/- English proof (translation)
Establish `h1 : x ∣ y` using `IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.le`. Establish `h2 : y ∣ x` using `IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.ge`. Conclude with `le_antisymm (norm_le_of_dvd' h2) (norm_le_of_dvd' h1)`.
-/
private theorem norm_eq_of_addVal {l : ℕ} [Fact l.Prime] {x y : ℤ_[l]}
    (h : IsDiscreteValuationRing.addVal ℤ_[l] x = IsDiscreteValuationRing.addVal ℤ_[l] y) :
    ‖x‖ = ‖y‖ := by
  have h1 : x ∣ y := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.le
  have h2 : y ∣ x := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.ge
  exact le_antisymm (norm_le_of_dvd' h2) (norm_le_of_dvd' h1)

/- English proof (translation)
Introduce `l _ u c hc`. Take `⟨hv, hc1, hc2⟩` from `hc`. Establish `hval1 : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1` using `IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p`. Establish `hl : (l : ℤ_[l]) ∣ u - 1`. Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, hval1]`.

Simplify using `only [vl] at hv`. Rewrite using `[hv]`. Conclude with `hc1` after adjusting the coercions. Establish `hn1 : ‖u - 1‖ < 1` using `(PadicInt.norm_lt_one_iff_dvd _).2 hl`. Establish `hu : ‖u‖ = 1`.

Use `PadicInt.norm_eq_of_norm_add_lt_right (z1 := u) (z2 := -1) (by rw [norm_neg, norm_one, ← sub_eq_add_neg]; exact hn1)` as an intermediate fact. Rewrite `this` using `[norm_neg, norm_one]`. Then use the resulting hypothesis. Use `⟨hu, hl, ?_⟩` and prove the remaining obligations. Introduce `j a b`. Establish `hunit : IsUnit u` using `PadicInt.isUnit_iff.2 hu`.

Use `set v := hunit.unit with hvdef`. Establish `hvu : (v : ℤ_[l]) = u` using `hunit.unit_spec`. Establish `hvmem : v ∈ abelian₂.oneUnits ℤ_[l]` using `by show (v : ℤ_[l]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, hvu]`. Conclude with `hn1`.

Set `U : abelian₂.oneUnits ℤ_[l]` to `⟨v, hvmem⟩`. Use `set n : ℤ := ((l ^ j * a : ℕ) : ℤ) - ((l ^ j * b : ℕ) : ℤ) with hndef`. Establish `hlm : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`.

Establish `hptU : IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U) = c`. Rewrite using `[abelian₂.coe_pt]`. Simplify using `only [vl] at hv`. Rewrite using `[show ((U : ℤ_[l]ˣ) : ℤ_[l]) = u from hvu]`. Conclude with `hv`.

Establish `hcond : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) < ↑(l - 1) * IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U)`. Rewrite using `[hval1, hptU]`. Establish `hlt : 1 < (l - 1) * c`. Establish `hp` using `(Fact.out : l.Prime).two_le`. Break down `Nat.lt_or_ge l 3 with h | h` into its components or cases.

Establish `h2 : l = 2` using `by omega`. Use `hc2 h2` as an intermediate fact. Substitute `h2` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `h3 : 2 ≤ l - 1` using `by omega`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hlt` after adjusting the coercions. Establish `key` using `abelian₂.lte ℤ_[l] l Fact.out hlm U hcond n`. Establish `hfac : (u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b = (u ^ l ^ j) ^ b * ↑(abelian₂.pt (U ^ n))`. Rewrite using `[abelian₂.coe_pt]`.

Establish `h1 : ((U ^ n : abelian₂.oneUnits ℤ_[l]) : ℤ_[l]ˣ) = v ^ n` using `rfl`. Establish `h2 : v ^ ((l ^ j * a : ℕ) : ℤ) = v ^ ((l ^ j * b : ℕ) : ℤ) * v ^ n`. Rewrite using `[← zpow_add]`. Use `congr 1`. Rewrite using `[hndef]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ∀ k : ℕ, (u ^ l ^ j) ^ k = ((v ^ ((l ^ j * k : ℕ) : ℤ) : ℤ_[l]ˣ) : ℤ_[l])`. Introduce `k`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, hvu, pow_mul]`. Rewrite using `[h1, h3 a, h3 b, h2, Units.val_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfac, norm_mul, norm_pow, norm_pow, hu, one_pow, one_pow, one_mul]`. Rewrite using `[norm_eq_of_addVal (y := (l : ℤ_[l]) ^ (j + c) * ((a : ℤ_[l]) - (b : ℤ_[l])))]`. Rewrite using `[norm_mul, PadicInt.norm_p_pow, zpow_neg, zpow_natCast]`. Establish `hcast : ((n : ℤ) : ℤ_[l]) = (l : ℤ_[l]) ^ j * ((a : ℤ_[l]) - (b : ℤ_[l]))`.

Rewrite using `[hndef]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, hptU, hcast, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hval1]`. Simplify using `only [nsmul_eq_mul, mul_one]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.PropA.lteNorm :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ‖u‖ = 1 ∧ (l : ℤ_[l]) ∣ u - 1 ∧
      ∀ j a b : ℕ, ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖ = ((l : ℝ) ^ (j + c))⁻¹ * ‖(a : ℤ_[l]) - b‖ := by
  intro l _ u c hc
  obtain ⟨hv, hc1, hc2⟩ := hc
  have hval1 : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p
  have hl : (l : ℤ_[l]) ∣ u - 1 := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hval1]
    simp only [vl] at hv
    rw [hv]
    exact_mod_cast hc1
  have hn1 : ‖u - 1‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).2 hl
  have hu : ‖u‖ = 1 := by
    have := PadicInt.norm_eq_of_norm_add_lt_right (z1 := u) (z2 := -1)
      (by rw [norm_neg, norm_one, ← sub_eq_add_neg]; exact hn1)
    rwa [norm_neg, norm_one] at this
  refine ⟨hu, hl, ?_⟩
  intro j a b
  have hunit : IsUnit u := PadicInt.isUnit_iff.2 hu
  set v := hunit.unit with hvdef
  have hvu : (v : ℤ_[l]) = u := hunit.unit_spec
  have hvmem : v ∈ abelian₂.oneUnits ℤ_[l] := by
    show (v : ℤ_[l]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l]
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, hvu]
    exact hn1
  let U : abelian₂.oneUnits ℤ_[l] := ⟨v, hvmem⟩
  set n : ℤ := ((l ^ j * a : ℕ) : ℤ) - ((l ^ j * b : ℕ) : ℤ) with hndef
  have hlm : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hptU : IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U) = c := by
    rw [abelian₂.coe_pt]
    simp only [vl] at hv
    rw [show ((U : ℤ_[l]ˣ) : ℤ_[l]) = u from hvu]
    exact hv
  have hcond : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) <
      ↑(l - 1) * IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U) := by
    rw [hval1, hptU]
    have hlt : 1 < (l - 1) * c := by
      have hp := (Fact.out : l.Prime).two_le
      rcases Nat.lt_or_ge l 3 with h | h
      · have h2 : l = 2 := by omega
        have := hc2 h2
        subst h2
        omega
      · have h3 : 2 ≤ l - 1 := by omega
        calc 1 < 2 * 1 := by norm_num
          _ ≤ (l - 1) * c := Nat.mul_le_mul h3 hc1
    exact_mod_cast hlt
  have key := abelian₂.lte ℤ_[l] l Fact.out hlm U hcond n
  have hfac : (u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b = (u ^ l ^ j) ^ b * ↑(abelian₂.pt (U ^ n)) := by
    rw [abelian₂.coe_pt]
    have h1 : ((U ^ n : abelian₂.oneUnits ℤ_[l]) : ℤ_[l]ˣ) = v ^ n := rfl
    have h2 : v ^ ((l ^ j * a : ℕ) : ℤ) = v ^ ((l ^ j * b : ℕ) : ℤ) * v ^ n := by
      rw [← zpow_add]
      congr 1
      rw [hndef]
      ring
    have h3 : ∀ k : ℕ, (u ^ l ^ j) ^ k = ((v ^ ((l ^ j * k : ℕ) : ℤ) : ℤ_[l]ˣ) : ℤ_[l]) := by
      intro k
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hvu, pow_mul]
    rw [h1, h3 a, h3 b, h2, Units.val_mul]
    ring
  rw [hfac, norm_mul, norm_pow, norm_pow, hu, one_pow, one_pow, one_mul]
  rw [norm_eq_of_addVal (y := (l : ℤ_[l]) ^ (j + c) * ((a : ℤ_[l]) - (b : ℤ_[l])))]
  · rw [norm_mul, PadicInt.norm_p_pow, zpow_neg, zpow_natCast]
  · have hcast : ((n : ℤ) : ℤ_[l]) = (l : ℤ_[l]) ^ j * ((a : ℤ_[l]) - (b : ℤ_[l])) := by
      rw [hndef]
      push_cast
      ring
    rw [key, hptU, hcast, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hval1]
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    ring
