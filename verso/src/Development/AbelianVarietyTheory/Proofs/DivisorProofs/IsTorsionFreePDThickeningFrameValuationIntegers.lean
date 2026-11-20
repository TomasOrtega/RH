import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrameIntegers

/- English proof (translation)
Introduce `p hp C _ _ _ v O _ _ hnu _ _ hv`. Establish `hp0 : p ≠ 0` using `hp.out.ne_zero`. Establish `hpC : (p : C) ≠ 0` using `Nat.cast_ne_zero.mpr hp0`. Establish `hmapp : algebraMap O C (p : O) = (p : C)` using `map_natCast _ _`. Establish `hvp1 : v (p : C) < 1`.

Establish `h1` using `hv.map_le_one (p : O)`. Rewrite `h1` using `[hmapp]`. Break down `lt_or_eq_of_le h1 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (hv.isUnit_of_one (by rw [hmapp]; exact Ne.isUnit hpC) (by rw [hmapp]; exact h)) hnu.out`.

Establish `hint : ∀ z : ℤ, v (z : C) ≤ 1`. Introduce `z`. Use `hv.map_le_one (z : O)` as an intermediate fact. Rewrite `this` using `[map_intCast]`. Then use the resulting hypothesis. Use `⟨Function.surjective_id, hv.hom_inj, ?_, Ne.isUnit hpC, ?_, ?_, ?_, inferInstance⟩` and prove the remaining obligations.

Introduce `q`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, v (p : C) ^ k * v q ≤ 1 := by`. Distinguish the cases in `hq : v q = 0`. Conclude with `⟨0, by simp [hq]⟩`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (inv_pos.mpr (pos_iff_ne_zero.mpr hq)) hvp1`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hle : v ((p : C) ^ k * q) ≤ 1` using `by rw [map_mul, map_pow]; exact hk`. Take `⟨b, hb⟩` from `hv.exists_of_le_one hle`. Conclude with `⟨k, b, hb.symm⟩`.

Introduce `n hn`. Establish `hB : (n : C) * (Nat.gcdA n p : C) + (p : C) * (Nat.gcdB n p : C) = 1`. Establish `h` using `Nat.gcd_eq_gcd_ab n p`. Rewrite `h` using `[Nat.Coprime.gcd_eq_one hn]`. Conclude with `h.symm` after adjusting the coercions.

Establish `hvn : v (n : C) = 1`. Establish `h1 : v (n : C) ≤ 1` using `by exact_mod_cast hint n`. Assume the negation of the conclusion as `hne`. Establish `hlt : v (n : C) < 1` using `lt_of_le_of_ne h1 hne`. Establish `a1 : v ((n : C) * (Nat.gcdA n p : C)) < 1`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt`. Establish `a2 : v ((p : C) * (Nat.gcdB n p : C)) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hvp1`.

Use `Valuation.map_add_lt v a1 a2` as an intermediate fact. Rewrite `this` using `[hB, map_one]`. Conclude with `lt_irrefl _ this`. Establish `hnC : (n : C) ≠ 0`. Introduce `h`.

Rewrite `hvn` using `[h, map_zero]`. Conclude with `zero_ne_one hvn`. Establish `hmapn : algebraMap O C (n : O) = (n : C)` using `map_natCast _ _`. Conclude with `hv.isUnit_of_one (by rw [hmapn]; exact Ne.isUnit hnC) (by rw [hmapn]; exact hvn)`. Introduce `x hx`.

Simplify using `only [RingHom.id_apply] at hx`. Substitute `hx` using the available equality. Conclude with `⟨0, rfl, by simp [hp0]⟩`. Introduce `a ha`. Establish `hpO : (p : O) ≠ 0`.

Introduce `h`. Apply `hpC` to reduce the goal to its premises. Rewrite using `[← hmapp, h, map_zero]`. Conclude with `(mul_eq_zero.mp ha).resolve_left hpO`.
-/
theorem isFrame_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → IsFrame p C (RingHom.id O) := by
  intro p hp C _ _ _ v O _ _ hnu _ _ hv
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hmapp : algebraMap O C (p : O) = (p : C) := map_natCast _ _
  have hvp1 : v (p : C) < 1 := by
    have h1 := hv.map_le_one (p : O)
    rw [hmapp] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (hv.isUnit_of_one (by rw [hmapp]; exact Ne.isUnit hpC) (by rw [hmapp]; exact h)) hnu.out
  have hint : ∀ z : ℤ, v (z : C) ≤ 1 := by
    intro z
    have := hv.map_le_one (z : O)
    rwa [map_intCast] at this
  refine ⟨Function.surjective_id, hv.hom_inj, ?_, Ne.isUnit hpC, ?_, ?_, ?_, inferInstance⟩
  · intro q
    obtain ⟨k, hk⟩ : ∃ k : ℕ, v (p : C) ^ k * v q ≤ 1 := by
      by_cases hq : v q = 0
      · exact ⟨0, by simp [hq]⟩
      · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (pos_iff_ne_zero.mpr hq)) hvp1
        refine ⟨k, ?_⟩
        calc v (p : C) ^ k * v q ≤ (v q)⁻¹ * v q := mul_le_mul_of_nonneg_right hk.le zero_le
          _ = 1 := inv_mul_cancel₀ hq
    have hle : v ((p : C) ^ k * q) ≤ 1 := by rw [map_mul, map_pow]; exact hk
    obtain ⟨b, hb⟩ := hv.exists_of_le_one hle
    exact ⟨k, b, hb.symm⟩
  · intro n hn
    have hB : (n : C) * (Nat.gcdA n p : C) + (p : C) * (Nat.gcdB n p : C) = 1 := by
      have h := Nat.gcd_eq_gcd_ab n p
      rw [Nat.Coprime.gcd_eq_one hn] at h
      exact_mod_cast h.symm
    have hvn : v (n : C) = 1 := by
      have h1 : v (n : C) ≤ 1 := by exact_mod_cast hint n
      by_contra hne
      have hlt : v (n : C) < 1 := lt_of_le_of_ne h1 hne
      have a1 : v ((n : C) * (Nat.gcdA n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      have a2 : v ((p : C) * (Nat.gcdB n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hvp1
      have := Valuation.map_add_lt v a1 a2
      rw [hB, map_one] at this
      exact lt_irrefl _ this
    have hnC : (n : C) ≠ 0 := by
      intro h; rw [h, map_zero] at hvn; exact zero_ne_one hvn
    have hmapn : algebraMap O C (n : O) = (n : C) := map_natCast _ _
    exact hv.isUnit_of_one (by rw [hmapn]; exact Ne.isUnit hnC) (by rw [hmapn]; exact hvn)
  · intro x hx
    simp only [RingHom.id_apply] at hx
    subst hx
    exact ⟨0, rfl, by simp [hp0]⟩
  · intro a ha
    have hpO : (p : O) ≠ 0 := by
      intro h; apply hpC; rw [← hmapp, h, map_zero]
    exact (mul_eq_zero.mp ha).resolve_left hpO

end GlobalTheory.FrameIntegers
