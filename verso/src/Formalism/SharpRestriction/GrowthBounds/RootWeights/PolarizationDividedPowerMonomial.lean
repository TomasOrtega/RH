import Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowersPreserveZero

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section ops

variable {K : Type} [Field K] {σ : Type}

def polarizationOperator (K : Type) [Field K] {σ : Type} (v w : σ) : Module.End K (MvPolynomial σ K) :=
  (LinearMap.mulLeft K (X v)) ∘ₗ (pderiv w).toLinearMap

/- English proof (translation)
Use `show X v * pderiv w (monomial m c) = _`. Rewrite using `[pderiv_monomial, X, monomial_mul, one_mul, add_comm (Finsupp.single v 1)]`.
-/
theorem polarization_monomial (v w : σ) (m : σ →₀ ℕ) (c : K) :
    polarizationOperator K v w (monomial m c) = monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : K)) := by
  show X v * pderiv w (monomial m c) = _
  rw [pderiv_monomial, X, monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, polarization_monomial]`. Establish `hw : (m - Finsupp.single w k + Finsupp.single v k : σ →₀ ℕ) w = m w - k`.

Simplify using `[Finsupp.single_apply, hvw]`. Establish `hexp : (m - Finsupp.single w k + Finsupp.single v k - Finsupp.single w 1 + Finsupp.single v 1 : σ →₀ ℕ) = m - Finsupp.single w (k + 1) + Finsupp.single v (k + 1)`. Use extensionality with `x`. Distinguish the cases in `hx : x = w`. Rewrite using `[hx]`.

Simplify using `[Finsupp.single_apply, hvw]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hy : x = v`. Rewrite using `[hy]`. Simplify using `[Finsupp.single_apply, hvw, Ne.symm hvw]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[Finsupp.single_apply, Ne.symm hx, Ne.symm hy]`. Rewrite using `[hexp, hw, Nat.descFactorial_succ, Nat.cast_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polarization_pow_monomial (v w : σ) (hvw : v ≠ w) (k : ℕ) (m : σ →₀ ℕ) (c : K) :
    (polarizationOperator K v w ^ k) (monomial m c) =
      monomial (m - Finsupp.single w k + Finsupp.single v k) (c * ((m w).descFactorial k : K)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, polarization_monomial]
    have hw : (m - Finsupp.single w k + Finsupp.single v k : σ →₀ ℕ) w = m w - k := by
      simp [Finsupp.single_apply, hvw]
    have hexp : (m - Finsupp.single w k + Finsupp.single v k - Finsupp.single w 1
        + Finsupp.single v 1 : σ →₀ ℕ) = m - Finsupp.single w (k + 1) + Finsupp.single v (k + 1) := by
      ext x
      by_cases hx : x = w
      · rw [hx]
        simp [Finsupp.single_apply, hvw]
        omega
      · by_cases hy : x = v
        · rw [hy]
          simp [Finsupp.single_apply, hvw, Ne.symm hvw]
          omega
        · simp [Finsupp.single_apply, Ne.symm hx, Ne.symm hy]
    rw [hexp, hw, Nat.descFactorial_succ, Nat.cast_mul]
    congr 1
    ring

/- English proof (translation)
Rewrite using `[polarization_pow_monomial v w hvw, MvPolynomial.smul_monomial, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]`. Use `congr 1`. Establish `: (k.factorial : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)`. Rewrite using `[smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem polarization_divided_power_monomial [CharZero K] (v w : σ) (hvw : v ≠ w) (k : ℕ) (m : σ →₀ ℕ) (c : K) :
    ((k.factorial : K)⁻¹) • (polarizationOperator K v w ^ k) (monomial m c) =
      monomial (m - Finsupp.single w k + Finsupp.single v k) (c * ((m w).choose k : K)) := by
  rw [polarization_pow_monomial v w hvw, MvPolynomial.smul_monomial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  congr 1
  have : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [smul_eq_mul]
  field_simp

/- English proof (translation)
Use `show polarizationOperator K v w * polarizationOperator K v' w' = polarizationOperator K v' w' * polarizationOperator K v w`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, polarization_monomial, polarization_monomial, polarization_monomial, polarization_monomial]`.

Establish `e1 : (m - Finsupp.single w' 1 + Finsupp.single v' 1 : σ →₀ ℕ) w = m w`. Simplify using `[Finsupp.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]`. Establish `e2 : (m - Finsupp.single w 1 + Finsupp.single v 1 : σ →₀ ℕ) w' = m w'`. Simplify using `[Finsupp.single_apply, h3, Ne.symm h2, Ne.symm h3, h2]`. Establish `hexp : (m - Finsupp.single w' 1 + Finsupp.single v' 1 - Finsupp.single w 1 + Finsupp.single v 1 : σ →₀ ℕ) = m - Finsupp.single w 1 + Finsupp.single v 1 - Finsupp.single w' 1 + Finsupp.single v' 1`.

Use extensionality with `x`. Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`. Apply the tactic sequence `by_cases a1 : w = x <;> by_cases a2 : w' = x <;> by_cases a3 : v = x <;>`. Apply the tactic sequence `by_cases a4 : v' = x <;> (try subst_vars) <;> (try simp_all) <;> omega`. Rewrite using `[e1, e2, hexp]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, hp, hq]`.
-/
theorem polarization_commute (v w v' w' : σ) (h1 : w ≠ v') (h2 : w ≠ w') (h3 : w' ≠ v) :
    Commute (polarizationOperator K v w) (polarizationOperator K v' w') := by
  show polarizationOperator K v w * polarizationOperator K v' w' = polarizationOperator K v' w' * polarizationOperator K v w
  refine LinearMap.ext fun f => ?_
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [Module.End.mul_apply, Module.End.mul_apply, polarization_monomial, polarization_monomial,
      polarization_monomial, polarization_monomial]
    have e1 : (m - Finsupp.single w' 1 + Finsupp.single v' 1 : σ →₀ ℕ) w = m w := by
      simp [Finsupp.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]
    have e2 : (m - Finsupp.single w 1 + Finsupp.single v 1 : σ →₀ ℕ) w' = m w' := by
      simp [Finsupp.single_apply, h3, Ne.symm h2, Ne.symm h3, h2]
    have hexp : (m - Finsupp.single w' 1 + Finsupp.single v' 1 - Finsupp.single w 1
        + Finsupp.single v 1 : σ →₀ ℕ) =
        m - Finsupp.single w 1 + Finsupp.single v 1 - Finsupp.single w' 1 + Finsupp.single v' 1 := by
      ext x
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      by_cases a1 : w = x <;> by_cases a2 : w' = x <;> by_cases a3 : v = x <;>
        by_cases a4 : v' = x <;> (try subst_vars) <;> (try simp_all) <;> omega
    rw [e1, e2, hexp]
    congr 1
    ring
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]

end ops

section fact

variable {σ : Type}

/- English proof (translation)
Establish `hd : Disjoint (m.erase v).support (Finsupp.single v j).support` using `Finset.disjoint_of_subset_right Finsupp.support_single_subset (Finset.disjoint_singleton_right.mpr (by simp))`. Unfold `expFact`. Rewrite using `[Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp)]`.
-/
theorem exponent_factorial_erase_single (m : σ →₀ ℕ) (v : σ) (j : ℕ) :
    expFact (m.erase v + Finsupp.single v j) = expFact (m.erase v) * j.factorial := by
  have hd : Disjoint (m.erase v).support (Finsupp.single v j).support :=
    Finset.disjoint_of_subset_right Finsupp.support_single_subset
      (Finset.disjoint_singleton_right.mpr (by simp))
  unfold expFact
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp)]

/- English proof (translation)
Establish `h1 : m + Finsupp.single v k = m.erase v + Finsupp.single v (m v + k)`. Use extensionality with `x`. Distinguish the cases in `hx : x = v`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Finsupp.erase_ne hx, Finsupp.single_apply, Ne.symm hx]`. Establish `h2 : expFact m = expFact (m.erase v) * (m v).factorial` using `by conv_lhs => rw [← Finsupp.erase_add_single v m]`. Conclude with `exponent_factorial_erase_single m v (m v)`. Rewrite using `[h1, exponent_factorial_erase_single, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exponent_factorial_add_single (m : σ →₀ ℕ) (v : σ) (k : ℕ) :
    expFact (m + Finsupp.single v k) * (m v).factorial = expFact m * (m v + k).factorial := by
  have h1 : m + Finsupp.single v k = m.erase v + Finsupp.single v (m v + k) := by
    ext x
    by_cases hx : x = v
    · subst hx
      simp
    · simp [Finsupp.erase_ne hx, Finsupp.single_apply, Ne.symm hx]
  have h2 : expFact m = expFact (m.erase v) * (m v).factorial := by
    conv_lhs => rw [← Finsupp.erase_add_single v m]
    exact exponent_factorial_erase_single m v (m v)
  rw [h1, exponent_factorial_erase_single, h2]
  ring

/- English proof (translation)
Unfold `expFact Finsupp.prod`. Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _`.
-/
theorem exponent_factorial_ne_zero_of (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

/- English proof (translation)
Establish `hC : (m w).choose k ≠ 0` using `(Nat.choose_pos hk).ne'`. Use `set a := m - Finsupp.single w k with ha`. Establish `haw : a w = m w - k` using `by simp [ha]`. Establish `hav : a v = m v` using `by simp [ha, Finsupp.single_apply, Ne.symm hvw]`. Establish `hm : a + Finsupp.single w k = m`.

Use extensionality with `x`. Distinguish the cases in `hx : x = w`. Substitute `hx` using the available equality. Simplify using `[ha]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[ha, Finsupp.single_apply, Ne.symm hx]`. Establish `e1` using `exponent_factorial_add_single a w k`. Rewrite `e1` using `[hm, haw, Nat.sub_add_cancel hk]`. Establish `e2` using `exponent_factorial_add_single a v k`. Rewrite `e2` using `[hav]`.

Establish `f1 : expFact m = expFact a * (m w).choose k * k.factorial`. Use `Nat.choose_mul_factorial_mul_factorial hk` as an intermediate fact. Apply `Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m w - k))` to reduce the goal to its premises. Rewrite using `[e1, ← this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `f2 : expFact (a + Finsupp.single v k) = expFact a * (m v + k).choose k * k.factorial`. Use `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k (m v))` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel]`. Apply `Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m v))` to reduce the goal to its premises. Rewrite using `[e2, ← this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdvd : expFact m ∣ (m w).choose k ^ 2 * expFact (a + Finsupp.single v k)`. Rewrite using `[f1, f2]`. Conclude with `⟨(m w).choose k * (m v + k).choose k, by ring⟩`. Establish `hne : (m w).choose k ^ 2 * expFact (a + Finsupp.single v k) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hC) (exponent_factorial_ne_zero_of _)`.

Establish `hle` using `(padicValNat_dvd_iff_le (p := p) hne).mp ((pow_padicValNat_dvd (p := p)).trans hdvd)`. Rewrite `hle` using `[padicValNat.mul (pow_ne_zero _ hC) (exponent_factorial_ne_zero_of _), padicValNat.pow]`. Conclude with `hle`.
-/
theorem padic_exponent_factorial_bound (p : ℕ) [Fact p.Prime] (m : σ →₀ ℕ) (v w : σ) (hvw : v ≠ w) (k : ℕ) (hk : k ≤ m w) :
    padicValNat p (expFact m) ≤ 2 * padicValNat p ((m w).choose k) +
      padicValNat p (expFact (m - Finsupp.single w k + Finsupp.single v k)) := by
  have hC : (m w).choose k ≠ 0 := (Nat.choose_pos hk).ne'
  set a := m - Finsupp.single w k with ha
  have haw : a w = m w - k := by simp [ha]
  have hav : a v = m v := by simp [ha, Finsupp.single_apply, Ne.symm hvw]
  have hm : a + Finsupp.single w k = m := by
    ext x
    by_cases hx : x = w
    · subst hx
      simp [ha]
      omega
    · simp [ha, Finsupp.single_apply, Ne.symm hx]
  have e1 := exponent_factorial_add_single a w k
  rw [hm, haw, Nat.sub_add_cancel hk] at e1
  have e2 := exponent_factorial_add_single a v k
  rw [hav] at e2
  have f1 : expFact m = expFact a * (m w).choose k * k.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hk
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m w - k))
    rw [e1, ← this]
    ring
  have f2 : expFact (a + Finsupp.single v k) = expFact a * (m v + k).choose k * k.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k (m v))
    rw [Nat.add_sub_cancel] at this
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m v))
    rw [e2, ← this]
    ring
  have hdvd : expFact m ∣ (m w).choose k ^ 2 * expFact (a + Finsupp.single v k) := by
    rw [f1, f2]
    exact ⟨(m w).choose k * (m v + k).choose k, by ring⟩
  have hne : (m w).choose k ^ 2 * expFact (a + Finsupp.single v k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hC) (exponent_factorial_ne_zero_of _)
  have hle := (padicValNat_dvd_iff_le (p := p) hne).mp ((pow_padicValNat_dvd (p := p)).trans hdvd)
  rw [padicValNat.mul (pow_ne_zero _ hC) (exponent_factorial_ne_zero_of _), padicValNat.pow] at hle
  exact hle

end fact

end Formalism.MainNotions.G.GLWeightTheory
