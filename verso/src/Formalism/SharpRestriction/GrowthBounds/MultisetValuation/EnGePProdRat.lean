import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AuxUOfFirstTheoremPlaceBound
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.JpSubstExpand
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

/- English proof (translation)
Conclude with `natCast_mem Y.Oc p`.
-/
theorem en_p_mem : (p : Y.Kc) ∈ Y.Oc := by
  exact natCast_mem Y.Oc p

/- English proof (translation)
Use `lift N to ℕ using hN`. Rewrite using `[zpow_natCast]`. Conclude with `Y.Oc.pow_mem (en_p_mem Y) _`.
-/
theorem en_ppow_mem (N : ℤ) (hN : 0 ≤ N) : (p : Y.Kc) ^ N ∈ Y.Oc := by
  lift N to ℕ using hN
  rw [zpow_natCast]
  exact Y.Oc.pow_mem (en_p_mem Y) _

/- English proof (translation)
Break down `Y.Oc_val z with hz | hz` into its components or cases. Conclude with `hz`. Distinguish the cases in `h0 : z = 0`. Rewrite using `[h0]`. Conclude with `Y.Oc.zero_mem`.

Establish `e : z = z ^ M * (z⁻¹) ^ (M - 1)`. Rewrite using `[inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ h0), ← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`.

Conclude with `Y.Oc.mul_mem h (Y.Oc.pow_mem hz _)`.
-/
theorem en_root (z : Y.Kc) (M : ℕ) (hM : 0 < M) (h : z ^ M ∈ Y.Oc) : z ∈ Y.Oc := by
  rcases Y.Oc_val z with hz | hz
  · exact hz
  · by_cases h0 : z = 0
    · rw [h0]
      exact Y.Oc.zero_mem
    · have e : z = z ^ M * (z⁻¹) ^ (M - 1) := by
        rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ h0), ← pow_succ']
        congr 1
        omega
      rw [e]
      exact Y.Oc.mul_mem h (Y.Oc.pow_mem hz _)

/- English proof (translation)
Introduce `a b hb hab`. Rewrite using `[one_pow, one_mul]`. Establish `h' : (a : ℝ) ≤ 0` using `by linarith`. Establish `h'' : a ≤ 0` using `by exact_mod_cast h'`. Conclude with `en_ppow_mem Y (-a) (by omega)`.
-/
theorem en_geC_one : Y.geC 1 0 := by
  intro a b hb hab
  rw [one_pow, one_mul]
  have h' : (a : ℝ) ≤ 0 := by linarith
  have h'' : a ≤ 0 := by exact_mod_cast h'
  exact en_ppow_mem Y (-a) (by omega)

/- English proof (translation)
Introduce `a b hb hab`. Establish `hp` using `pKc_ne Y`. Establish `hM0 : 0 < q1.den * q2.den` using `Nat.mul_pos q1.den_pos q2.den_pos`. Choose the witnesses or unpack the hypotheses as in `⟨a1, ha1⟩ : ∃ a1 : ℤ, (a1 : ℝ) = (q1 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by`. Use `⟨q1.num * q2.den * b, ?_⟩` and prove the remaining obligations.

Establish `hd : (q1.den : ℝ) ≠ 0` using `by exact_mod_cast q1.den_pos.ne'`. Rewrite using `[Rat.cast_def]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Choose the witnesses or unpack the hypotheses as in `⟨a2, ha2⟩ : ∃ a2 : ℤ, (a2 : ℝ) = (q2 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by`.

Use `⟨q2.num * q1.den * b, ?_⟩` and prove the remaining obligations. Establish `hd : (q2.den : ℝ) ≠ 0` using `by exact_mod_cast q2.den_pos.ne'`. Rewrite using `[Rat.cast_def]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `hx'` using `hx a1 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha1.le`. Establish `hy'` using `hy a2 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha2.le`. Establish `hle : a * ((q1.den * q2.den : ℕ) : ℤ) ≤ a1 + a2`. Establish `h' : ((a * ((q1.den * q2.den : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((a1 + a2 : ℤ) : ℝ)`. Use `push_cast`.

Rewrite using `[ha1, ha2]`. Move the coercions through the operations in `at hab ⊢`. Establish `hM' : (0 : ℝ) ≤ (q1.den : ℝ) * q2.den` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h'` after adjusting the coercions.

Establish `key : ((x * y) ^ b * (p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) = (x ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a1)) * (y ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a2)) * (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ))`. Establish `h1 : ((p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) = (p : Y.Kc) ^ (-a1) * (p : Y.Kc) ^ (-a2) * (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ))`. Rewrite using `[← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp, ← zpow_add₀ hp]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_pow, h1]`. Expand and normalize the polynomial expressions, which then agree. Apply `en_root Y _ (q1.den * q2.den) hM0` to reduce the goal to its premises. Rewrite using `[key]`.

Conclude with `Y.Oc.mul_mem (Y.Oc.mul_mem hx' hy') (en_ppow_mem Y _ (by omega))`.
-/
theorem en_geC_mul_rat {x y : Y.Kc} (q1 q2 : ℚ) (hx : Y.geC x q1) (hy : Y.geC y q2) :
    Y.geC (x * y) ((q1 + q2 : ℚ) : ℝ) := by
  intro a b hb hab
  have hp := pKc_ne Y
  have hM0 : 0 < q1.den * q2.den := Nat.mul_pos q1.den_pos q2.den_pos
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℤ, (a1 : ℝ) = (q1 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q1.num * q2.den * b, ?_⟩
    have hd : (q1.den : ℝ) ≠ 0 := by exact_mod_cast q1.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℤ, (a2 : ℝ) = (q2 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q2.num * q1.den * b, ?_⟩
    have hd : (q2.den : ℝ) ≠ 0 := by exact_mod_cast q2.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hx' := hx a1 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha1.le
  have hy' := hy a2 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha2.le
  have hle : a * ((q1.den * q2.den : ℕ) : ℤ) ≤ a1 + a2 := by
    have h' : ((a * ((q1.den * q2.den : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((a1 + a2 : ℤ) : ℝ) := by
      push_cast
      rw [ha1, ha2]
      push_cast at hab ⊢
      have hM' : (0 : ℝ) ≤ (q1.den : ℝ) * q2.den := by positivity
      nlinarith
    exact_mod_cast h'
  have key : ((x * y) ^ b * (p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
      (x ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a1)) * (y ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a2)) *
        (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
    have h1 : ((p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
        (p : Y.Kc) ^ (-a1) * (p : Y.Kc) ^ (-a2) * (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp, ← zpow_add₀ hp]
      congr 1
      push_cast
      ring
    rw [mul_pow, h1]
    ring
  apply en_root Y _ (q1.den * q2.den) hM0
  rw [key]
  exact Y.Oc.mul_mem (Y.Oc.mul_mem hx' hy') (en_ppow_mem Y _ (by omega))

/- English proof (translation)
Conclude with `Finset.sum_induction f (fun x => Y.geC x g) (fun _ _ ha hb => geC_add Y ha hb) (geC_zero Y g) h`.
-/
theorem en_geC_sum {α : Type} (s : Finset α) (f : α → Y.Kc) (g : ℝ) (h : ∀ i ∈ s, Y.geC (f i) g) :
    Y.geC (∑ i ∈ s, f i) g := by
  exact Finset.sum_induction f (fun x => Y.geC x g) (fun _ _ ha hb => geC_add Y ha hb) (geC_zero Y g) h

def geP {τ : Type} (a : MvPolynomial τ Y.Kc) (g : ℝ) : Prop := ∀ n, Y.geC (MvPolynomial.coeff n a) g

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPolynomial.coeff_one]`. Use `split_ifs`. Conclude with `en_geC_one Y`. Conclude with `geC_zero Y 0`.
-/
theorem valuation_coeff_one_nonneg {τ : Type} : geP Y (1 : MvPolynomial τ Y.Kc) 0 := by
  classical
  intro n
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact en_geC_one Y
  · exact geC_zero Y 0

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPolynomial.coeff_mul]`. Conclude with `en_geC_sum Y _ _ _ fun x _ => en_geC_mul_rat Y q1 q2 (ha x.1) (hb x.2)`.
-/
theorem valuation_coeff_ge_mul_rat {τ : Type} {a b : MvPolynomial τ Y.Kc} (q1 q2 : ℚ) (ha : geP Y a q1) (hb : geP Y b q2) :
    geP Y (a * b) ((q1 + q2 : ℚ) : ℝ) := by
  classical
  intro n
  rw [MvPolynomial.coeff_mul]
  exact en_geC_sum Y _ _ _ fun x _ => en_geC_mul_rat Y q1 q2 (ha x.1) (hb x.2)

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `using valuation_coeff_one_nonneg Y (τ := τ)`. Introduce `i t hi ih h`.

Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`. Conclude with `valuation_coeff_ge_mul_rat Y _ _ (h i (Finset.mem_insert_self i t)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem valuation_coeff_ge_prod_rat {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (q : α → ℚ)
    (h : ∀ i ∈ s, geP Y (a i) (q i)) : geP Y (∏ i ∈ s, a i) ((∑ i ∈ s, q i : ℚ) : ℝ) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using valuation_coeff_one_nonneg Y (τ := τ)
  · intro i t hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact valuation_coeff_ge_mul_rat Y _ _ (h i (Finset.mem_insert_self i t))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPolynomial.coeff_sum]`. Conclude with `en_geC_sum Y _ _ _ fun i hi => h i hi n`.
-/
theorem valuation_coeff_ge_sum {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (g : ℝ) (h : ∀ i ∈ s, geP Y (a i) g) :
    geP Y (∑ i ∈ s, a i) g := by
  intro n
  rw [MvPolynomial.coeff_sum]
  exact en_geC_sum Y _ _ _ fun i hi => h i hi n

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Conclude with `geC_mul_Oc Y (h n) hc`.
-/
theorem valuation_coeff_ge_smul {τ : Type} {a : MvPolynomial τ Y.Kc} {g : ℝ} {c : Y.Kc} (hc : c ∈ Y.Oc) (h : geP Y a g) :
    geP Y (c • a) g := by
  intro n
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact geC_mul_Oc Y (h n) hc

end Formalism.MainNotions.FormalGroupSystem.Pf
