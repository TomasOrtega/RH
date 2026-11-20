import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset PowerSeries

namespace PositivityTheory.RgJS

namespace ElementarySymmetricRelation

variable {m : ℕ}

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[mul_sub, mul_one, ← mul_assoc, map_sub]`. Break down `n with _ | n` into its components or cases. Rewrite using `[coeff_zero_mul_X, coeff_mk, coeff_one]`. Simplify using the standard rewrite rules.

Rewrite using `[coeff_succ_mul_X, coeff_mul_C, coeff_mk, coeff_mk, coeff_one]`. Simplify using `[pow_succ]`.
-/
theorem geom_mul (a : ℂ) : (PowerSeries.mk fun n => a ^ n : PowerSeries ℂ) * (1 - C a * X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  rcases n with _ | n
  · rw [coeff_zero_mul_X, coeff_mk, coeff_one]
    simp
  · rw [coeff_succ_mul_X, coeff_mul_C, coeff_mk, coeff_mk, coeff_one]
    simp [pow_succ]

/- English proof (translation)
Rewrite using `[coeff_prod, hN]`. Use `Finset.sum_nbij' (fun l => ⇑l) (fun f => Finsupp.equivFunOnFinite.symm f) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `l hl`. Rewrite `hl` using `[mem_finsuppAntidiag]`. Rewrite using `[Finset.Nat.mem_antidiagonalTuple]`.

Conclude with `hl.1`. Introduce `f hf`. Rewrite `hf` using `[Finset.Nat.mem_antidiagonalTuple]`. Rewrite using `[mem_finsuppAntidiag]`. Use `⟨by simpa using hf, by simp⟩` and prove the remaining obligations.

Introduce `l _`. Simplify using the standard rewrite rules. Introduce `f _`. Simplify using the standard rewrite rules. Introduce `l _`.

Simplify using `[coeff_mk]`.
-/
theorem coeff_prod_geom (α : Fin m → ℂ) (p : ℕ) :
    coeff p (∏ i, (PowerSeries.mk fun n => α i ^ n : PowerSeries ℂ)) = hN p α := by
  classical
  rw [coeff_prod, hN]
  refine Finset.sum_nbij' (fun l => ⇑l) (fun f => Finsupp.equivFunOnFinite.symm f) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [mem_finsuppAntidiag] at hl
    rw [Finset.Nat.mem_antidiagonalTuple]
    exact hl.1
  · intro f hf
    rw [Finset.Nat.mem_antidiagonalTuple] at hf
    rw [mem_finsuppAntidiag]
    refine ⟨by simpa using hf, by simp⟩
  · intro l _
    simp
  · intro f _
    simp
  · intro l _
    simp [coeff_mk]

/- English proof (translation)
Establish `h1 : (PowerSeries.mk fun p => hN p α : PowerSeries ℂ) = ∏ i, (PowerSeries.mk fun n => α i ^ n : PowerSeries ℂ)`. Use extensionality with `p`. Rewrite using `[coeff_mk, coeff_prod_geom]`. Rewrite using `[h1, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun i _ => geom_mul (α i)`.
-/
theorem key (α : Fin m → ℂ) :
    (PowerSeries.mk fun p => hN p α : PowerSeries ℂ) * ∏ i, (1 - C (α i) * X) = 1 := by
  have h1 : (PowerSeries.mk fun p => hN p α : PowerSeries ℂ) = ∏ i, (PowerSeries.mk fun n => α i ^ n : PowerSeries ℂ) := by
    ext p
    rw [coeff_mk, coeff_prod_geom]
  rw [h1, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => geom_mul (α i)

/- English proof (translation)
Establish `e : ∏ l ∈ s, (1 - C (α l) * X : PowerSeries ℂ) = ∑ t ∈ s.powerset, C (∏ l ∈ t, -α l) * X ^ t.card`. Rewrite using `[show (∏ l ∈ s, (1 - C (α l) * X : PowerSeries ℂ)) = ∏ l ∈ s, (C (-α l) * X + 1) from prod_congr rfl (fun l _ => by rw [map_neg]; ring)]`. Rewrite using `[prod_add]`. Use `sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[prod_const_one, mul_one, prod_mul_distrib, prod_const, ← map_prod]`.

Rewrite using `[e, map_sum, mul_sum]`. Repeatedly rewrite using `[coeff_C_mul_X_pow]`. Rewrite using `[← sum_filter]`. Apply `sum_congr` to reduce the goal to its premises. Use extensionality with `t`.

Simplify using `only [mem_filter, mem_powerset, mem_powersetCard]`. Apply the tactic sequence `constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩`. Introduce `t ht`. Rewrite `ht` using `[mem_powersetCard]`. Rewrite using `[← ht.2, ← prod_const (-1 : ℂ), ← prod_mul_distrib]`.

Conclude with `prod_congr rfl (fun _ _ => by ring)`.
-/
theorem coeff_prod_one_sub (s : Finset (Fin m)) (α : Fin m → ℂ) (b : ℕ) :
    coeff b (∏ l ∈ s, (1 - C (α l) * X : PowerSeries ℂ)) =
      (-1) ^ b * ∑ S ∈ s.powersetCard b, ∏ l ∈ S, α l := by
  have e : ∏ l ∈ s, (1 - C (α l) * X : PowerSeries ℂ) =
      ∑ t ∈ s.powerset, C (∏ l ∈ t, -α l) * X ^ t.card := by
    rw [show (∏ l ∈ s, (1 - C (α l) * X : PowerSeries ℂ)) = ∏ l ∈ s, (C (-α l) * X + 1) from
      prod_congr rfl (fun l _ => by rw [map_neg]; ring)]
    rw [prod_add]
    refine sum_congr rfl (fun t _ => ?_)
    rw [prod_const_one, mul_one, prod_mul_distrib, prod_const, ← map_prod]
  rw [e, map_sum, mul_sum]
  simp_rw [coeff_C_mul_X_pow]
  rw [← sum_filter]
  apply sum_congr
  · ext t
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
  · intro t ht
    rw [mem_powersetCard] at ht
    rw [← ht.2, ← prod_const (-1 : ℂ), ← prod_mul_distrib]
    exact prod_congr rfl (fun _ _ => by ring)

/- English proof (translation)
Establish `hi` using `i.2`. Unfold `eEx`. Rewrite using `[powersetCard_eq_empty.mpr, sum_empty]`. Rewrite using `[card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eEx_eq_zero (α : Fin m → ℂ) (i : Fin m) {r : ℕ} (hr : m ≤ r) : eEx α i r = 0 := by
  have hi := i.2
  unfold eEx
  rw [powersetCard_eq_empty.mpr, sum_empty]
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

/- English proof (translation)
Rewrite using `[hZ, if_neg (by omega)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem hZ_of_le (α : Fin m → ℂ) {p r : ℕ} (h : r ≤ p) : hZ ((p : ℤ) - r) α = hN (p - r) α := by
  rw [hZ, if_neg (by omega)]
  congr 1
  omega

/- English proof (translation)
Simplify using `only [hZ]`. Rewrite using `[if_pos (by omega)]`.
-/
theorem hZ_of_lt (α : Fin m → ℂ) {p r : ℕ} (h : p < r) : hZ ((p : ℤ) - r) α = 0 := by
  simp only [hZ]
  rw [if_pos (by omega)]

/- English proof (translation)
Establish `hsplit : (∏ l, (1 - C (α l) * X : PowerSeries ℂ)) = (1 - C (α i) * X) * ∏ l ∈ univ.erase i, (1 - C (α l) * X)` using `(Finset.mul_prod_erase univ _ (mem_univ i)).symm`. Establish `hg : (PowerSeries.mk fun n => α i ^ n : PowerSeries ℂ) = (PowerSeries.mk fun p => hN p α) * ∏ l ∈ univ.erase i, (1 - C (α l) * X)`. Combine the equalities or inequalities in the displayed calculation. Establish `hc` using `congrArg (coeff p) hg`. Rewrite `hc` using `[coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`.

Rewrite using `[hc]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_mk, coeff_prod_one_sub]`. Both sides reduce to the same expression.
-/
theorem coeff_eq (α : Fin m → ℂ) (i : Fin m) (p : ℕ) :
    α i ^ p = ∑ k ∈ range (p + 1), hN k α * ((-1) ^ (p - k) * eEx α i (p - k)) := by
  classical
  have hsplit : (∏ l, (1 - C (α l) * X : PowerSeries ℂ)) =
      (1 - C (α i) * X) * ∏ l ∈ univ.erase i, (1 - C (α l) * X) :=
    (Finset.mul_prod_erase univ _ (mem_univ i)).symm
  have hg : (PowerSeries.mk fun n => α i ^ n : PowerSeries ℂ) =
      (PowerSeries.mk fun p => hN p α) * ∏ l ∈ univ.erase i, (1 - C (α l) * X) := by
    calc (PowerSeries.mk fun n => α i ^ n : PowerSeries ℂ)
        = (PowerSeries.mk fun n => α i ^ n) * ((PowerSeries.mk fun p => hN p α) * ∏ l, (1 - C (α l) * X)) := by rw [key, mul_one]
      _ = ((PowerSeries.mk fun n => α i ^ n) * (1 - C (α i) * X)) *
            ((PowerSeries.mk fun p => hN p α) * ∏ l ∈ univ.erase i, (1 - C (α l) * X)) := by rw [hsplit]; ring
      _ = _ := by rw [geom_mul, one_mul]
  have hc := congrArg (coeff p) hg
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_mk, coeff_prod_one_sub]
  rfl

end ElementarySymmetricRelation

open ElementarySymmetricRelation in
/- English proof (translation)
Introduce `_ m α i p`. Establish `hF1 : ∑ r ∈ range (p + 1), (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α = ∑ r ∈ range (p + 1 + m), (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α` using `sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) (fun r hr hr' => by`. Simplify using `only [mem_range] at hr hr'`. Rewrite using `[hZ_of_lt α (show p < r by omega), mul_zero])`. Establish `hF2 : ∑ r ∈ range m, (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α = ∑ r ∈ range (p + 1 + m), (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α` using `sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) (fun r hr hr' => by`.

Simplify using `only [mem_range] at hr hr'`. Rewrite using `[eEx_eq_zero α i (show m ≤ r by omega), mul_zero, zero_mul])`. Rewrite using `[hF2, ← hF1, coeff_eq α i p]`. Use `conv_lhs => rw [← sum_range_reflect]`. Use `sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations.

Rewrite `hj` using `[mem_range]`. Rewrite using `[hZ_of_le α (show j ≤ p by omega), show p + 1 - 1 - j = p - j by omega, show p - (p - j) = j by omega]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem elementary_relation_of_generating : HGen → ERel := by
  intro _ m α i p
  have hF1 : ∑ r ∈ range (p + 1), (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α =
      ∑ r ∈ range (p + 1 + m), (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α :=
    sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) (fun r hr hr' => by
      simp only [mem_range] at hr hr'
      rw [hZ_of_lt α (show p < r by omega), mul_zero])
  have hF2 : ∑ r ∈ range m, (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α =
      ∑ r ∈ range (p + 1 + m), (-1 : ℂ) ^ r * eEx α i r * hZ ((p : ℤ) - r) α :=
    sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) (fun r hr hr' => by
      simp only [mem_range] at hr hr'
      rw [eEx_eq_zero α i (show m ≤ r by omega), mul_zero, zero_mul])
  rw [hF2, ← hF1, coeff_eq α i p]
  conv_lhs => rw [← sum_range_reflect]
  refine sum_congr rfl (fun j hj => ?_)
  rw [mem_range] at hj
  rw [hZ_of_le α (show j ≤ p by omega), show p + 1 - 1 - j = p - j by omega,
    show p - (p - j) = j by omega]
  ring

end PositivityTheory.RgJS
