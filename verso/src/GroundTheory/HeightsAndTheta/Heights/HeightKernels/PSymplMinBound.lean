import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplMinBound

/- English proof (translation)
Establish `hnn : 0 ≤ ∏ i, Real.sqrt (lam i)` using `Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _`. Establish `hsq : (∏ i, Real.sqrt (lam i)) ^ 2 = 1`. Rewrite using `[← Finset.prod_pow]`. Repeatedly rewrite using `[Real.sq_sqrt (hlam _).le]`. Conclude with `hprod`.

Use polynomial arithmetic with `[hsq, hnn]`.
-/
theorem prod_sqrt_eq_one {ι : Type} [Fintype ι] (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hprod : ∏ i, lam i = 1) : ∏ i, Real.sqrt (lam i) = 1 := by
  have hnn : 0 ≤ ∏ i, Real.sqrt (lam i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hsq : (∏ i, Real.sqrt (lam i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    simp_rw [Real.sq_sqrt (hlam _).le]
    exact hprod
  nlinarith [hsq, hnn]

/- English proof (translation)
Establish `hc0 : 0 < c` using `by linarith`. Establish `ha : ∀ i, 0 < c / Real.sqrt (lam i)` using `fun i => div_pos hc0 (Real.sqrt_pos.2 (hlam i))`. Establish `hpa : 1 < ∏ i, c / Real.sqrt (lam i)`. Rewrite using `[Finset.prod_div_distrib, prod_sqrt_eq_one lam hlam hprod, div_one, Finset.prod_const, Finset.card_univ]`. Conclude with `one_lt_pow₀ hc Fintype.card_ne_zero`.

Take `⟨v, hv, hbox⟩` from `h2 ι O (fun i => c / Real.sqrt (lam i)) hO ha hpa`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Establish `hlt : ∀ i ∈ (Finset.univ : Finset ι), lam i * (O *ᵥ intVec v) i ^ 2 < c ^ 2`. Introduce `i _`. Establish `hs` using `Real.sqrt_pos.2 (hlam i)`.

Establish `h1 : |(O *ᵥ intVec v) i| * Real.sqrt (lam i) < c` using `(lt_div_iff₀ hs).1 (hbox i)`. Establish `h2' : (|(O *ᵥ intVec v) i| * Real.sqrt (lam i)) ^ 2 < c ^ 2` using `pow_lt_pow_left₀ h1 (mul_nonneg (abs_nonneg _) hs.le) two_ne_zero`. Rewrite `h2'` using `[mul_pow, sq_abs, Real.sq_sqrt (hlam i).le]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.
-/
theorem exists_lt (h2 : SymplMinkowskiBox.Statement) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (O : Matrix ι ι ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (hO : |O.det| = 1)
    (hprod : ∏ i, lam i = 1) (c : ℝ) (hc : 1 < c) :
    ∃ v : ι → ℤ, v ≠ 0 ∧
      ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < (Fintype.card ι : ℝ) * c ^ 2 := by
  have hc0 : 0 < c := by linarith
  have ha : ∀ i, 0 < c / Real.sqrt (lam i) := fun i => div_pos hc0 (Real.sqrt_pos.2 (hlam i))
  have hpa : 1 < ∏ i, c / Real.sqrt (lam i) := by
    rw [Finset.prod_div_distrib, prod_sqrt_eq_one lam hlam hprod, div_one, Finset.prod_const,
      Finset.card_univ]
    exact one_lt_pow₀ hc Fintype.card_ne_zero
  obtain ⟨v, hv, hbox⟩ := h2 ι O (fun i => c / Real.sqrt (lam i)) hO ha hpa
  refine ⟨v, hv, ?_⟩
  have hlt : ∀ i ∈ (Finset.univ : Finset ι), lam i * (O *ᵥ intVec v) i ^ 2 < c ^ 2 := by
    intro i _
    have hs := Real.sqrt_pos.2 (hlam i)
    have h1 : |(O *ᵥ intVec v) i| * Real.sqrt (lam i) < c := (lt_div_iff₀ hs).1 (hbox i)
    have h2' : (|(O *ᵥ intVec v) i| * Real.sqrt (lam i)) ^ 2 < c ^ 2 :=
      pow_lt_pow_left₀ h1 (mul_nonneg (abs_nonneg _) hs.le) two_ne_zero
    rw [mul_pow, sq_abs, Real.sq_sqrt (hlam i).le] at h2'
    linarith
  calc ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < ∑ _i : ι, c ^ 2 :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
    _ = (Fintype.card ι : ℝ) * c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end PSymplMinBound

/- English proof (translation)
Introduce `ι _ _ G hG hdet m hm`. Take `⟨w, hw, -⟩` from `hm.1`. Establish `hne : Nonempty ι`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`.

Conclude with `hw (funext fun i => (IsEmpty.false i).elim)`. Take `⟨O, lam, hlam, hO, hprod, hq⟩` from `h1 ι G hG`. Rewrite `hprod` using `[hdet]`. Establish `hN : (0 : ℝ) < Fintype.card ι` using `by exact_mod_cast Fintype.card_pos`. Establish `key : ∀ c : ℝ, 1 < c → m < (Fintype.card ι : ℝ) * c ^ 2`.

Introduce `c hc`. Take `⟨v, hv, hlt⟩` from `PSymplMinBound.exists_lt h2 O lam hlam hO hprod c hc`. Establish `hmv : m ≤ qf G (intVec v)` using `hm.2 ⟨v, hv, rfl⟩`. Rewrite `hmv` using `[hq]`. Combine the linear equalities and inequalities to obtain the conclusion.

Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_le]`. Use `set N : ℝ := (Fintype.card ι : ℝ) with hNdef`. Use `set t : ℝ := (m / N + 1) / 2 with htdef`. Establish `hmN : 1 < m / N` using `by rw [lt_div_iff₀ hN]; linarith`.

Establish `ht : 1 < t` using `by rw [htdef]; linarith`. Establish `hsqrt : 1 < Real.sqrt t`. Rewrite using `[Real.lt_sqrt zero_le_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk` using `key (Real.sqrt t) hsqrt`.

Rewrite `hk` using `[Real.sq_sqrt (by linarith)]`. Establish `: N * t = (m + N) / 2`. Rewrite using `[htdef]`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem SymplMinBound.proof (h1 : SymplQuadDiag.Statement) (h2 : SymplMinkowskiBox.Statement) :
    SymplMinBound.Statement := by
  intro ι _ _ G hG hdet m hm
  obtain ⟨w, hw, -⟩ := hm.1
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hw (funext fun i => (IsEmpty.false i).elim)
  obtain ⟨O, lam, hlam, hO, hprod, hq⟩ := h1 ι G hG
  rw [hdet] at hprod
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ c : ℝ, 1 < c → m < (Fintype.card ι : ℝ) * c ^ 2 := by
    intro c hc
    obtain ⟨v, hv, hlt⟩ := PSymplMinBound.exists_lt h2 O lam hlam hO hprod c hc
    have hmv : m ≤ qf G (intVec v) := hm.2 ⟨v, hv, rfl⟩
    rw [hq] at hmv
    linarith
  by_contra hcon
  rw [not_le] at hcon
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set t : ℝ := (m / N + 1) / 2 with htdef
  have hmN : 1 < m / N := by rw [lt_div_iff₀ hN]; linarith
  have ht : 1 < t := by rw [htdef]; linarith
  have hsqrt : 1 < Real.sqrt t := by
    rw [Real.lt_sqrt zero_le_one]; linarith
  have hk := key (Real.sqrt t) hsqrt
  rw [Real.sq_sqrt (by linarith)] at hk
  have : N * t = (m + N) / 2 := by
    rw [htdef]; field_simp
  linarith

end GroundTheory.Heights₂.Heights
