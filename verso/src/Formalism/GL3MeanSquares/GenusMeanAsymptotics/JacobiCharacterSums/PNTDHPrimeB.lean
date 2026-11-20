import Mathlib

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

/- English proof (translation)
Establish `hx : 0 ≤ b * t` using `mul_nonneg hb ht`. Establish `hf : (0:ℝ) < (m.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos m`. Establish `h1 : (b * t) ^ m ≤ Real.exp (b * t) * (m.factorial : ℝ)`. Establish `h` using `Real.pow_div_factorial_le_exp (b * t) hx m`. Rewrite `h` using `[div_le_iff₀ hf]`. Then use the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (Real.exp (b * t) * (m.factorial : ℝ)) * Real.exp (-(b * t)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le`. Use `_ = (m.factorial : ℝ) := by`.

Rewrite using `[mul_comm (Real.exp (b * t)), mul_assoc, ← Real.exp_add]`. Simplify using the standard rewrite rules.
-/
lemma dhpr_pow_exp_le (m : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    b ^ m * (t ^ m * Real.exp (-(b * t))) ≤ (m.factorial : ℝ) := by
  have hx : 0 ≤ b * t := mul_nonneg hb ht
  have hf : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : (b * t) ^ m ≤ Real.exp (b * t) * (m.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (b * t) hx m
    rwa [div_le_iff₀ hf] at h
  calc b ^ m * (t ^ m * Real.exp (-(b * t))) = (b * t) ^ m * Real.exp (-(b * t)) := by
        rw [mul_pow]; ring
    _ ≤ (Real.exp (b * t) * (m.factorial : ℝ)) * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (m.factorial : ℝ) := by
        rw [mul_comm (Real.exp (b * t)), mul_assoc, ← Real.exp_add]; simp

/- English proof (translation)
Establish `hpos : 0 < 1 + a` using `by linarith`. Establish `h4 : Real.exp (-a) * (1 + a) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ hpos]`. Establish `e : (1 - Real.exp (-a)) * (1 + a) = (1 + a) - Real.exp (-a) * (1 + a)` using `by ring`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma dhpr_one_sub_exp_neg {a : ℝ} (ha : 0 < a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by
  have hpos : 0 < 1 + a := by linarith
  have h4 : Real.exp (-a) * (1 + a) ≤ 1 := by
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_iff₀ hpos]
  have e : (1 - Real.exp (-a)) * (1 + a) = (1 + a) - Real.exp (-a) * (1 + a) := by ring
  rw [e]; linarith

/- English proof (translation)
Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `only [pow_zero, mul_one]`. Combine the linear relations using `[Real.add_one_le_exp (1:ℝ)]`. Establish `hm : (0:ℝ) < m` using `by exact_mod_cast h`.

Establish `hm' : (m:ℝ) ≠ 0` using `hm.ne'`. Establish `key : (m:ℝ) + 1 ≤ m * Real.exp (1 / m)`. Establish `h1` using `Real.add_one_le_exp (1 / (m:ℝ))`. Establish `h2 : (m:ℝ) * (1 / m + 1) = m + 1`. Rewrite using `[mul_add, mul_one_div_cancel hm', mul_one, add_comm]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← Real.exp_nat_mul, mul_one_div_cancel hm', mul_comm]`.
-/
lemma dhpr_pow_ratio (m : ℕ) : ((m : ℝ) + 1) ^ m ≤ Real.exp 1 * (m : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp only [pow_zero, mul_one]
    linarith [Real.add_one_le_exp (1:ℝ)]
  · have hm : (0:ℝ) < m := by exact_mod_cast h
    have hm' : (m:ℝ) ≠ 0 := hm.ne'
    have key : (m:ℝ) + 1 ≤ m * Real.exp (1 / m) := by
      have h1 := Real.add_one_le_exp (1 / (m:ℝ))
      have h2 : (m:ℝ) * (1 / m + 1) = m + 1 := by
        rw [mul_add, mul_one_div_cancel hm', mul_one, add_comm]
      calc (m:ℝ) + 1 = m * (1 / m + 1) := h2.symm
        _ ≤ m * Real.exp (1 / m) := mul_le_mul_of_nonneg_left h1 hm.le
    calc ((m:ℝ) + 1) ^ m ≤ ((m:ℝ) * Real.exp (1 / m)) ^ m := by gcongr
      _ = Real.exp 1 * (m:ℝ) ^ m := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_one_div_cancel hm', mul_comm]

/- English proof (translation)
Establish `hηm : 0 < η ^ m` using `pow_pos hη m`. Establish `ht : (0:ℝ) ≤ (v:ℝ) + 1` using `by positivity`. Establish `h1` using `dhpr_pow_exp_le m hη.le ht`. Establish `h2 : Real.exp (-(η * v)) ≤ Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1)))`. Rewrite using `[← Real.exp_add]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `e : -(η * (v:ℝ)) = 1 + -(η * ((v:ℝ) + 1)) - (1 - η)` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hηm]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = Real.exp 1 * m.factorial / η ^ m := by ring`.
-/
lemma dhpr_wsup (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v : ℕ) :
    ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤ Real.exp 1 * m.factorial / η ^ m := by
  have hηm : 0 < η ^ m := pow_pos hη m
  have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
  have h1 := dhpr_pow_exp_le m hη.le ht
  have h2 : Real.exp (-(η * v)) ≤ Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : -(η * (v:ℝ)) = 1 + -(η * ((v:ℝ) + 1)) - (1 - η) := by ring
    rw [e]; linarith
  calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * v))
      ≤ ((v : ℝ) + 1) ^ m * (Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp 1 * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
    _ ≤ Real.exp 1 * ((m.factorial : ℝ) / η ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        rw [le_div_iff₀ hηm]
        calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1))) * η ^ m
            = η ^ m * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
          _ ≤ (m.factorial : ℝ) := h1
    _ = Real.exp 1 * m.factorial / η ^ m := by ring

/- English proof (translation)
Take `⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / ((m:ℝ) + 1)` from `⟨_, rfl⟩`. Establish `hm1 : (0:ℝ) < (m:ℝ) + 1` using `by positivity`. Establish `hm1ne : (m:ℝ) + 1 ≠ 0` using `hm1.ne'`. Establish `hδη : ((m:ℝ) + 1) * δ = η` using `by rw [hδ]; field_simp`. Establish `hδpos : 0 < δ` using `by rw [hδ]; exact div_pos hη hm1`.

Establish `hm0 : (0:ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hη'nn : 0 ≤ (m:ℝ) * δ` using `mul_nonneg hm0 hδpos.le`. Establish `hsplit : (m:ℝ) * δ + δ = η` using `by rw [← hδη]; ring`. Establish `hη'le : (m:ℝ) * δ ≤ 1` using `by linarith`. Establish `hpow : η ^ m ≤ Real.exp 1 * ((m:ℝ) * δ) ^ m`.

Rewrite using `[← hδη, mul_pow, mul_pow, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (dhpr_pow_ratio m) (pow_nonneg hδpos.le m)`. Establish `hterm : ∀ v : ℕ, η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) ≤ Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v))`. Introduce `v`. Establish `ht : (0:ℝ) ≤ (v:ℝ) + 1` using `by positivity`.

Establish `h1` using `dhpr_pow_exp_le m hη'nn ht`. Establish `hexp : Real.exp (-(η * v)) ≤ Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v))`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[← hsplit]`.

Establish `e : -(((m:ℝ) * δ + δ) * (v:ℝ)) = 1 + -((m:ℝ) * δ * ((v:ℝ) + 1)) + -(δ * v) - (1 - (m:ℝ) * δ)` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul hpow ?_ (by positivity) (mul_nonneg (Real.exp_pos 1).le (pow_nonneg hη'nn m))` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left hexp (by positivity)`. Use `_ = Real.exp 1 * Real.exp 1 * (((m:ℝ) * δ) ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))))) * Real.exp (-(δ * v)) := by ring`. Use `_ ≤ Real.exp 1 * Real.exp 1 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by`. Use `mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left h1 (by positivity)`.

Use `_ = Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by`. Rewrite using `[← Real.exp_add]`. Evaluate the numerical expressions. Establish `hsum : η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤ Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v))`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`.

Conclude with `Finset.sum_le_sum (fun v _ => hterm v)`. Establish `hG : (∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ ≤ 1 + δ`. Establish `hrw : ∀ v : ℕ, Real.exp (-(δ * v)) = Real.exp (-δ) ^ v`. Introduce `v`. Rewrite using `[← Real.exp_nat_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hrw]`. Establish `hr0 : 0 < Real.exp (-δ)` using `Real.exp_pos _`. Establish `hsub : ∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v`.

Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_Ico]`. Rewrite using `[Finset.mem_range]`. Conclude with `hx.2`.

Introduce `i _ _`. Conclude with `pow_nonneg hr0.le i`. Establish `hG0 : 0 ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v` using `Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)`. Establish `hgeo : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) ≤ 1`. Establish `h` using `geom_sum_mul (Real.exp (-δ)) V`.

Establish `hV : 0 ≤ Real.exp (-δ) ^ V` using `pow_nonneg hr0.le V`. Establish `e : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) = -((∑ v ∈ range V, Real.exp (-δ) ^ v) * (Real.exp (-δ) - 1))` using `by ring`. Rewrite using `[e, h]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `dhpr_one_sub_exp_neg hδpos`.

Establish `h2' : δ ≤ (1 - Real.exp (-δ)) * (1 + δ)`. Rewrite `h2` using `[div_le_iff₀ (by linarith)]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[le_div_iff₀ (pow_pos hη (m + 1))]`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul_of_nonneg_right ?_ hm1.le` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left hG (by positivity)`. Use `_ = Real.exp 2 * (m.factorial : ℝ) * ((m:ℝ) + 1 + η) := by rw [← hδη]; ring`. Use `_ ≤ Real.exp 2 * (m.factorial : ℝ) * (2 * ((m:ℝ) + 1)) := by`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = 2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) := by ring`.
-/
lemma dhpr_wsum (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) / η ^ (m + 1) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / ((m:ℝ) + 1) := ⟨_, rfl⟩
  have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hm1ne : (m:ℝ) + 1 ≠ 0 := hm1.ne'
  have hδη : ((m:ℝ) + 1) * δ = η := by rw [hδ]; field_simp
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hη hm1
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hη'nn : 0 ≤ (m:ℝ) * δ := mul_nonneg hm0 hδpos.le
  have hsplit : (m:ℝ) * δ + δ = η := by rw [← hδη]; ring
  have hη'le : (m:ℝ) * δ ≤ 1 := by linarith
  have hpow : η ^ m ≤ Real.exp 1 * ((m:ℝ) * δ) ^ m := by
    rw [← hδη, mul_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (dhpr_pow_ratio m) (pow_nonneg hδpos.le m)
  have hterm : ∀ v : ℕ, η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) ≤
      Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
    intro v
    have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
    have h1 := dhpr_pow_exp_le m hη'nn ht
    have hexp : Real.exp (-(η * v)) ≤
        Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← hsplit]
      have e : -(((m:ℝ) * δ + δ) * (v:ℝ)) =
          1 + -((m:ℝ) * δ * ((v:ℝ) + 1)) + -(δ * v) - (1 - (m:ℝ) * δ) := by ring
      rw [e]; linarith
    calc η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v)))
        ≤ (Real.exp 1 * ((m:ℝ) * δ) ^ m) * (((v:ℝ) + 1) ^ m *
            (Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)))) := by
          refine mul_le_mul hpow ?_ (by positivity) (mul_nonneg (Real.exp_pos 1).le (pow_nonneg hη'nn m))
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 1 * Real.exp 1 * (((m:ℝ) * δ) ^ m * (((v:ℝ) + 1) ^ m *
            Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))))) * Real.exp (-(δ * v)) := by ring
      _ ≤ Real.exp 1 * Real.exp 1 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          rw [← Real.exp_add]; norm_num
  have hsum : η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun v _ => hterm v)
  have hG : (∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ ≤ 1 + δ := by
    have hrw : ∀ v : ℕ, Real.exp (-(δ * v)) = Real.exp (-δ) ^ v := by
      intro v; rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [hrw]
    have hr0 : 0 < Real.exp (-δ) := Real.exp_pos _
    have hsub : ∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Ico] at hx
        rw [Finset.mem_range]
        exact hx.2
      · intro i _ _
        exact pow_nonneg hr0.le i
    have hG0 : 0 ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have hgeo : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) ≤ 1 := by
      have h := geom_sum_mul (Real.exp (-δ)) V
      have hV : 0 ≤ Real.exp (-δ) ^ V := pow_nonneg hr0.le V
      have e : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) =
          -((∑ v ∈ range V, Real.exp (-δ) ^ v) * (Real.exp (-δ) - 1)) := by ring
      rw [e, h]; linarith
    have h2 := dhpr_one_sub_exp_neg hδpos
    have h2' : δ ≤ (1 - Real.exp (-δ)) * (1 + δ) := by
      rwa [div_le_iff₀ (by linarith)] at h2
    calc (∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v) * δ
        ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * δ := mul_le_mul_of_nonneg_right hsub hδpos.le
      _ ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * ((1 - Real.exp (-δ)) * (1 + δ)) :=
          mul_le_mul_of_nonneg_left h2' hG0
      _ = ((∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ))) * (1 + δ) := by ring
      _ ≤ 1 * (1 + δ) := mul_le_mul_of_nonneg_right hgeo (by linarith)
      _ = 1 + δ := one_mul _
  rw [le_div_iff₀ (pow_pos hη (m + 1))]
  calc (∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η ^ (m + 1)
      = (η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η := by ring
    _ ≤ (Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * η :=
        mul_le_mul_of_nonneg_right hsum hη.le
    _ = Real.exp 2 * (m.factorial : ℝ) * ((∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ) *
          ((m:ℝ) + 1) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (1 + δ) * ((m:ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hm1.le
        exact mul_le_mul_of_nonneg_left hG (by positivity)
    _ = Real.exp 2 * (m.factorial : ℝ) * ((m:ℝ) + 1 + η) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (2 * ((m:ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) := by ring

/- English proof (translation)
Establish `hr0 : 0 < Real.exp (-(1/4:ℝ))` using `Real.exp_pos _`. Establish `hterm : ∀ v : ℕ, ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2)) ≤ 4 * Real.exp (-(1/4:ℝ)) ^ v`. Introduce `v`. Establish `h1` using `Real.add_one_le_exp ((v:ℝ) / 4)`. Establish `hv : (0:ℝ) ≤ v` using `Nat.cast_nonneg v`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add, ← Real.exp_nat_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h15 : (1:ℝ) / 5 ≤ 1 - Real.exp (-(1/4:ℝ))`.

Establish `h` using `dhpr_one_sub_exp_neg (show (0:ℝ) < 1/4 by norm_num)`. Establish `e : (1/4:ℝ) / (1 + 1/4) = 1 / 5` using `by norm_num`. Rewrite `h` using `[e]`. Conclude with `h`. Establish `hgeo : ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v ≤ 5 * Real.exp (-(1/4:ℝ)) ^ v0`.

Rewrite using `[Finset.sum_Ico_eq_sum_range]`. Simplify using `only [pow_add]`. Rewrite using `[← Finset.mul_sum, mul_comm (Real.exp (-(1/4:ℝ)) ^ v0)]`. Establish `hG0 : 0 ≤ ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k` using `Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)`. Establish `h` using `geom_sum_mul (Real.exp (-(1/4:ℝ))) (V - v0)`.

Establish `hV : 0 ≤ Real.exp (-(1/4:ℝ)) ^ (V - v0)` using `pow_nonneg hr0.le _`. Establish `hmul` using `mul_le_mul_of_nonneg_left h15 hG0`. Establish `hle : ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k ≤ 5`. Establish `e : (∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (1 - Real.exp (-(1/4:ℝ))) = -((∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (Real.exp (-(1/4:ℝ)) - 1))` using `by ring`. Rewrite `e` using `[h]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_le_mul_of_nonneg_right hle (pow_nonneg hr0.le _)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_nat_mul]`. Establish `e : (v0:ℝ) * -(1/4) = -((v0:ℝ) / 4)` using `by ring`.

Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dhpr_esum (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)) ≤
      20 * Real.exp (-((v0 : ℝ) / 4)) := by
  have hr0 : 0 < Real.exp (-(1/4:ℝ)) := Real.exp_pos _
  have hterm : ∀ v : ℕ, ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2)) ≤ 4 * Real.exp (-(1/4:ℝ)) ^ v := by
    intro v
    have h1 := Real.add_one_le_exp ((v:ℝ) / 4)
    have hv : (0:ℝ) ≤ v := Nat.cast_nonneg v
    calc ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2))
        ≤ (4 * Real.exp ((v:ℝ) / 4)) * Real.exp (-((v:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 4 * (Real.exp ((v:ℝ) / 4) * Real.exp (-((v:ℝ) / 2))) := by ring
      _ = 4 * Real.exp (-(1/4:ℝ)) ^ v := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          congr 2
          ring
  have h15 : (1:ℝ) / 5 ≤ 1 - Real.exp (-(1/4:ℝ)) := by
    have h := dhpr_one_sub_exp_neg (show (0:ℝ) < 1/4 by norm_num)
    have e : (1/4:ℝ) / (1 + 1/4) = 1 / 5 := by norm_num
    rw [e] at h
    exact h
  have hgeo : ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v ≤ 5 * Real.exp (-(1/4:ℝ)) ^ v0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum, mul_comm (Real.exp (-(1/4:ℝ)) ^ v0)]
    have hG0 : 0 ≤ ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have h := geom_sum_mul (Real.exp (-(1/4:ℝ))) (V - v0)
    have hV : 0 ≤ Real.exp (-(1/4:ℝ)) ^ (V - v0) := pow_nonneg hr0.le _
    have hmul := mul_le_mul_of_nonneg_left h15 hG0
    have hle : ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k ≤ 5 := by
      have e : (∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (1 - Real.exp (-(1/4:ℝ))) =
          -((∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (Real.exp (-(1/4:ℝ)) - 1)) := by ring
      rw [h] at e
      linarith
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg hr0.le _)
  calc ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))
      ≤ ∑ v ∈ Ico v0 V, 4 * Real.exp (-(1/4:ℝ)) ^ v := Finset.sum_le_sum (fun v _ => hterm v)
    _ = 4 * ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v := by rw [Finset.mul_sum]
    _ ≤ 4 * (5 * Real.exp (-(1/4:ℝ)) ^ v0) := mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = 20 * Real.exp (-((v0 : ℝ) / 4)) := by
        rw [← Real.exp_nat_mul]
        have e : (v0:ℝ) * -(1/4) = -((v0:ℝ) / 4) := by ring
        rw [e]; ring

/- English proof (translation)
The claim follows from `Nat.floor_mono (Real.exp_le_exp.mpr (by exact_mod_cast h))`.
-/
lemma dhpr_floor_mono {v w : ℕ} (h : v ≤ w) :
    ⌊Real.exp (v : ℝ)⌋₊ ≤ ⌊Real.exp (w : ℝ)⌋₊ :=
  Nat.floor_mono (Real.exp_le_exp.mpr (by exact_mod_cast h))

/- English proof (translation)
Introduce `V hV`. Proceed by induction on `V, hV using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hn ih`. Rewrite using `[Finset.sum_Ico_succ_top hn, ← ih]`.

Conclude with `(Finset.sum_Ioc_consecutive g (dhpr_floor_mono hn) (dhpr_floor_mono (by omega : n ≤ n + 1))).symm`.
-/
lemma dhpr_blocks (g : ℕ → ℝ) (v0 : ℕ) : ∀ V, v0 ≤ V →
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, g n =
      ∑ v ∈ Ico v0 V, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, g n := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← ih]
    exact (Finset.sum_Ioc_consecutive g (dhpr_floor_mono hn)
      (dhpr_floor_mono (by omega : n ≤ n + 1))).symm

end Formalism.HermitianLattices.Ext.PrimesInProgressions
