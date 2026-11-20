import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

/- English proof (translation)
Introduce `eps Ct m heps heps1`. Establish `hr : 0 < eps / 4` using `by positivity`. Establish `hK0 : 0 < 3 + |Ct|` using `by positivity`. Establish `h1` using `(isLittleO_log_rpow_atTop hr).bound (by positivity : (0:ℝ) < 1 / (2 * (3 + |Ct|)))`. Establish `h2` using `(tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (3 * Real.log 2 + Real.log m))`.

Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop 1))`. Use `⟨x0, fun x hx N t e q d hN hNle hP ht htx hqd => ?_⟩` and prove the remaining obligations. Take `⟨⟨hl, hg⟩, hx1⟩` from `hx0 x hx`. Establish `hxpos : 0 < x` using `by linarith`. Establish `hlogx : 0 ≤ Real.log x` using `Real.log_nonneg hx1`.

Establish `hX : 0 < x ^ (eps / 4)` using `Real.rpow_pos_of_pos hxpos _`. Rewrite `hl` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hX]`. Establish `hKl : (3 + |Ct|) * Real.log x ≤ x ^ (eps / 4) / 2`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.

Establish `hprod : 1 ≤ 2 ^ (e + 2) * m * q * d` using `le_trans hN hNle`. Establish `hm : 1 ≤ m` using `Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)`. Establish `hq : 1 ≤ q` using `Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)`. Establish `hd : 1 ≤ d` using `Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)`. Establish `hNr : (1:ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `htr : (1:ℝ) ≤ t` using `by exact_mod_cast ht`. Establish `hmr : (1:ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hqr : (1:ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hdr : (1:ℝ) ≤ d` using `by exact_mod_cast hd`. Establish `hNle' : (N:ℝ) ≤ 2 ^ (e + 2) * m * (q * d)`.

Rewrite using `[← mul_assoc]`. Conclude with `hNle` after adjusting the coercions. Rewrite using `[Real.log_mul (by linarith) (by linarith)]`. Establish `hlogN : Real.log N ≤ ((e:ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q:ℝ) * d)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by linarith), Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlogt : Real.log t ≤ Ct * Real.log x`. Combine the equalities or inequalities in the displayed calculation.

Establish `hE : (e:ℝ) * Real.log 2 ≤ Real.log 2 + (2 + 8 * eps) * Real.log x`. Establish `h` using `Real.log_le_log (by positivity) hP.2`. Rewrite `h` using `[Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos _).ne', Real.log_rpow hxpos]`. Conclude with `h`. Establish `hC : Ct * Real.log x ≤ |Ct| * Real.log x` using `mul_le_mul_of_nonneg_right (le_abs_self Ct) hlogx`.

Use polynomial arithmetic with `[mul_nonneg hlogx (by linarith : (0:ℝ) ≤ 1 - 8 * eps)]`.
-/
theorem UpperTheory.V.log_conductor_mul_height_le_of_pageN :
    ∀ (eps Ct : ℝ) (m : ℕ), 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ N t e q d : ℕ, 1 ≤ N → N ≤ 2 ^ (e + 2) * m * q * d →
      PageN eps x e → 1 ≤ t → (t : ℝ) ≤ x ^ Ct → Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) → Real.log ((N : ℝ) * t) ≤ 2 * x ^ (eps / 4) := by
  intro eps Ct m heps heps1
  have hr : 0 < eps / 4 := by positivity
  have hK0 : 0 < 3 + |Ct| := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).bound (by positivity : (0:ℝ) < 1 / (2 * (3 + |Ct|)))
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (3 * Real.log 2 + Real.log m))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx N t e q d hN hNle hP ht htx hqd => ?_⟩
  obtain ⟨⟨hl, hg⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hX : 0 < x ^ (eps / 4) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hX] at hl
  have hKl : (3 + |Ct|) * Real.log x ≤ x ^ (eps / 4) / 2 := by
    calc (3 + |Ct|) * Real.log x ≤ (3 + |Ct|) * (1 / (2 * (3 + |Ct|)) * x ^ (eps / 4)) :=
          mul_le_mul_of_nonneg_left hl hK0.le
      _ = x ^ (eps / 4) / 2 := by
          field_simp
  have hprod : 1 ≤ 2 ^ (e + 2) * m * q * d := le_trans hN hNle
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have htr : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hNle' : (N:ℝ) ≤ 2 ^ (e + 2) * m * (q * d) := by
    rw [← mul_assoc]
    exact_mod_cast hNle
  rw [Real.log_mul (by linarith) (by linarith)]
  have hlogN : Real.log N ≤ ((e:ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q:ℝ) * d) := by
    calc Real.log N ≤ Real.log (2 ^ (e + 2) * m * ((q:ℝ) * d)) :=
          Real.log_le_log (by linarith) hNle'
      _ = ((e:ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q:ℝ) * d) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by linarith),
            Real.log_pow]
          push_cast
          ring
  have hlogt : Real.log t ≤ Ct * Real.log x := by
    calc Real.log t ≤ Real.log (x ^ Ct) := Real.log_le_log (by linarith) htx
      _ = Ct * Real.log x := Real.log_rpow hxpos _
  have hE : (e:ℝ) * Real.log 2 ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have h := Real.log_le_log (by positivity) hP.2
    rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos _).ne',
      Real.log_rpow hxpos] at h
    exact h
  have hC : Ct * Real.log x ≤ |Ct| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlogx
  nlinarith [mul_nonneg hlogx (by linarith : (0:ℝ) ≤ 1 - 8 * eps)]
