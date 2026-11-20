import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg.ThQuot

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
theorem ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_nat_mul (n : ℕ) (z : ℂ) : ee ((n : ℂ) * z) = ee z ^ n := by
  unfold ee
  rw [← Complex.exp_nat_mul]; congr 1; ring

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_neg (z : ℂ) : ee (-z) = (ee z)⁻¹ := by
  unfold ee
  rw [← Complex.exp_neg]; congr 1; ring

/- English proof (translation)
Unfold `ee`. Rewrite using `[Complex.norm_exp, Real.exp_lt_one_iff]`. Establish `h1` using `τ.im_pos`. Establish `h2` using `Real.pi_pos`. Establish `: (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im)`.

Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite using `[this]`. Establish `: 0 < 2 * Real.pi * τ.im` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

/- English proof (translation)
Establish `h : Summable (fun n : ℕ => -(q ^ (n + 1) * t))`. Establish `h0` using `(summable_geometric_of_norm_lt_one hq).mul_right (q * t)`. Use `h0.neg.congr fun n => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify `Complex.multipliable_one_add_of_summable h` using `[sub_eq_add_neg]`.
-/
theorem multipliable_one_sub {q : ℂ} (hq : ‖q‖ < 1) (t : ℂ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1) * t) := by
  have h : Summable (fun n : ℕ => -(q ^ (n + 1) * t)) := by
    have h0 := (summable_geometric_of_norm_lt_one hq).mul_right (q * t)
    refine h0.neg.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable h

/- English proof (translation)
Unfold `HasProd at *`. Simplify using `only [Finset.prod_div_distrib, Finset.prod_pow]`. Conclude with `(hf.pow k).div hg hb`.
-/
theorem hasProd_pow_div {f g : ℕ → ℂ} {a b : ℂ} (hf : HasProd f a) (hg : HasProd g b) (hb : b ≠ 0) (k : ℕ) :
    HasProd (fun n => f n ^ k / g n) (a ^ k / b) := by
  unfold HasProd at *
  simp only [Finset.prod_div_distrib, Finset.prod_pow]
  exact (hf.pow k).div hg hb

/- English proof (translation)
Establish `h2 : ¬ 2 ∣ c` using `fun hd => by`. Use `Nat.Coprime.coprime_dvd_left hd h` as an intermediate fact. Evaluate the numerical expressions using `at this`. Establish `h3 : ¬ 3 ∣ c` using `fun hd => by`. Use `Nat.Coprime.coprime_dvd_left hd h` as an intermediate fact.

Evaluate the numerical expressions using `at this`. Take `⟨m, hm⟩ : ∃ m, c = 6 * m + 1 ∨ c = 6 * m + 5` from `⟨c / 6, by omega⟩`. Break down `hm with rfl | rfl` into its components or cases. Conclude with `⟨3 * m ^ 2 + m, by ring⟩`. Conclude with `⟨3 * m ^ 2 + 5 * m + 2, by ring⟩`.
-/
theorem twelve_dvd {c : ℕ} (h1 : 1 < c) (h : Nat.Coprime c 6) : ∃ k, c ^ 2 = 12 * k + 1 := by
  have h2 : ¬ 2 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  have h3 : ¬ 3 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  obtain ⟨m, hm⟩ : ∃ m, c = 6 * m + 1 ∨ c = 6 * m + 5 := ⟨c / 6, by omega⟩
  rcases hm with rfl | rfl
  · exact ⟨3 * m ^ 2 + m, by ring⟩
  · exact ⟨3 * m ^ 2 + 5 * m + 2, by ring⟩

/- English proof (translation)
Introduce `c τ z h1 hc hne`. Take `⟨k, hk⟩` from `twelve_dvd h1 hc`. Establish `hodd : Odd c`. Establish `: Odd (c ^ 2)` using `⟨6 * k, by omega⟩`. Conclude with `(Nat.odd_pow_iff (by norm_num)).mp this`.

Take `⟨j, hj⟩` from `hodd`. Establish `hq` using `norm_ee_lt_one τ`. Use `set s := ee (z / 2) with hs`. Use `set u := ee ((τ : ℂ) / 12) with hu`. Establish `hs0 : s ≠ 0` using `ee_ne_zero _`.

Establish `hu0 : u ≠ 0` using `ee_ne_zero _`. Establish `ht : ee z = s ^ 2`. Rewrite using `[hs, ← ee_nat_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hqu : ee (τ : ℂ) = u ^ 12`. Rewrite using `[hu, ← ee_nat_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e1 : ee (-z / 2) = s⁻¹` using `by rw [neg_div, ee_neg]`. Establish `e2 : ee ((c : ℂ) * z / 2) = s ^ c` using `by rw [mul_div_assoc, ee_nat_mul]`. Establish `e3 : ee (-((c : ℂ) * z) / 2) = (s ^ c)⁻¹` using `by rw [neg_div, ee_neg, e2]`. Establish `e4 : ee ((c : ℂ) * z) = ee z ^ c` using `ee_nat_mul c z`.

Unfold `th at hne ⊢`. Unfold `cth`. Rewrite `hne`, the goal using `[e2, e3, e4]`. Rewrite `*` using `[e1, ← hs, ← hu]`. Establish `mf` using `((multipliable_one_sub hq (ee z)).mul (multipliable_one_sub hq (ee z)⁻¹)).hasProd`.

Establish `mg` using `((multipliable_one_sub hq (ee z ^ c)).mul (multipliable_one_sub hq (ee z ^ c)⁻¹)).hasProd`. Use `set A := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) with hA`. Use `set B := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z ^ c) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z ^ c)⁻¹) with hB`. Establish `hB0 : B ≠ 0` using `right_ne_zero_of_mul hne`. Establish `hd : s ^ c - (s ^ c)⁻¹ ≠ 0` using `right_ne_zero_of_mul (left_ne_zero_of_mul hne)`.

Establish `hP : ∏' m : ℕ, cthFac c (ee (τ : ℂ)) (ee z) (m + 1) = A ^ (c ^ 2) / B`. Use `hasProd_pow_div mf mg hB0 (c ^ 2)` as an intermediate fact. Use `(HasProd.tprod_eq ?_)` and prove the remaining obligations. Simplify `this` using `only [cthFac, mul_pow]`. Rewrite using `[hP]`.

Establish `x1 : (c ^ 2 - 1) / 12 = k` using `by omega`. Establish `x2 : c * (c - 1) / 2 = c * j`. Establish `: c * (c - 1) = 2 * (c * j)`. Establish `: c - 1 = 2 * j` using `by omega`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers. Establish `x3 : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c * j : ℕ) : ℤ)`. Establish `: (c : ℤ) - (c : ℤ) ^ 2 = 2 * (-((c * j : ℕ) : ℤ))`. Substitute `hj` using the available equality.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[x1, x2, x3, zpow_neg, zpow_natCast, ht, hqu]`.

Establish `hsc : s ^ c ≠ 0` using `pow_ne_zero _ hs0`. Establish `y1 : s ^ c - (s ^ c)⁻¹ = -(1 - (s ^ 2) ^ c) / s ^ c` using `by field_simp; ring`. Establish `y2 : s - s⁻¹ = -(1 - s ^ 2) / s` using `by field_simp; ring`. Establish `hd' : 1 - (s ^ 2) ^ c ≠ 0`. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[y1, h]`. Simplify using the standard rewrite rules. Establish `hc2 : Odd (c ^ 2)` using `⟨6 * k, by omega⟩`. Establish `y3 : s ^ (c ^ 2) = s ^ c * (s ^ 2) ^ (c * j)`.

Rewrite using `[← pow_mul, ← pow_add]`. Use `congr 1`. Substitute `hj` using the available equality. Expand and normalize the polynomial expressions, which then agree. Establish `y4 : u ^ (c ^ 2) = u * (u ^ 12) ^ k` using `by rw [hk, ← pow_mul]; ring`.

Establish `y5 : ((-1 : ℂ)) ^ (c * j) * (-1) ^ (c * j) = 1` using `by rw [← mul_pow]; simp`. Rewrite using `[y1, y2, mul_pow, mul_pow, div_pow, hc2.neg_pow, y3, y4, neg_pow (s ^ 2)]`. Establish `hS : (s ^ 2) ^ (c * j) ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ hs0)`. Generalize the expression as in `(s ^ 2) ^ (c * j) = S at *`. Generalize the expression as in `(1 - (s ^ 2) ^ c) = D at *`.

Generalize the expression as in `(1 - s ^ 2) ^ (c ^ 2) = E at *`. Generalize the expression as in `s ^ c = T at *`. Generalize the expression as in `A ^ (c ^ 2) = A' at *`. Generalize the expression as in `(u ^ 12) ^ k = U at *`. Generalize the expression as in `((-1 : ℂ)) ^ (c * j) = ε at *`.

Establish `hε : ε ≠ 0` using `left_ne_zero_of_mul (y5 ▸ one_ne_zero)`. Establish `hi : ε⁻¹ = ε` using `inv_eq_of_mul_eq_one_right y5`. Rewrite using `[mul_inv, hi]`. Clear the denominators using the available nonvanishing facts.
-/
theorem cth_eq_th_quot : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → th ((c : ℂ) * z) τ ≠ 0 →
    cth c (ee (τ : ℂ)) (ee z) = (-1) ^ (c * (c - 1) / 2) * th z τ ^ (c ^ 2) / th ((c : ℂ) * z) τ := by
  intro c τ z h1 hc hne
  obtain ⟨k, hk⟩ := twelve_dvd h1 hc
  have hodd : Odd c := by
    have : Odd (c ^ 2) := ⟨6 * k, by omega⟩
    exact (Nat.odd_pow_iff (by norm_num)).mp this
  obtain ⟨j, hj⟩ := hodd
  have hq := norm_ee_lt_one τ
  set s := ee (z / 2) with hs
  set u := ee ((τ : ℂ) / 12) with hu
  have hs0 : s ≠ 0 := ee_ne_zero _
  have hu0 : u ≠ 0 := ee_ne_zero _
  have ht : ee z = s ^ 2 := by
    rw [hs, ← ee_nat_mul]; congr 1; push_cast; ring
  have hqu : ee (τ : ℂ) = u ^ 12 := by
    rw [hu, ← ee_nat_mul]; congr 1; push_cast; ring
  have e1 : ee (-z / 2) = s⁻¹ := by rw [neg_div, ee_neg]
  have e2 : ee ((c : ℂ) * z / 2) = s ^ c := by rw [mul_div_assoc, ee_nat_mul]
  have e3 : ee (-((c : ℂ) * z) / 2) = (s ^ c)⁻¹ := by rw [neg_div, ee_neg, e2]
  have e4 : ee ((c : ℂ) * z) = ee z ^ c := ee_nat_mul c z
  unfold th at hne ⊢
  unfold cth
  rw [e2, e3, e4] at hne ⊢
  rw [e1, ← hs, ← hu] at *
  have mf := ((multipliable_one_sub hq (ee z)).mul (multipliable_one_sub hq (ee z)⁻¹)).hasProd
  have mg := ((multipliable_one_sub hq (ee z ^ c)).mul (multipliable_one_sub hq (ee z ^ c)⁻¹)).hasProd
  set A := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) with hA
  set B := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z ^ c) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z ^ c)⁻¹) with hB
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hne
  have hd : s ^ c - (s ^ c)⁻¹ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hP : ∏' m : ℕ, cthFac c (ee (τ : ℂ)) (ee z) (m + 1) = A ^ (c ^ 2) / B := by
    have := hasProd_pow_div mf mg hB0 (c ^ 2)
    refine (HasProd.tprod_eq ?_)
    simpa only [cthFac, mul_pow] using this
  rw [hP]
  have x1 : (c ^ 2 - 1) / 12 = k := by omega
  have x2 : c * (c - 1) / 2 = c * j := by
    have : c * (c - 1) = 2 * (c * j) := by
      have : c - 1 = 2 * j := by omega
      rw [this]; ring
    omega
  have x3 : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c * j : ℕ) : ℤ) := by
    have : (c : ℤ) - (c : ℤ) ^ 2 = 2 * (-((c * j : ℕ) : ℤ)) := by
      subst hj; push_cast; ring
    rw [this]; omega
  rw [x1, x2, x3, zpow_neg, zpow_natCast, ht, hqu]
  have hsc : s ^ c ≠ 0 := pow_ne_zero _ hs0
  have y1 : s ^ c - (s ^ c)⁻¹ = -(1 - (s ^ 2) ^ c) / s ^ c := by
    field_simp; ring
  have y2 : s - s⁻¹ = -(1 - s ^ 2) / s := by field_simp; ring
  have hd' : 1 - (s ^ 2) ^ c ≠ 0 := by
    intro h; apply hd; rw [y1, h]; simp
  have hc2 : Odd (c ^ 2) := ⟨6 * k, by omega⟩
  have y3 : s ^ (c ^ 2) = s ^ c * (s ^ 2) ^ (c * j) := by
    rw [← pow_mul, ← pow_add]; congr 1; subst hj; ring
  have y4 : u ^ (c ^ 2) = u * (u ^ 12) ^ k := by rw [hk, ← pow_mul]; ring
  have y5 : ((-1 : ℂ)) ^ (c * j) * (-1) ^ (c * j) = 1 := by rw [← mul_pow]; simp
  rw [y1, y2, mul_pow, mul_pow, div_pow, hc2.neg_pow, y3, y4, neg_pow (s ^ 2)]
  have hS : (s ^ 2) ^ (c * j) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hs0)
  generalize (s ^ 2) ^ (c * j) = S at *
  generalize (1 - (s ^ 2) ^ c) = D at *
  generalize (1 - s ^ 2) ^ (c ^ 2) = E at *
  generalize s ^ c = T at *
  generalize A ^ (c ^ 2) = A' at *
  generalize (u ^ 12) ^ k = U at *
  generalize ((-1 : ℂ)) ^ (c * j) = ε at *
  have hε : ε ≠ 0 := left_ne_zero_of_mul (y5 ▸ one_ne_zero)
  have hi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right y5
  rw [mul_inv, hi]
  field_simp

end GlobalTheory.Sieg.ThQuot
