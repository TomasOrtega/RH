import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

noncomputable section

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.ConjSize

variable {K : Type} [Field K] (ι τ : K →+* ℂ)

def Sz (z : ℂ) (B : ℝ) : Prop := ∃ y, ι y = z ∧ ‖τ y‖ ≤ B

def Un (z : ℂ) : Prop := ∃ y, ι y = z ∧ ‖τ y‖ = 1

variable {ι τ}

/- English proof (translation)
The claim follows from `let ⟨_, _, h⟩ := h; (norm_nonneg _).trans h`.
-/
theorem Sz.nonneg {z : ℂ} {B : ℝ} (h : Sz ι τ z B) : 0 ≤ B := let ⟨_, _, h⟩ := h; (norm_nonneg _).trans h

/- English proof (translation)
The claim follows from `let ⟨y, e, h⟩ := h; ⟨y, e, h.trans hB⟩`.
-/
theorem Sz.mono {z : ℂ} {B B' : ℝ} (h : Sz ι τ z B) (hB : B ≤ B') : Sz ι τ z B' :=
  let ⟨y, e, h⟩ := h; ⟨y, e, h.trans hB⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, map_zero _, by simpa using hB⟩`.
-/
theorem Sz.zero {B : ℝ} (hB : 0 ≤ B) : Sz ι τ 0 B := ⟨0, map_zero _, by simpa using hB⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, map_one _, by simp⟩`.
-/
theorem Sz.one : Sz ι τ 1 1 := ⟨1, map_one _, by simp⟩

/- English proof (translation)
Establish `h0` using `h.nonneg`. Take `⟨y, e, hy⟩` from `h`. Take `⟨y', e', hy'⟩` from `h'`. Conclude with `⟨y * y', by rw [map_mul, e, e'], by rw [map_mul, norm_mul]; exact mul_le_mul hy hy' (norm_nonneg _) h0⟩`.
-/
theorem Sz.mul {z z' : ℂ} {B B' : ℝ} (h : Sz ι τ z B) (h' : Sz ι τ z' B') : Sz ι τ (z * z') (B * B') := by
  have h0 := h.nonneg
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  exact ⟨y * y', by rw [map_mul, e, e'], by rw [map_mul, norm_mul]; exact mul_le_mul hy hy' (norm_nonneg _) h0⟩

/- English proof (translation)
Take `⟨y, e, hy⟩` from `h`. Take `⟨y', e', hy'⟩` from `h'`. Conclude with `⟨y + y', by rw [map_add, e, e'], by rw [map_add]; exact (norm_add_le _ _).trans (add_le_add hy hy')⟩`.
-/
theorem Sz.add {z z' : ℂ} {B B' : ℝ} (h : Sz ι τ z B) (h' : Sz ι τ z' B') : Sz ι τ (z + z') (B + B') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  exact ⟨y + y', by rw [map_add, e, e'], by rw [map_add]; exact (norm_add_le _ _).trans (add_le_add hy hy')⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using Sz.one`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul h`.
-/
theorem Sz.pow {z : ℂ} {B : ℝ} (h : Sz ι τ z B) (n : ℕ) : Sz ι τ (z ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using Sz.one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Sz.zero le_rfl`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem Sz.sum {α : Type*} (s : Finset α) {f : α → ℂ} {B : α → ℝ} (h : ∀ i ∈ s, Sz ι τ (f i) (B i)) :
    Sz ι τ (∑ i ∈ s, f i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sz.zero le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Simplify using `using Sz.sum s h`.
-/
theorem Sz.sum_card {α : Type*} (s : Finset α) {f : α → ℂ} {B : ℝ} (h : ∀ i ∈ s, Sz ι τ (f i) B) :
    Sz ι τ (∑ i ∈ s, f i) (s.card * B) := by
  simpa using Sz.sum s h

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact Sz.one`. Consider the case `cons a l ih`. Simplify using `using (h a List.mem_cons_self).mul (ih fun z hz => h z (List.mem_cons_of_mem _ hz))`.
-/
theorem Sz.list_prod {l : List ℂ} (h : ∀ z ∈ l, Sz ι τ z 1) : Sz ι τ l.prod 1 := by
  induction l with
  | nil => exact Sz.one
  | cons a l ih =>
    simpa using (h a List.mem_cons_self).mul (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

/- English proof (translation)
Use `haveI : CharZero K := ι.charZero`. Use `⟨(q : K), map_ratCast _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`.
-/
theorem Sz.rat (q : ℚ) : Sz ι τ (q : ℂ) |(q : ℝ)| := by
  haveI : CharZero K := ι.charZero
  refine ⟨(q : K), map_ratCast _ _, ?_⟩
  rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

/- English proof (translation)
Simplify using `using Sz.rat (ι := ι) (τ := τ) ((n : ℚ)⁻¹)`.
-/
theorem Sz.inv_nat (n : ℕ) : Sz ι τ ((n : ℂ)⁻¹) ((n : ℝ)⁻¹) := by
  simpa using Sz.rat (ι := ι) (τ := τ) ((n : ℚ)⁻¹)

/- English proof (translation)
The claim follows from `let ⟨y, e, h⟩ := h; ⟨y, e, h.le⟩`.
-/
theorem Un.sz {z : ℂ} (h : Un ι τ z) : Sz ι τ z 1 := let ⟨y, e, h⟩ := h; ⟨y, e, h.le⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, map_one _, by simp⟩`.
-/
theorem Un.one : Un ι τ 1 := ⟨1, map_one _, by simp⟩

/- English proof (translation)
Take `⟨y, e, hy⟩` from `h`. Take `⟨y', e', hy'⟩` from `h'`. Conclude with `⟨y * y', by rw [map_mul, e, e'], by rw [map_mul, norm_mul, hy, hy', one_mul]⟩`.
-/
theorem Un.mul {z z' : ℂ} (h : Un ι τ z) (h' : Un ι τ z') : Un ι τ (z * z') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  exact ⟨y * y', by rw [map_mul, e, e'], by rw [map_mul, norm_mul, hy, hy', one_mul]⟩

/- English proof (translation)
Take `⟨y, e, hy⟩` from `h`. Conclude with `⟨y⁻¹, by rw [map_inv₀, e], by rw [map_inv₀, norm_inv, hy, inv_one]⟩`.
-/
theorem Un.inv {z : ℂ} (h : Un ι τ z) : Un ι τ z⁻¹ := by
  obtain ⟨y, e, hy⟩ := h
  exact ⟨y⁻¹, by rw [map_inv₀, e], by rw [map_inv₀, norm_inv, hy, inv_one]⟩

/- English proof (translation)
Simplify using `using h.mul h'.sz`.
-/
theorem Sz.mul_un {z z' : ℂ} {B : ℝ} (h : Sz ι τ z B) (h' : Un ι τ z') : Sz ι τ (z * z') B := by
  simpa using h.mul h'.sz

/- English proof (translation)
Simplify using `using h.sz.mul h'`.
-/
theorem Un.mul_sz {z z' : ℂ} {B : ℝ} (h : Un ι τ z) (h' : Sz ι τ z' B) : Sz ι τ (z * z') B := by
  simpa using h.sz.mul h'

/- English proof (translation)
Take `⟨y, rfl⟩` from `hz`. Establish `h1 : y ^ n = 1` using `ι.injective (by rw [map_pow, h, map_one])`. Establish `h2 : ‖τ y‖ ^ n = 1` using `by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]`. Conclude with `⟨y, rfl, (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2⟩`.
-/
theorem Un.of_pow_eq_one {z : ℂ} (hz : z ∈ Set.range ι) {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) : Un ι τ z := by
  obtain ⟨y, rfl⟩ := hz
  have h1 : y ^ n = 1 := ι.injective (by rw [map_pow, h, map_one])
  have h2 : ‖τ y‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact ⟨y, rfl, (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `haveI : CharZero K := ι.charZero`. Take `⟨y, hy⟩` from `h`. Take `⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = nabs k u` from `⟨(resCard k : ℚ) ^ (-SmGL.ord k u), by`. Rewrite using `[GlobalTheory.LGrp.nabs_eq_zpow]`. Use `push_cast`.

Use the proof step `rfl⟩`. Establish `h2 : apow u (1 / 2) ^ 2 = (r : ℂ)`. Rewrite using `[sq, ← apow_add, apow, ← hr]`. Evaluate the numerical expressions. Establish `h3 : y ^ 2 = (r : K)` using `ι.injective (by rw [map_pow, hy, h2, map_ratCast])`.

Use `⟨y, hy, Real.le_sqrt_of_sq_le ?_⟩` and prove the remaining obligations. Rewrite using `[← norm_pow, ← map_pow, h3, map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, hr, Real.norm_of_nonneg (GlobalTheory.SplitWeil.Model.nabs_pos u).le]`.
-/
theorem sz_apow_half (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) : Sz ι τ (apow u (1 / 2)) (Real.sqrt (nabs k u)) := by
  haveI : CharZero K := ι.charZero
  obtain ⟨y, hy⟩ := h
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = nabs k u := ⟨(resCard k : ℚ) ^ (-SmGL.ord k u), by
    rw [GlobalTheory.LGrp.nabs_eq_zpow]; push_cast; rfl⟩
  have h2 : apow u (1 / 2) ^ 2 = (r : ℂ) := by
    rw [sq, ← apow_add, apow, ← hr]; norm_num
  have h3 : y ^ 2 = (r : K) := ι.injective (by rw [map_pow, hy, h2, map_ratCast])
  refine ⟨y, hy, Real.le_sqrt_of_sq_le ?_⟩
  rw [← norm_pow, ← map_pow, h3, map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, hr,
    Real.norm_of_nonneg (GlobalTheory.SplitWeil.Model.nabs_pos u).le]

/- English proof (translation)
Establish `: apow u ((n : ℂ) / 2) = apow u (1 / 2) ^ n`. Rewrite using `[apow, apow, ← Complex.cpow_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Use `((sz_apow_half u h).mono ?_).pow n` and prove the remaining obligations. Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sz_apow_nat_half (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) (n : ℕ) {c : ℝ} (hc : 1 ≤ c) (hu : nabs k u ≤ c) :
    Sz ι τ (apow u ((n : ℂ) / 2)) (c ^ n) := by
  have : apow u ((n : ℂ) / 2) = apow u (1 / 2) ^ n := by
    rw [apow, apow, ← Complex.cpow_nat_mul]; congr 1; ring
  rw [this]
  refine ((sz_apow_half u h).mono ?_).pow n
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/- English proof (translation)
Use `borelize k`. Simplify using `using sz_apow_nat_half (τ := τ) u h n le_rfl (GlobalTheory.SplitWeil.Model.nabs_le_one u hu)`.
-/
theorem sz_apow_of_le_one (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) (n : ℕ) (hu : valuation k (u : k) ≤ 1) :
    Sz ι τ (apow u ((n : ℂ) / 2)) 1 := by
  borelize k
  simpa using sz_apow_nat_half (τ := τ) u h n le_rfl (GlobalTheory.SplitWeil.Model.nabs_le_one u hu)

end Local

end GlobalTheory.ConjSize

end
