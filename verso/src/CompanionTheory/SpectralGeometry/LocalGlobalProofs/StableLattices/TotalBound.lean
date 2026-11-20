import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFar

open CompanionTheory.RgExh.U

/- English proof (translation)
The claim follows from `|x a0| ≤ B + M + K := by have hm : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨a0, h0⟩ have e : (s.card : ℝ) * x a0 = ∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a) + ∑ a ∈ s, (x a0 - x a) := by simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] ring hav …`.
-/
theorem x_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (h0 : a0 ∈ s) (B M K : ℝ) (hK0 : 0 ≤ K)
    (hy : ∀ a ∈ s, |y a| ≤ B) (hM : ∀ a ∈ s, |x a0 - x a| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    |x a0| ≤ B + M + K := by
  have hm : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a0, h0⟩
  have e : (s.card : ℝ) * x a0 = ∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a) + ∑ a ∈ s, (x a0 - x a) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h1 : |∑ a ∈ s, y a| ≤ (s.card : ℝ) * B := by
    calc |∑ a ∈ s, y a| ≤ ∑ a ∈ s, |y a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, B := Finset.sum_le_sum hy
      _ = (s.card : ℝ) * B := by simp
  have h2 : |∑ a ∈ s, (x a0 - x a)| ≤ (s.card : ℝ) * M := by
    calc |∑ a ∈ s, (x a0 - x a)| ≤ ∑ a ∈ s, |x a0 - x a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, M := Finset.sum_le_sum hM
      _ = (s.card : ℝ) * M := by simp
  have h3 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * B + K + (s.card : ℝ) * M := by
    have : |(s.card : ℝ) * x a0| = (s.card : ℝ) * |x a0| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s.card : ℝ))]
    rw [← this, e]
    calc _ ≤ |∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := abs_add_le _ _
      _ ≤ |∑ a ∈ s, y a| + |∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  have h4 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * (B + M + K) := by nlinarith
  exact le_of_mul_le_mul_left h4 (by linarith)

/- English proof (translation)
Establish `h1 : ∀ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) + 2 * x a0 * (y a - x a) ≤ y a ^ 2 - x a ^ 2`. Introduce `a ha`. Establish `he : (x a - x a0) ^ 2 ≤ M ^ 2` using `sq_le_sq' (by linarith [(abs_le.mp (hM a ha)).1]) (abs_le.mp (hM a ha)).2`. Use polynomial arithmetic with `[sq_nonneg ((y a - x a) + 2 * (x a - x a0))]`. Establish `h2` using `Finset.sum_le_sum h1`.

Rewrite `h2` using `[Finset.sum_add_distrib, ← Finset.mul_sum]`. Establish `h3 : -(2 * X * K) ≤ 2 * x a0 * ∑ a ∈ s, (y a - x a)`. Establish `: |x a0 * ∑ a ∈ s, (y a - x a)| ≤ X * K`. Rewrite using `[abs_mul]`. Conclude with `mul_le_mul hX hK (abs_nonneg _) hX0`.

Use polynomial arithmetic with `[(abs_le.mp this).1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fiber_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (M X K : ℝ) (hX0 : 0 ≤ X)
    (hX : |x a0| ≤ X) (hM : ∀ a ∈ s, |x a - x a0| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    ∑ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K ≤ ∑ a ∈ s, (y a ^ 2 - x a ^ 2) := by
  have h1 : ∀ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) + 2 * x a0 * (y a - x a) ≤ y a ^ 2 - x a ^ 2 := by
    intro a ha
    have he : (x a - x a0) ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [(abs_le.mp (hM a ha)).1])
      (abs_le.mp (hM a ha)).2
    nlinarith [sq_nonneg ((y a - x a) + 2 * (x a - x a0))]
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
  have h3 : -(2 * X * K) ≤ 2 * x a0 * ∑ a ∈ s, (y a - x a) := by
    have : |x a0 * ∑ a ∈ s, (y a - x a)| ≤ X * K := by
      rw [abs_mul]
      exact mul_le_mul hX hK (abs_nonneg _) hX0
    nlinarith [(abs_le.mp this).1]
  linarith

/- English proof (translation)
Establish `hmaps : ∀ a ∈ (univ : Finset (Fin n)), lev a ∈ univ.image lev` using `fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps (fun a => y a ^ 2 - x a ^ 2), ← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (y a - x a) ^ 2 / 2 - 2 * M ^ 2)]`. Establish `hcard : ((univ.image lev).card : ℝ) ≤ n`. Use `Finset.card_image_le (s := (univ : Finset (Fin n))) (f := lev)` as an intermediate fact. Simplify using `only [Finset.card_univ, Fintype.card_fin] at this`.

Conclude with `this` after adjusting the coercions. Establish `h1 : ∑ c ∈ univ.image lev, (∑ a ∈ univ.filter (fun a => lev a = c), ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K) ≤ ∑ c ∈ univ.image lev, ∑ a ∈ univ.filter (fun a => lev a = c), (y a ^ 2 - x a ^ 2)`. Use `Finset.sum_le_sum fun c hc => ?_` and prove the remaining obligations. Take `⟨a0, -, rfl⟩` from `Finset.mem_image.mp hc`. Use `fiber_bound _ x y a0 M X K hX0 (hX a0) (fun a ha => ?_) (hK _)` and prove the remaining obligations.

Conclude with `hM a a0 (Finset.mem_filter.mp ha).2`. Rewrite `h1` using `[Finset.sum_sub_distrib]`. Simplify using `only [Finset.sum_const, nsmul_eq_mul] at h1`. Establish `h2 : ((univ.image lev).card : ℝ) * (2 * X * K) ≤ n * (2 * X * K)` using `mul_le_mul_of_nonneg_right hcard (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem total_bound {n : ℕ} (x y : Fin n → ℝ) (lev : Fin n → ℕ) (M X K : ℝ) (hX0 : 0 ≤ X) (hK0 : 0 ≤ K)
    (hX : ∀ a, |x a| ≤ X) (hM : ∀ a b, lev a = lev b → |x a - x b| ≤ M)
    (hK : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K) :
    ∑ a, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - n * (2 * X * K) ≤ ∑ a, (y a ^ 2 - x a ^ 2) := by
  have hmaps : ∀ a ∈ (univ : Finset (Fin n)), lev a ∈ univ.image lev :=
    fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun a => y a ^ 2 - x a ^ 2),
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (y a - x a) ^ 2 / 2 - 2 * M ^ 2)]
  have hcard : ((univ.image lev).card : ℝ) ≤ n := by
    have := Finset.card_image_le (s := (univ : Finset (Fin n))) (f := lev)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h1 : ∑ c ∈ univ.image lev, (∑ a ∈ univ.filter (fun a => lev a = c),
      ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K) ≤
      ∑ c ∈ univ.image lev, ∑ a ∈ univ.filter (fun a => lev a = c), (y a ^ 2 - x a ^ 2) := by
    refine Finset.sum_le_sum fun c hc => ?_
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp hc
    refine fiber_bound _ x y a0 M X K hX0 (hX a0) (fun a ha => ?_) (hK _)
    exact hM a a0 (Finset.mem_filter.mp ha).2
  rw [Finset.sum_sub_distrib] at h1
  simp only [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((univ.image lev).card : ℝ) * (2 * X * K) ≤ n * (2 * X * K) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

/- English proof (translation)
Establish `h1 : d a ^ 2 + d b ^ 2 ≤ ∑ c, d c ^ 2`. Rewrite using `[← Finset.sum_pair (f := fun c => d c ^ 2) hab]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)`. Establish `h2 : D ^ 2 ≤ (d a - d b) ^ 2`. Rewrite using `[← sq_abs (d a - d b)]`.

Conclude with `pow_le_pow_left₀ hD h 2`. Use polynomial arithmetic with `[sq_nonneg (d a + d b)]`.
-/
theorem two_bound {n : ℕ} (d : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) (D : ℝ) (hD : 0 ≤ D)
    (h : D ≤ |d a - d b|) : D ^ 2 / 2 ≤ ∑ c, d c ^ 2 := by
  have h1 : d a ^ 2 + d b ^ 2 ≤ ∑ c, d c ^ 2 := by
    rw [← Finset.sum_pair (f := fun c => d c ^ 2) hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have h2 : D ^ 2 ≤ (d a - d b) ^ 2 := by
    rw [← sq_abs (d a - d b)]
    exact pow_le_pow_left₀ hD h 2
  nlinarith [sq_nonneg (d a + d b)]

/- English proof (translation)
Introduce `n C δ K hδ`. Take `⟨C', hC'⟩ : ∃ C' : ℝ, C' = |C|` from `⟨_, rfl⟩`. Take `⟨K', hK'⟩ : ∃ K' : ℝ, K' = |K|` from `⟨_, rfl⟩`. Take `⟨M, hMdef⟩ : ∃ M : ℝ, M = n * Lc n` from `⟨_, rfl⟩`. Establish `hC0 : 0 ≤ C'` using `hC' ▸ abs_nonneg _`.

Establish `hK0 : 0 ≤ K'` using `hK' ▸ abs_nonneg _`. Establish `hM0 : 0 ≤ M` using `by rw [hMdef, Lc]; positivity`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = 2 * n * M ^ 2 + 2 * n * K' * (M + K') + 2 * (n : ℝ) ^ 2 * (M + K') + (n : ℝ) ^ 3 + n * C' ^ 2 + K'` from `⟨_, rfl⟩`. Take `⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = 2 * n * K' * C' + 2 * (n : ℝ) ^ 2 * C'` from `⟨_, rfl⟩`.

Establish `hA0 : 0 ≤ A` using `by rw [hA]; positivity`. Establish `hB0 : 0 ≤ Bc` using `by rw [hBc]; positivity`. Use `⟨1 + 2 * M / δ + 16 * (A + Bc) / δ ^ 2, ?_⟩` and prove the remaining obligations. Introduce `χ x r lev σ N _ _ hr hsp hblk hineq hsep hbd hN a b hab`. Assume the negation of the conclusion as `hne`.

Establish `hq1 : 0 ≤ 2 * M / δ` using `by positivity`. Establish `hq2 : 0 ≤ 16 * (A + Bc) / δ ^ 2` using `by positivity`. Establish `hN1 : 1 ≤ N` using `by linarith`. Establish `hN0 : 0 ≤ N` using `by linarith`. Establish `hδN : 2 * M ≤ δ * N`.

Establish `: 2 * M / δ ≤ N` using `by linarith`. Rewrite `this` using `[div_le_iff₀ hδ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hδ2 : 16 * (A + Bc) + δ ^ 2 ≤ δ ^ 2 * N`. Establish `: 16 * (A + Bc) / δ ^ 2 ≤ N - 1` using `by linarith`.

Rewrite `this` using `[div_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun a => (χ (σ a)).re` from `⟨_, rfl⟩`. Establish `hyb : ∀ a, |y a| ≤ C' * N`. Introduce `a`.

Rewrite using `[hy]`. Use `(hbd (σ a)).1.trans ?_` and prove the remaining obligations. Rewrite using `[hC']`. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self C) hN0`. Establish `hblk' : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K'`.

Introduce `c`. Establish `h1` using `Complex.abs_re_le_norm (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a) - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ))`. Establish `h2 : (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a) - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ)).re = ∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)`. Rewrite using `[hy, Finset.sum_sub_distrib]`. Simplify using `[Complex.re_sum]`.

Rewrite `h1` using `[h2]`. Conclude with `h1.trans ((hblk c).trans (hK' ▸ le_abs_self K))`. Establish `hspM : ∀ a b, lev a = lev b → |x a - x b| ≤ M` using `fun a b h => hMdef ▸ hsp a b h`. Take `⟨X, hXdef⟩ : ∃ X : ℝ, X = C' * N + M + K'` from `⟨_, rfl⟩`. Establish `hX0 : 0 ≤ X` using `by rw [hXdef]; positivity`.

Establish `hX : ∀ a, |x a| ≤ X`. Introduce `a`. Rewrite using `[hXdef]`. Use `x_bound (univ.filter fun c => lev c = lev a) x y a (by simp) _ _ _ hK0 (fun c _ => hyb c) (fun c hc => hspM a c (Finset.mem_filter.mp hc).2.symm) (hblk' _)` and prove the remaining obligations. Establish `hlow` using `total_bound x y lev M X K' hX0 hK0 hX hspM hblk'`.

Establish `hD : (δ * N - M) ^ 2 / 2 ≤ ∑ c, (y c - x c) ^ 2`. Use `two_bound (fun c => y c - x c) a b hne _ (by linarith) ?_` and prove the remaining obligations. Establish `h1 : δ * N ≤ |y a - y b|`. Rewrite using `[hy]`. Conclude with `hsep (σ a) (σ b) (fun h => hne (σ.injective h))`.

Establish `h2` using `hspM a b hab`. Establish `h3 : |y a - y b| ≤ |(y a - x a) - (y b - x b)| + |x a - x b|`. Establish `: y a - y b = ((y a - x a) - (y b - x b)) + (x a - x b)` using `by ring`. Rewrite using `[this]`. Conclude with `abs_add_le _ _`.

Use `show δ * N - M ≤ |(y a - x a) - (y b - x b)|`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hYsum : ∑ a, y a ^ 2 = ∑ a, (χ a).re ^ 2`. Rewrite using `[hy]`. Conclude with `Equiv.sum_comp σ (fun a => (χ a).re ^ 2)`.

Establish `hIm : ∑ a, (χ a).im ^ 2 ≤ n * C' ^ 2`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← sq_abs (χ a).im]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) ((hbd a).2.trans (hC' ▸ le_abs_self C)) 2`.

Use `_ = n * C' ^ 2 := by simp`. Establish `hxr : ∑ a, (x a - r a) ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2)`. Establish `: ∀ a ∈ (univ : Finset (Fin n)), (x a - r a) ^ 2 ≤ x a ^ 2 + (2 * X * n + (n : ℝ) ^ 2)`. Introduce `a _`. Establish `h1 : |x a * r a| ≤ X * n`.

Rewrite using `[abs_mul]`. Conclude with `mul_le_mul (hX a) (hr a) (abs_nonneg _) hX0`. Establish `h2 : r a ^ 2 ≤ (n : ℝ) ^ 2`. Rewrite using `[← sq_abs (r a)]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hr a) 2`.

Use polynomial arithmetic with `[(abs_le.mp h1).1]`. Use `(Finset.sum_le_sum this).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Conclude with `le_refl _`.

Establish `hKK : K ≤ K'` using `hK' ▸ le_abs_self K`. Rewrite `hineq` using `[Finset.sum_sub_distrib]`. Establish `hup : ∑ a, y a ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K'`. Rewrite using `[hYsum]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `hlow` using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow`. Establish `hδM : (δ * N / 2) ^ 2 ≤ (δ * N - M) ^ 2`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e1 : (δ * N / 2) ^ 2 = (δ * N) ^ 2 / 4` using `by ring`. Establish `h5 : (δ * N) ^ 2 / 16 ≤ n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K' = A + Bc * N`. Rewrite using `[hA, hBc, hXdef]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h5` using `[e2]`. Establish `h6 : 16 * (A + Bc) < δ ^ 2 * N` using `by linarith [pow_pos hδ 2]`. Establish `h7 : 16 * (A + Bc) * N < δ ^ 2 * N * N` using `mul_lt_mul_of_pos_right h6 (by linarith)`. Establish `e3 : (δ * N) ^ 2 = δ ^ 2 * N * N` using `by ring`.

Establish `h8 : A ≤ A * N` using `le_mul_of_one_le_right hA0 hN1`. Rewrite `h5` using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem farNum : FarNum := by
  intro n C δ K hδ
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = |C| := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = |K| := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = n * Lc n := ⟨_, rfl⟩
  have hC0 : 0 ≤ C' := hC' ▸ abs_nonneg _
  have hK0 : 0 ≤ K' := hK' ▸ abs_nonneg _
  have hM0 : 0 ≤ M := by rw [hMdef, Lc]; positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * n * M ^ 2 + 2 * n * K' * (M + K') + 2 * (n : ℝ) ^ 2 * (M + K') + (n : ℝ) ^ 3
      + n * C' ^ 2 + K' := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = 2 * n * K' * C' + 2 * (n : ℝ) ^ 2 * C' := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ Bc := by rw [hBc]; positivity
  refine ⟨1 + 2 * M / δ + 16 * (A + Bc) / δ ^ 2, ?_⟩
  intro χ x r lev σ N _ _ hr hsp hblk hineq hsep hbd hN a b hab
  by_contra hne
  have hq1 : 0 ≤ 2 * M / δ := by positivity
  have hq2 : 0 ≤ 16 * (A + Bc) / δ ^ 2 := by positivity
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hδN : 2 * M ≤ δ * N := by
    have : 2 * M / δ ≤ N := by linarith
    rw [div_le_iff₀ hδ] at this
    linarith
  have hδ2 : 16 * (A + Bc) + δ ^ 2 ≤ δ ^ 2 * N := by
    have : 16 * (A + Bc) / δ ^ 2 ≤ N - 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith

  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun a => (χ (σ a)).re := ⟨_, rfl⟩
  have hyb : ∀ a, |y a| ≤ C' * N := by
    intro a
    rw [hy]
    refine (hbd (σ a)).1.trans ?_
    rw [hC']
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hN0
  have hblk' : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K' := by
    intro c
    have h1 := Complex.abs_re_le_norm (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ))
    have h2 : (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ)).re
        = ∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a) := by
      rw [hy, Finset.sum_sub_distrib]
      simp [Complex.re_sum]
    rw [h2] at h1
    exact h1.trans ((hblk c).trans (hK' ▸ le_abs_self K))
  have hspM : ∀ a b, lev a = lev b → |x a - x b| ≤ M := fun a b h => hMdef ▸ hsp a b h

  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = C' * N + M + K' := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hX : ∀ a, |x a| ≤ X := by
    intro a
    rw [hXdef]
    refine x_bound (univ.filter fun c => lev c = lev a) x y a (by simp) _ _ _ hK0
      (fun c _ => hyb c) (fun c hc => hspM a c (Finset.mem_filter.mp hc).2.symm) (hblk' _)

  have hlow := total_bound x y lev M X K' hX0 hK0 hX hspM hblk'
  have hD : (δ * N - M) ^ 2 / 2 ≤ ∑ c, (y c - x c) ^ 2 := by
    refine two_bound (fun c => y c - x c) a b hne _ (by linarith) ?_
    have h1 : δ * N ≤ |y a - y b| := by
      rw [hy]
      exact hsep (σ a) (σ b) (fun h => hne (σ.injective h))
    have h2 := hspM a b hab
    have h3 : |y a - y b| ≤ |(y a - x a) - (y b - x b)| + |x a - x b| := by
      have : y a - y b = ((y a - x a) - (y b - x b)) + (x a - x b) := by ring
      rw [this]
      exact abs_add_le _ _
    show δ * N - M ≤ |(y a - x a) - (y b - x b)|
    linarith

  have hYsum : ∑ a, y a ^ 2 = ∑ a, (χ a).re ^ 2 := by
    rw [hy]
    exact Equiv.sum_comp σ (fun a => (χ a).re ^ 2)
  have hIm : ∑ a, (χ a).im ^ 2 ≤ n * C' ^ 2 := by
    calc ∑ a, (χ a).im ^ 2 ≤ ∑ _a : Fin n, C' ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← sq_abs (χ a).im]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hbd a).2.trans (hC' ▸ le_abs_self C)) 2
      _ = n * C' ^ 2 := by simp
  have hxr : ∑ a, (x a - r a) ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) := by
    have : ∀ a ∈ (univ : Finset (Fin n)), (x a - r a) ^ 2 ≤ x a ^ 2 + (2 * X * n + (n : ℝ) ^ 2) := by
      intro a _
      have h1 : |x a * r a| ≤ X * n := by
        rw [abs_mul]
        exact mul_le_mul (hX a) (hr a) (abs_nonneg _) hX0
      have h2 : r a ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs (r a)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hr a) 2
      nlinarith [(abs_le.mp h1).1]
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_refl _
  have hKK : K ≤ K' := hK' ▸ le_abs_self K
  rw [Finset.sum_sub_distrib] at hineq
  have hup : ∑ a, y a ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K' := by
    rw [hYsum]
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at hlow
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  have hδM : (δ * N / 2) ^ 2 ≤ (δ * N - M) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have e1 : (δ * N / 2) ^ 2 = (δ * N) ^ 2 / 4 := by ring
  have h5 : (δ * N) ^ 2 / 16 ≤ n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2)
      + n * C' ^ 2 + K' := by
    linarith
  have e2 : n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K'
      = A + Bc * N := by
    rw [hA, hBc, hXdef]
    ring
  rw [e2] at h5
  have h6 : 16 * (A + Bc) < δ ^ 2 * N := by linarith [pow_pos hδ 2]
  have h7 : 16 * (A + Bc) * N < δ ^ 2 * N * N := mul_lt_mul_of_pos_right h6 (by linarith)
  have e3 : (δ * N) ^ 2 = δ ^ 2 * N * N := by ring
  have h8 : A ≤ A * N := le_mul_of_one_le_right hA0 hN1
  rw [e3] at h5
  linarith

end GlobalTheory.CompanionTheory.RgExhFar
