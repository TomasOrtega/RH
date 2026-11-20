import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIntervalIntegralLeOfSpaced
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvOfIsPrimitive
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.MultSieve

/- English proof (translation)
Establish `h` using `GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)`. Rewrite `h` using `[← star_gaussSum_eq]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_pow, ← Complex.mul_conj']`. Simplify using `using h`.
-/
theorem norm_sq_gaussSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ^ 2 = q := by
  have h := GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  rw [← star_gaussSum_eq] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simpa using h

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Establish `key : ∀ χ : DirichletCharacter ℂ q, ((‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 : ℝ) : ℂ) = ∑ b : ZMod q, ∑ c : ZMod q, (χ⁻¹ b * χ c) * (F b * (starRingEnd ℂ) (F c))`. Introduce `χ`. Rewrite using `[Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Establish `: (starRingEnd ℂ) (χ⁻¹ c) = χ c`. Use `MulChar.star_apply' χ⁻¹ c` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Rewrite using `[map_mul, this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Complex.ofReal_sum]`. Repeatedly rewrite using `[key]`. Rewrite using `[Finset.sum_comm, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Repeatedly rewrite using `[← Finset.sum_mul]`. Distinguish the cases in `hb : IsUnit b`. Establish `h1 : ∀ c : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c = if b = c then (q.totient : ℂ) else 0`. Introduce `c`. Rewrite using `[← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]`.

Use `Finset.sum_congr rfl fun χ _ => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `hb`. Rewrite using `[MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]`. Simplify using `[h1, hb, Complex.mul_conj']`. Simplify using `[hb, MulChar.map_nonunit _ hb]`.
-/
theorem sum_norm_sq_char {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2
      = q.totient * ∑ b : ZMod q, if IsUnit b then ‖F b‖ ^ 2 else 0 := by
  classical
  apply Complex.ofReal_injective
  have key : ∀ χ : DirichletCharacter ℂ q, ((‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 : ℝ) : ℂ)
      = ∑ b : ZMod q, ∑ c : ZMod q, (χ⁻¹ b * χ c) * (F b * (starRingEnd ℂ) (F c)) := by
    intro χ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have : (starRingEnd ℂ) (χ⁻¹ c) = χ c := by
      have := MulChar.star_apply' χ⁻¹ c
      rwa [inv_inv] at this
    rw [map_mul, this]; ring
  rw [Complex.ofReal_sum]
  simp_rw [key]
  rw [Finset.sum_comm, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  by_cases hb : IsUnit b
  · have h1 : ∀ c : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c
        = if b = c then (q.totient : ℂ) else 0 := by
      intro c
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]
      refine Finset.sum_congr rfl fun χ _ => ?_
      obtain ⟨u, rfl⟩ := hb
      rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    simp [h1, hb, Complex.mul_conj']
  · simp [hb, MulChar.map_nonunit _ hb]

/- English proof (translation)
Use `set F : ZMod q → ℂ := fun b => ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b) with hF`. Establish `hq : (0 : ℝ) < q` using `by exact_mod_cast NeZero.pos q`. Establish `h1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → q * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2`. Introduce `χ hχ`. Establish `hχ' : (χ⁻¹).IsPrimitive`.

Rewrite using `[DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]`. Conclude with `hχ`. Rewrite using `[← norm_sq_gaussSum hχ', ← mul_pow, ← norm_mul]`. Use `congr 2`. Simplify using `only [hF, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Establish `h` using `gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' (n : ZMod q)`. Rewrite `h` using `[inv_inv]`. Rewrite using `[mul_left_comm, mul_comm (gaussSum _ _), ← h, gaussSum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.mulShift_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∑ b : ZMod q, (if IsUnit b then ‖F b‖ ^ 2 else 0) = ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2`. Rewrite using `[Finset.sum_filter]`.

Use `symm`. Use `Finset.sum_nbij' (fun b => (b : ZMod q)) (fun b => b.val) (by simp) (fun b _ => by simpa using ZMod.val_lt b) (fun b hb => ZMod.val_cast_of_lt (by simpa using hb)) (by simp) ?_` and prove the remaining obligations. Introduce `b _`. Use `if_congr (ZMod.isUnit_iff_coprime b q).symm ?_ rfl` and prove the remaining obligations. Use `congr 2`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `ZMod.stdAddChar_coe (N := q) ((n * b : ℕ) : ℤ)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2]`. Establish `h3 : {χ : DirichletCharacter ℂ q | χ.IsPrimitive} = ↑(Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)` using `by simp`. Rewrite using `[h3, finsum_mem_coe_finset]`.

Use `le_of_mul_le_mul_left ?_ hq` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_congr rfl fun χ hχ => h1 χ (Finset.mem_filter.1 hχ).2]`. Use `(Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity).trans ?_` and prove the remaining obligations. Rewrite using `[sum_norm_sq_char]`. Apply the tactic sequence `refine mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q) (Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)`.
-/
theorem sum_primitive_le {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ q | χ.IsPrimitive}, ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
  classical
  set F : ZMod q → ℂ := fun b => ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b) with hF
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      q * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 := by
    intro χ hχ
    have hχ' : (χ⁻¹).IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
    rw [← norm_sq_gaussSum hχ', ← mul_pow, ← norm_mul]
    congr 2
    simp only [hF, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' (n : ZMod q)
    rw [inv_inv] at h
    rw [mul_left_comm, mul_comm (gaussSum _ _), ← h, gaussSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.mulShift_apply]; ring
  have h2 : ∑ b : ZMod q, (if IsUnit b then ‖F b‖ ^ 2 else 0)
      = ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
    rw [Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun b => (b : ZMod q)) (fun b => b.val) (by simp)
      (fun b _ => by simpa using ZMod.val_lt b)
      (fun b hb => ZMod.val_cast_of_lt (by simpa using hb)) (by simp) ?_
    intro b _
    refine if_congr (ZMod.isUnit_iff_coprime b q).symm ?_ rfl
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    have := ZMod.stdAddChar_coe (N := q) ((n * b : ℕ) : ℤ)
    push_cast at this
    rw [this]
    congr 2
    push_cast; ring
  rw [← h2]
  have h3 : {χ : DirichletCharacter ℂ q | χ.IsPrimitive}
      = ↑(Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) := by simp
  rw [h3, finsum_mem_coe_finset]
  refine le_of_mul_le_mul_left ?_ hq
  rw [Finset.mul_sum, Finset.sum_congr rfl fun χ hχ => h1 χ (Finset.mem_filter.1 hχ).2]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => by positivity).trans ?_
  rw [sum_norm_sq_char]
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q)
    (Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)

/- English proof (translation)
Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Establish `hr0 : (0 : ℝ) < r` using `by exact_mod_cast (by omega : 0 < r)`. Establish `hb1 : (b : ℝ) / q < 1` using `(div_lt_one hq0).2 (by exact_mod_cast hb)`. Establish `hc1 : (c : ℝ) / r < 1` using `(div_lt_one hr0).2 (by exact_mod_cast hc)`. Establish `hb0 : 0 ≤ (b : ℝ) / q` using `by positivity`.

Establish `hc0 : 0 ≤ (c : ℝ) / r` using `by positivity`. Establish `hk : (b : ℝ) / q - (c : ℝ) / r - k ≠ 0`. Introduce `h`. Establish `h1 : (k : ℝ) < 1` using `by linarith`. Establish `h2 : (-1 : ℝ) < k` using `by linarith`.

Establish `h1' : k < 1` using `by exact_mod_cast h1`. Establish `h2' : -1 < k` using `by exact_mod_cast h2`. Establish `: k = 0` using `by omega`. Substitute `this` using the available equality. Apply `hne` to reduce the goal to its premises.

Simplify using `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : (b : ℝ) / q - (c : ℝ) / r - k = ((b * r - c * q - k * q * r : ℤ) : ℝ) / (q * r)` using `by push_cast; field_simp`. Rewrite `hk`, the goal using `[he]`. Establish `hm : (b * r - c * q - k * q * r : ℤ) ≠ 0`.

Introduce `h`. Rewrite `hk` using `[h]`. Simplify using `at hk`. Establish `hm1 : (1 : ℝ) ≤ |((b * r - c * q - k * q * r : ℤ) : ℝ)|`. Conclude with `Int.one_le_abs hm` after adjusting the coercions.

Rewrite using `[abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * r)]`. Establish `hq' : (q : ℝ) ≤ Q` using `by exact_mod_cast hq`. Establish `hr' : (r : ℝ) ≤ Q` using `by exact_mod_cast hr`. Rewrite using `[sq]`. Use `gcongr`.
-/
theorem farey_spaced (Q q r b c : ℕ) (hq : q ≤ Q) (hr : r ≤ Q) (hb : b < q) (hc : c < r)
    (hne : (b : ℝ) / q ≠ (c : ℝ) / r) (k : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(b : ℝ) / q - (c : ℝ) / r - k| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb1 : (b : ℝ) / q < 1 := (div_lt_one hq0).2 (by exact_mod_cast hb)
  have hc1 : (c : ℝ) / r < 1 := (div_lt_one hr0).2 (by exact_mod_cast hc)
  have hb0 : 0 ≤ (b : ℝ) / q := by positivity
  have hc0 : 0 ≤ (c : ℝ) / r := by positivity
  have hk : (b : ℝ) / q - (c : ℝ) / r - k ≠ 0 := by
    intro h
    have h1 : (k : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < k := by linarith
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    have : k = 0 := by omega
    subst this
    apply hne
    simp at h
    linarith
  have he : (b : ℝ) / q - (c : ℝ) / r - k = ((b * r - c * q - k * q * r : ℤ) : ℝ) / (q * r) := by
    push_cast; field_simp
  rw [he] at hk ⊢
  have hm : (b * r - c * q - k * q * r : ℤ) ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  have hm1 : (1 : ℝ) ≤ |((b * r - c * q - k * q * r : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * r)]
  have hq' : (q : ℝ) ≤ Q := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
  rw [sq]
  gcongr

/- English proof (translation)
Use `Rat.div_int_inj (a := b) (b := q) (c := c) (d := r) (by exact_mod_cast hq) (by exact_mod_cast hr) (by simpa using hb) (by simpa using hc) (by apply Rat.cast_injective (α := ℝ); push_cast; exact h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem reduced_inj {q r b c : ℕ} (hq : 0 < q) (hr : 0 < r) (hb : Nat.Coprime b q)
    (hc : Nat.Coprime c r) (h : (b : ℝ) / q = (c : ℝ) / r) : q = r ∧ b = c := by
  have := Rat.div_int_inj (a := b) (b := q) (c := c) (d := r) (by exact_mod_cast hq)
    (by exact_mod_cast hr) (by simpa using hb) (by simpa using hc)
    (by apply Rat.cast_injective (α := ℝ); push_cast; exact h)
  omega

end GlobalTheory.MultSieve

namespace GlobalTheory

/- English proof (translation)
Introduce `Q M N a hQ`. Establish `hQ' : (1 : ℝ) ≤ Q` using `by exact_mod_cast hQ`. Use `set P := (Finset.range Q).sigma (fun q => (Finset.range (q + 1)).filter (fun b => Nat.Coprime b (q + 1))) with hP`. Use `set φ : (Σ _ : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) with hφ`. Establish `hmem : ∀ p ∈ P, p.1 < Q ∧ p.2 < p.1 + 1 ∧ Nat.Coprime p.2 (p.1 + 1)`.

Introduce `p hp`. Simplify `hp` using `only [hP, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]`. Establish `hinj : Set.InjOn φ P`. Introduce and unpack `⟨q, b⟩ hp ⟨r, c⟩ hp' h`. Take `⟨h1, h2⟩` from `MultSieve.reduced_inj (Nat.succ_pos q) (Nat.succ_pos r) (hmem _ hp).2.2 (hmem _ hp').2.2 h`.

Take `rfl : q = r` from `by omega`. Take `rfl : b = c` from `h2`. Both sides reduce to the same expression. Establish `h` using `additive_large_sieve M N a (P.image φ) (1 / (Q : ℝ) ^ 2) (by positivity) (by rw [div_le_one (by positivity)]; nlinarith) ?_`. Rewrite `h` using `[Finset.sum_image hinj, one_div_one_div, hP, Finset.sum_sigma]`.

Conclude with `(Finset.sum_le_sum fun q _ => MultSieve.sum_primitive_le _ a).trans h`. Introduce `x hx y hy hxy k`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨p', hp', rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `MultSieve.farey_spaced Q _ _ _ _ (hmem _ hp).1 (hmem _ hp').1 (hmem _ hp).2.1 (hmem _ hp').2.1 hxy k`.
-/
theorem multiplicative_large_sieve : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro Q M N a hQ
  classical
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set P := (Finset.range Q).sigma
    (fun q => (Finset.range (q + 1)).filter (fun b => Nat.Coprime b (q + 1))) with hP
  set φ : (Σ _ : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) with hφ
  have hmem : ∀ p ∈ P, p.1 < Q ∧ p.2 < p.1 + 1 ∧ Nat.Coprime p.2 (p.1 + 1) := by
    intro p hp
    simpa only [hP, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] using hp
  have hinj : Set.InjOn φ P := by
    rintro ⟨q, b⟩ hp ⟨r, c⟩ hp' h
    obtain ⟨h1, h2⟩ := MultSieve.reduced_inj (Nat.succ_pos q) (Nat.succ_pos r)
      (hmem _ hp).2.2 (hmem _ hp').2.2 h
    obtain rfl : q = r := by omega
    obtain rfl : b = c := h2
    rfl
  have h := additive_large_sieve M N a (P.image φ) (1 / (Q : ℝ) ^ 2) (by positivity)
    (by rw [div_le_one (by positivity)]; nlinarith) ?_
  · rw [Finset.sum_image hinj, one_div_one_div, hP, Finset.sum_sigma] at h
    exact (Finset.sum_le_sum fun q _ => MultSieve.sum_primitive_le _ a).trans h
  · intro x hx y hy hxy k
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hy
    exact MultSieve.farey_spaced Q _ _ _ _ (hmem _ hp).1 (hmem _ hp').1 (hmem _ hp).2.1
      (hmem _ hp').2.1 hxy k

end GlobalTheory
