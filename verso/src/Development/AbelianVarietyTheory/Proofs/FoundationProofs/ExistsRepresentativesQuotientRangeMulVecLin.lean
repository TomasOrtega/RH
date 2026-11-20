import Mathlib

open Finset Matrix

namespace GlobalTheory

section Trace

variable {A : Type*} [Fintype A] [DecidableEq A]

/- English proof (translation)
Establish `h : IsIdempotentElem (Matrix.toLin' E)`. Rewrite using `[IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]`. Conclude with `⟨_, by rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ h).trace]⟩`.
-/
theorem exists_nat_trace_of_mul_self {E : Matrix A A ℂ} (hE : E * E = E) :
    ∃ r : ℕ, E.trace = r := by
  have h : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  exact ⟨_, by rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ h).trace]⟩

/- English proof (translation)
Use `set S : Matrix A A ℂ := 1 + V + V ^ 2 + V ^ 3 with hS`. Establish `h1 : V * S = S`. Establish `: V * S = V + V ^ 2 + V ^ 3 + V ^ 4` using `by rw [hS]; noncomm_ring`. Rewrite using `[this, hV, hS]`. Normalize the expressions using the abelian group laws.

Establish `h2 : V ^ 2 * S = S` using `by rw [pow_two, mul_assoc, h1, h1]`. Establish `h3 : V ^ 3 * S = S` using `by rw [pow_succ, mul_assoc, h1, h2]`. Establish `h4 : S * S = (4 : ℂ) • S` using `by conv_lhs => rw [hS, add_mul, add_mul, add_mul, ← hS, one_mul, h1, h2, h3] module`. Take `⟨r, hr⟩` from `exists_nat_trace_of_mul_self (E := (4 : ℂ)⁻¹ • S) (by`. Rewrite using `[smul_mul_smul_comm, h4, smul_smul]`.

Use the proof step `norm_num)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr, hS]`. Simplify using `only [trace_smul, trace_add, trace_one, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nat_trace_of_pow_four {V : Matrix A A ℂ} (hV : V ^ 4 = 1) :
    ∃ r : ℕ, (Fintype.card A : ℂ) + V.trace + (V ^ 2).trace + (V ^ 3).trace = 4 * r := by
  set S : Matrix A A ℂ := 1 + V + V ^ 2 + V ^ 3 with hS
  have h1 : V * S = S := by
    have : V * S = V + V ^ 2 + V ^ 3 + V ^ 4 := by rw [hS]; noncomm_ring
    rw [this, hV, hS]; abel
  have h2 : V ^ 2 * S = S := by rw [pow_two, mul_assoc, h1, h1]
  have h3 : V ^ 3 * S = S := by rw [pow_succ, mul_assoc, h1, h2]
  have h4 : S * S = (4 : ℂ) • S := by
    conv_lhs => rw [hS, add_mul, add_mul, add_mul, ← hS, one_mul, h1, h2, h3]
    module
  obtain ⟨r, hr⟩ := exists_nat_trace_of_mul_self (E := (4 : ℂ)⁻¹ • S) (by
    rw [smul_mul_smul_comm, h4, smul_smul]; norm_num)
  refine ⟨r, ?_⟩
  rw [← hr, hS]
  simp only [trace_smul, trace_add, trace_one, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_nat_trace_of_pow_four hU`. Take `⟨t, ht⟩` from `exists_nat_trace_of_pow_four (V := Complex.I • U) (by`. Rewrite using `[smul_pow, hU, Complex.I_pow_four, one_smul])`. Simplify using `only [smul_pow, trace_smul, smul_eq_mul, h2, Complex.I_sq, Complex.I_pow_three] at hr ht`. Use `set a := U.trace`.

Use `set b := (U ^ 3).trace`. Use `set D := Fintype.card A`. Establish `hm : a + b = ((4 * r - D - 1 : ℤ) : ℂ)` using `by push_cast; linear_combination hr`. Establish `hn : Complex.I * (a - b) = ((4 * t - D + 1 : ℤ) : ℂ)` using `by push_cast; linear_combination ht`. Establish `hmn : (4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 = 4`.

Establish `: (((4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 : ℤ) : ℂ) = ((4 : ℤ) : ℂ)`. Rewrite using `[Int.cast_add, Int.cast_pow, Int.cast_pow, ← hm, ← hn, mul_pow, Complex.I_sq]`. Use `push_cast`. Take the linear combination `4 * h13`. Conclude with `this` after adjusting the coercions.

Break down `Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hodd) with h | h` into its components or cases. Establish `h0 : (4 * t - D + 1 : ℤ) = 0`. Take `⟨k, hk⟩ : ∃ k : ℤ, (4 * t - D + 1 : ℤ) = 4 * k` from `⟨t - D / 4, by omega⟩`. Rewrite `hmn`, the goal using `[hk]`. Establish `: k = 0` using `by nlinarith [sq_nonneg (4 * r - D - 1 : ℤ), sq_nonneg k, sq_nonneg (k - 1), sq_nonneg (k+1), Int.one_le_abs (z := k), sq_abs k]`.

Simplify using `[this]`. Rewrite `hn` using `[h0]`. Establish `hab : a = b` using `by simpa [sub_eq_zero] using hn`. Rewrite using `[ZMod.χ₄_nat_one_mod_four h, pow_two]`. Simplify `h13` using `[← hab]`.

Establish `h0 : (4 * r - D - 1 : ℤ) = 0`. Take `⟨k, hk⟩ : ∃ k : ℤ, (4 * r - D - 1 : ℤ) = 4 * k` from `⟨r - D / 4 - 1, by omega⟩`. Rewrite `hmn`, the goal using `[hk]`. Establish `: k = 0` using `by nlinarith [sq_nonneg (4 * t - D + 1 : ℤ), sq_nonneg k]`. Simplify using `[this]`.

Rewrite `hm` using `[h0]`. Rewrite using `[ZMod.χ₄_nat_three_mod_four h]`. Move the coercions through the operations in `at hm ⊢`. Take the linear combination `a * hm - h13`.
-/
theorem trace_sq_of_pow_four {U : Matrix A A ℂ} (hU : U ^ 4 = 1) (h2 : (U ^ 2).trace = 1)
    (h13 : U.trace * (U ^ 3).trace = 1) (hodd : Odd (Fintype.card A)) :
    U.trace ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) := by
  obtain ⟨r, hr⟩ := exists_nat_trace_of_pow_four hU
  obtain ⟨t, ht⟩ := exists_nat_trace_of_pow_four (V := Complex.I • U) (by
    rw [smul_pow, hU, Complex.I_pow_four, one_smul])
  simp only [smul_pow, trace_smul, smul_eq_mul, h2, Complex.I_sq, Complex.I_pow_three] at hr ht
  set a := U.trace
  set b := (U ^ 3).trace
  set D := Fintype.card A
  have hm : a + b = ((4 * r - D - 1 : ℤ) : ℂ) := by push_cast; linear_combination hr
  have hn : Complex.I * (a - b) = ((4 * t - D + 1 : ℤ) : ℂ) := by push_cast; linear_combination ht
  have hmn : (4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 = 4 := by
    have : (((4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 : ℤ) : ℂ) = ((4 : ℤ) : ℂ) := by
      rw [Int.cast_add, Int.cast_pow, Int.cast_pow, ← hm, ← hn, mul_pow, Complex.I_sq]
      push_cast
      linear_combination 4 * h13
    exact_mod_cast this
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hodd) with h | h
  · have h0 : (4 * t - D + 1 : ℤ) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (4 * t - D + 1 : ℤ) = 4 * k := ⟨t - D / 4, by omega⟩
      rw [hk] at hmn ⊢
      have : k = 0 := by nlinarith [sq_nonneg (4 * r - D - 1 : ℤ), sq_nonneg k, sq_nonneg (k - 1), sq_nonneg (k+1), Int.one_le_abs (z := k), sq_abs k]
      simp [this]
    rw [h0] at hn
    have hab : a = b := by simpa [sub_eq_zero] using hn
    rw [ZMod.χ₄_nat_one_mod_four h, pow_two]
    simpa [← hab] using h13
  · have h0 : (4 * r - D - 1 : ℤ) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (4 * r - D - 1 : ℤ) = 4 * k := ⟨r - D / 4 - 1, by omega⟩
      rw [hk] at hmn ⊢
      have : k = 0 := by nlinarith [sq_nonneg (4 * t - D + 1 : ℤ), sq_nonneg k]
      simp [this]
    rw [h0] at hm
    rw [ZMod.χ₄_nat_three_mod_four h]
    push_cast at hm ⊢
    linear_combination a * hm - h13

end Trace

section Bicharacter

variable {A : Type*} [AddCommGroup A] [Fintype A]

/- English proof (translation)
Take `⟨k, hk⟩` from `hodd`. Establish `h` using `card_nsmul_eq_zero (x := x)`. Rewrite `h` using `[hk, add_nsmul, mul_comm, mul_nsmul', two_nsmul, hx, nsmul_zero, zero_add, one_nsmul]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_add_self_eq_zero_of_odd_card (hodd : Odd (Fintype.card A)) {x : A}
    (hx : x + x = 0) : x = 0 := by
  obtain ⟨k, hk⟩ := hodd
  have h := card_nsmul_eq_zero (x := x)
  rwa [hk, add_nsmul, mul_comm, mul_nsmul', two_nsmul, hx, nsmul_zero, zero_add, one_nsmul] at h

/- English proof (translation)
Establish `hsum : ∀ x, ∑ y, B x y = if x = 0 then (Fintype.card A : ℂ) else 0`. Introduce `x`. Rewrite using `[AddChar.sum_eq_ite]`. Use `if_congr ⟨hnd x, ?_⟩ rfl rfl` and prove the remaining obligations. Introduce and unpack `rfl`.

Use extensionality with `y`. Rewrite using `[hsymm]`. Simplify using the standard rewrite rules. Establish `hD : (Fintype.card A : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Take `⟨s, hs⟩` from `IsAlgClosed.exists_pow_nat_eq (Fintype.card A : ℂ) two_pos`.

Establish `hs0 : s ≠ 0` using `by rintro rfl; exact hD (by simpa using hs.symm)`. Set `F : Matrix A A ℂ` to `Matrix.of fun x y => B x y`. Set `P : Matrix A A ℂ` to `Matrix.of fun x y => if x + y = 0 then 1 else 0`. Establish `hFF : F * F = (Fintype.card A : ℂ) • P`. Use extensionality with `x z`.

Simplify using `only [F, P, mul_apply, of_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[← hsum]`. Use `sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hsymm x y, hsymm (x + z) y, AddChar.map_add_eq_mul]`. Establish `hPP : P * P = 1`.

Use extensionality with `x z`. Simplify using `only [P, mul_apply, of_apply, one_apply, add_eq_zero_iff_neg_eq, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true, neg_neg]`. Establish `hP : P.trace = 1`. Establish `: ∀ x : A, x + x = 0 ↔ x = 0` using `fun x => ⟨eq_zero_of_add_self_eq_zero_of_odd_card hodd, fun h => by simp [h]⟩`. Simplify using `[P, trace, this]`.

Establish `hPF : (P * F).trace = ∑ x, B (-x) x`. Simplify using `[P, F, trace, mul_apply, add_eq_zero_iff_neg_eq]`. Establish `hF : F.trace = ∑ x, B x x` using `by simp [F, trace]`. Establish `hprod : F.trace * (P * F).trace = Fintype.card A`. Rewrite using `[hF, hPF, sum_mul_sum, ← Fintype.sum_prod_type']`.

Set `φ : A × A → A × A` to `fun p => (p.1 + p.2, p.1 - p.2)`. Establish `hφ : Function.Bijective φ`. Use `Finite.injective_iff_bijective.1 fun p q h => ?_` and prove the remaining obligations. Establish `h1 : p.1 + p.2 = q.1 + q.2` using `congrArg Prod.fst h`. Establish `h2 : p.1 - p.2 = q.1 - q.2` using `congrArg Prod.snd h`.

Establish `h3 : p.1 - q.1 = 0` using `eq_zero_of_add_self_eq_zero_of_odd_card hodd (by`. Establish `: p.1 - q.1 + (p.1 - q.1) = (p.1 + p.2 - (q.1 + q.2)) + (p.1 - p.2 - (q.1 - q.2))` using `by abel`. Rewrite using `[this, h1, h2]`. Use the proof step `simp)`. Establish `h4 : p.1 = q.1` using `sub_eq_zero.1 h3`.

Conclude with `Prod.ext h4 (by rwa [h4, add_right_inj] at h1)`. Rewrite using `[Fintype.sum_bijective φ hφ _ (fun p => B p.1 p.2), Fintype.sum_prod_type]`. Simplify using `[hsum]`. Introduce and unpack `⟨x, y⟩`. Simplify using `only [φ]`.

Rewrite using `[hsymm (x + y), AddChar.map_add_eq_mul, hsymm (x - y) x, hsymm (x - y) y, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hsymm y x, hsymm (-y) y]`. Establish `: B x (-y) * B x y = 1` using `by rw [← AddChar.map_add_eq_mul]; simp`. Take the linear combination `(-(B x x * B y (-y))) * this`. Establish `hU2 : (s⁻¹ • F) ^ 2 = P`. Rewrite using `[smul_pow, pow_two F, hFF, smul_smul, ← hs, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul]`.

Establish `key` using `trace_sq_of_pow_four (U := s⁻¹ • F) (by rw [show 4 = 2 + 2 from rfl, pow_add, hU2, hPP]) (by rw [hU2, hP]) (by`. Rewrite using `[pow_succ, hU2, mul_smul_comm, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, hprod, ← hs]`. Use the proof step `field_simp) hodd`. Rewrite using `[← key, ← hs, trace_smul, hF, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sq_sum_bicharacter (hodd : Odd (Fintype.card A)) (B : A → AddChar A ℂ)
    (hsymm : ∀ x y, B x y = B y x) (hnd : ∀ x, B x = 0 → x = 0) :
    (∑ x, B x x) ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) := by
  classical
  have hsum : ∀ x, ∑ y, B x y = if x = 0 then (Fintype.card A : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_eq_ite]
    refine if_congr ⟨hnd x, ?_⟩ rfl rfl
    rintro rfl
    ext y
    rw [hsymm]; simp
  have hD : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (Fintype.card A : ℂ) two_pos
  have hs0 : s ≠ 0 := by rintro rfl; exact hD (by simpa using hs.symm)
  let F : Matrix A A ℂ := Matrix.of fun x y => B x y
  let P : Matrix A A ℂ := Matrix.of fun x y => if x + y = 0 then 1 else 0
  have hFF : F * F = (Fintype.card A : ℂ) • P := by
    ext x z
    simp only [F, P, mul_apply, of_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← hsum]
    refine sum_congr rfl fun y _ => ?_
    rw [hsymm x y, hsymm (x + z) y, AddChar.map_add_eq_mul]
  have hPP : P * P = 1 := by
    ext x z
    simp only [P, mul_apply, of_apply, one_apply, add_eq_zero_iff_neg_eq, ite_mul, one_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true, neg_neg]
  have hP : P.trace = 1 := by
    have : ∀ x : A, x + x = 0 ↔ x = 0 := fun x =>
      ⟨eq_zero_of_add_self_eq_zero_of_odd_card hodd, fun h => by simp [h]⟩
    simp [P, trace, this]
  have hPF : (P * F).trace = ∑ x, B (-x) x := by
    simp [P, F, trace, mul_apply, add_eq_zero_iff_neg_eq]
  have hF : F.trace = ∑ x, B x x := by simp [F, trace]
  have hprod : F.trace * (P * F).trace = Fintype.card A := by
    rw [hF, hPF, sum_mul_sum, ← Fintype.sum_prod_type']
    let φ : A × A → A × A := fun p => (p.1 + p.2, p.1 - p.2)
    have hφ : Function.Bijective φ := by
      refine Finite.injective_iff_bijective.1 fun p q h => ?_
      have h1 : p.1 + p.2 = q.1 + q.2 := congrArg Prod.fst h
      have h2 : p.1 - p.2 = q.1 - q.2 := congrArg Prod.snd h
      have h3 : p.1 - q.1 = 0 := eq_zero_of_add_self_eq_zero_of_odd_card hodd (by
        have : p.1 - q.1 + (p.1 - q.1) =
            (p.1 + p.2 - (q.1 + q.2)) + (p.1 - p.2 - (q.1 - q.2)) := by abel
        rw [this, h1, h2]; simp)
      have h4 : p.1 = q.1 := sub_eq_zero.1 h3
      exact Prod.ext h4 (by rwa [h4, add_right_inj] at h1)
    rw [Fintype.sum_bijective φ hφ _ (fun p => B p.1 p.2), Fintype.sum_prod_type]
    · simp [hsum]
    · rintro ⟨x, y⟩
      simp only [φ]
      rw [hsymm (x + y), AddChar.map_add_eq_mul, hsymm (x - y) x, hsymm (x - y) y, sub_eq_add_neg,
        AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hsymm y x, hsymm (-y) y]
      have : B x (-y) * B x y = 1 := by rw [← AddChar.map_add_eq_mul]; simp
      linear_combination (-(B x x * B y (-y))) * this
  have hU2 : (s⁻¹ • F) ^ 2 = P := by
    rw [smul_pow, pow_two F, hFF, smul_smul, ← hs, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs0),
      one_smul]
  have key := trace_sq_of_pow_four (U := s⁻¹ • F)
    (by rw [show 4 = 2 + 2 from rfl, pow_add, hU2, hPP]) (by rw [hU2, hP])
    (by
      rw [pow_succ, hU2, mul_smul_comm, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
        mul_mul_mul_comm, hprod, ← hs]
      field_simp) hodd
  rw [← key, ← hs, trace_smul, hF, smul_eq_mul]
  field_simp

end Bicharacter

section Quadratic

variable {A : Type*} [AddCommGroup A] [Fintype A]

/- English proof (translation)
Set `B : A → AddChar A ℂ` to `fun x => ψ.compAddMonoidHom (q.polarBilin (x + x)).toAddMonoidHom`. Establish `hB : ∀ x y, B x y = ψ (QuadraticMap.polar q (x + x) y)` using `fun _ _ => rfl`. Rewrite using `[← sq_sum_bicharacter hodd B]`. Use `congr 1`. Establish `hφ : Function.Bijective fun x : A => x + x`.

Use `Finite.injective_iff_bijective.1 fun x y h => sub_eq_zero.1 ?_` and prove the remaining obligations. Use `eq_zero_of_add_self_eq_zero_of_odd_card hodd ?_` and prove the remaining obligations. Establish `h' : x + x = y + y` using `h`. Rewrite using `[sub_add_sub_comm, h', sub_self]`. Use `(Fintype.sum_bijective _ hφ _ _ fun x => ?_).symm` and prove the remaining obligations.

Rewrite using `[hB, QuadraticMap.polar_add_left, QuadraticMap.polar_self, QuadraticMap.map_add_self]`. Use `congr 1`. Use `module`. Introduce `x y`. Rewrite using `[hB, hB, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, QuadraticMap.polar_comm q x y]`.

Introduce `x hx`. Use `eq_zero_of_add_self_eq_zero_of_odd_card hodd (hnd _ fun y => ?_)` and prove the remaining obligations. Rewrite using `[← hB, hx]`. Both sides reduce to the same expression.
-/
theorem sq_sum_addChar_quadraticMap {M : Type*} [AddCommGroup M] (hodd : Odd (Fintype.card A))
    (q : QuadraticMap ℤ A M) (ψ : AddChar M ℂ)
    (hnd : ∀ x, (∀ y, ψ (QuadraticMap.polar q x y) = 1) → x = 0) :
    (∑ x, ψ (q x)) ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) := by
  let B : A → AddChar A ℂ := fun x => ψ.compAddMonoidHom (q.polarBilin (x + x)).toAddMonoidHom
  have hB : ∀ x y, B x y = ψ (QuadraticMap.polar q (x + x) y) := fun _ _ => rfl
  rw [← sq_sum_bicharacter hodd B]
  · congr 1
    have hφ : Function.Bijective fun x : A => x + x := by
      refine Finite.injective_iff_bijective.1 fun x y h => sub_eq_zero.1 ?_
      refine eq_zero_of_add_self_eq_zero_of_odd_card hodd ?_
      have h' : x + x = y + y := h
      rw [sub_add_sub_comm, h', sub_self]
    refine (Fintype.sum_bijective _ hφ _ _ fun x => ?_).symm
    rw [hB, QuadraticMap.polar_add_left, QuadraticMap.polar_self, QuadraticMap.map_add_self]
    congr 1
    module
  · intro x y
    rw [hB, hB, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left,
      QuadraticMap.polar_comm q x y]
  · intro x hx
    refine eq_zero_of_add_self_eq_zero_of_odd_card hodd (hnd _ fun y => ?_)
    rw [← hB, hx]; rfl

open Complex in
/- English proof (translation)
Introduce `r` and use `by simp only [Rat.cast_add, Rat.cast_one, mul_add, mul_one, exp_add, exp_two_pi_mul_I]`.
-/
theorem periodic_exp_two_pi_rat :
    Function.Periodic (fun r : ℚ => exp (2 * Real.pi * I * r)) 1 := fun r => by
  simp only [Rat.cast_add, Rat.cast_one, mul_add, mul_one, exp_add, exp_two_pi_mul_I]

noncomputable def ratCircleChar : AddChar (AddCircle (1 : ℚ)) ℂ where
  toFun := periodic_exp_two_pi_rat.lift
  map_zero_eq_one' := by
    change Complex.exp _ = 1
    simp
  map_add_eq_mul' x y := by
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    change Complex.exp _ = Complex.exp _ * Complex.exp _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratCircleChar_coe (r : ℚ) :
    ratCircleChar (r : AddCircle (1 : ℚ)) = Complex.exp (2 * Real.pi * Complex.I * r) := rfl

/- English proof (translation)
Use `⟨fun h => ?_, fun h => by simp [h]⟩` and prove the remaining obligations. Proceed by induction on `x using QuotientAddGroup.induction_on with | H r => ?_`. Rewrite `h` using `[ratCircleChar_coe, Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `h`. Rewrite `hn` using `[mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]`.

Use `(AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, mul_one]`. Conclude with `hn.symm` after adjusting the coercions.
-/
theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  induction x using QuotientAddGroup.induction_on with | H r => ?_
  rw [ratCircleChar_coe, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero] at hn
  refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
  rw [zsmul_eq_mul, mul_one]
  exact_mod_cast hn.symm

/- English proof (translation)
The claim follows from `sq_sum_addChar_quadraticMap hodd q _ fun x hx => hnd x fun y => ratCircleChar_eq_one_iff.1 (hx y)`.
-/
theorem sq_quadraticGaussSum (hodd : Odd (Fintype.card A))
    (q : QuadraticMap ℤ A (AddCircle (1 : ℚ)))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar q x y = 0) → x = 0) :
    (∑ x, ratCircleChar (q x)) ^ 2 =
      (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) :=
  sq_sum_addChar_quadraticMap hodd q _ fun x hx =>
    hnd x fun y => ratCircleChar_eq_one_iff.1 (hx y)

end Quadratic

section Matrices

variable {n : Type*} [Fintype n]

noncomputable def halfQuadraticModOne (M : Matrix n n ℚ) :
    QuadraticMap ℤ (n → ℤ) (AddCircle (1 : ℚ)) :=
  LinearMap.BilinMap.toQuadraticMap <| LinearMap.mk₂ ℤ
    (fun x y : n → ℤ =>
      ((((fun i => (x i : ℚ)) ⬝ᵥ M *ᵥ fun i => (y i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)))
    (fun x x' y => by
      rw [← AddCircle.coe_add, ← add_div, ← add_dotProduct]
      congr 3; ext; simp)
    (fun c x y => by
      rw [← AddCircle.coe_zsmul, ← smul_div_assoc, ← smul_dotProduct]
      congr 3; ext; simp)
    (fun x y y' => by
      rw [← AddCircle.coe_add, ← add_div, ← dotProduct_add, ← mulVec_add]
      congr 4; ext; simp)
    (fun c x y => by
      rw [← AddCircle.coe_zsmul, ← smul_div_assoc, ← dotProduct_smul, ← mulVec_smul]
      congr 4; ext; simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem halfQuadraticModOne_apply (M : Matrix n n ℚ) (x : n → ℤ) :
    halfQuadraticModOne M x =
      ((((fun i => (x i : ℚ)) ⬝ᵥ M *ᵥ fun i => (x i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)) := rfl

/- English proof (translation)
Rewrite using `[halfQuadraticModOne, LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.mk₂_apply, LinearMap.mk₂_apply, ← AddCircle.coe_add, dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm, add_halves]`.
-/
theorem polar_halfQuadraticModOne {M : Matrix n n ℚ} (hM : M.IsSymm) (x y : n → ℤ) :
    QuadraticMap.polar (halfQuadraticModOne M) x y =
      (((fun i => (y i : ℚ)) ⬝ᵥ M *ᵥ (fun i => (x i : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [halfQuadraticModOne, LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.mk₂_apply,
    LinearMap.mk₂_apply, ← AddCircle.coe_add, dotProduct_mulVec, ← mulVec_transpose, hM.eq,
    dotProduct_comm, add_halves]

variable [DecidableEq n] {b d : Matrix n n ℤ}

/- English proof (translation)
Rewrite using `[← Int.cast_det]`. Simplify using `using hd`.
-/
theorem isUnit_det_map_ratCast (hd : d.det ≠ 0) : IsUnit (d.map ((↑) : ℤ → ℚ)).det := by
  rw [← Int.cast_det]; simpa using hd

/- English proof (translation)
Establish `hu` using `isUnit_det_map_ratCast hd`. Establish `hs'` using `(hs.map (Int.castRingHom ℚ)).eq`. Rewrite `hs'` using `[Matrix.map_mul, transpose_map, transpose_mul, transpose_transpose]`. Simplify using `only [Int.coe_castRingHom] at hs'`. Rewrite using `[Matrix.IsSymm, transpose_mul, transpose_nonsing_inv]`.

Use `set B := b.map ((↑) : ℤ → ℚ)`. Use `set D := d.map ((↑) : ℤ → ℚ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]`. Use `_ = B * D⁻¹ := by`.

Rewrite using `[hs', ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_transpose _ hu), Matrix.one_mul]`.
-/
theorem isSymm_mul_inv_of_isSymm (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm) :
    (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹).IsSymm := by
  have hu := isUnit_det_map_ratCast hd
  have hs' := (hs.map (Int.castRingHom ℚ)).eq
  rw [Matrix.map_mul, transpose_map, transpose_mul, transpose_transpose] at hs'
  simp only [Int.coe_castRingHom] at hs'
  rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv]
  set B := b.map ((↑) : ℤ → ℚ)
  set D := d.map ((↑) : ℤ → ℚ)
  calc Dᵀ⁻¹ * Bᵀ = Dᵀ⁻¹ * (Bᵀ * D) * D⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = B * D⁻¹ := by
        rw [hs', ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_transpose _ hu), Matrix.one_mul]

omit [DecidableEq n] in
/- English proof (translation)
Use extensionality with `i`. Simplify using `[mulVec, dotProduct]`.
-/
theorem intCast_mulVec (d : Matrix n n ℤ) (x : n → ℤ) :
    (fun i => ((d *ᵥ x) i : ℚ)) = d.map ((↑) : ℤ → ℚ) *ᵥ fun i => (x i : ℚ) := by
  ext i; simp [mulVec, dotProduct]

omit [DecidableEq n] in
/- English proof (translation)
Simplify using `[dotProduct]`.
-/
theorem intCast_dotProduct (x y : n → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℚ) = (fun i => (x i : ℚ)) ⬝ᵥ fun i => (y i : ℚ) := by
  simp [dotProduct]

/- English proof (translation)
Introduce and unpack `_ ⟨μ, rfl⟩`. Establish `hu` using `isUnit_det_map_ratCast hd`. Establish `key : (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ (fun i => ((d *ᵥ μ) i : ℚ)) = fun i => ((b *ᵥ μ) i : ℚ)`. Rewrite using `[intCast_mulVec, intCast_mulVec, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]`. Use `⟨?_, LinearMap.ext fun y => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `he μ`. Rewrite `hk` using `[← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]`. Rewrite using `[mulVecLin_apply, halfQuadraticModOne_apply, key, ← intCast_dotProduct, hk]`. Conclude with `(AddCircle.coe_eq_zero_iff _).2 ⟨k, by simp⟩`. Rewrite using `[QuadraticMap.polarBilin_apply_apply, polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), mulVecLin_apply, key, ← intCast_dotProduct]`.

Conclude with `(AddCircle.coe_eq_zero_iff _).2 ⟨_, by rw [zsmul_eq_mul, mul_one]⟩`.
-/
theorem range_le_radical_halfQuadraticModOne (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) :
    LinearMap.range d.mulVecLin ≤
      (halfQuadraticModOne (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹)).radical := by
  rintro _ ⟨μ, rfl⟩
  have hu := isUnit_det_map_ratCast hd
  have key : (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ (fun i => ((d *ᵥ μ) i : ℚ)) =
      fun i => ((b *ᵥ μ) i : ℚ) := by
    rw [intCast_mulVec, intCast_mulVec, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu,
      Matrix.mul_one]
  refine ⟨?_, LinearMap.ext fun y => ?_⟩
  · obtain ⟨k, hk⟩ := he μ
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at hk
    rw [mulVecLin_apply, halfQuadraticModOne_apply, key, ← intCast_dotProduct, hk]
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨k, by simp⟩
  · rw [QuadraticMap.polarBilin_apply_apply,
      polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), mulVecLin_apply, key,
      ← intCast_dotProduct]
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨_, by rw [zsmul_eq_mul, mul_one]⟩

noncomputable def pairQuadraticForm (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) :
    QuadraticMap ℤ ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) (AddCircle (1 : ℚ)) :=
  QuadraticMap.lift _ _ (range_le_radical_halfQuadraticModOne hd hs he)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairQuadraticForm_mk (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    pairQuadraticForm hd hs he (Submodule.Quotient.mk ν) =
      ((((fun i => (ν i : ℚ)) ⬝ᵥ (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ
        fun i => (ν i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)) := rfl

/- English proof (translation)
Establish `hinv : (d.map ((↑) : ℤ → ℂ))⁻¹ = (d.map ((↑) : ℤ → ℚ))⁻¹.map (Rat.castHom ℂ)`. Use `inv_eq_right_inv ?_` and prove the remaining obligations. Establish `: d.map ((↑) : ℤ → ℂ) = (d.map ((↑) : ℤ → ℚ)).map (Rat.castHom ℂ)` using `by ext; simp`. Rewrite using `[this, ← Matrix.map_mul, mul_nonsing_inv _ (isUnit_det_map_ratCast hd), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[pairQuadraticForm_mk, ratCircleChar_coe, hinv]`.

Use `congr 1`. Simplify using `only [dotProduct, mulVec, mul_apply, map_apply, Rat.coe_castHom]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratCircleChar_pairQuadraticForm_mk (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    ratCircleChar (pairQuadraticForm hd hs he (Submodule.Quotient.mk ν)) =
      Complex.exp (Real.pi * Complex.I *
        ((fun i => (ν i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (ν i : ℂ))) := by
  have hinv : (d.map ((↑) : ℤ → ℂ))⁻¹ = (d.map ((↑) : ℤ → ℚ))⁻¹.map (Rat.castHom ℂ) := by
    refine inv_eq_right_inv ?_
    have : d.map ((↑) : ℤ → ℂ) = (d.map ((↑) : ℤ → ℚ)).map (Rat.castHom ℂ) := by ext; simp
    rw [this, ← Matrix.map_mul, mul_nonsing_inv _ (isUnit_det_map_ratCast hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [pairQuadraticForm_mk, ratCircleChar_coe, hinv]
  congr 1
  simp only [dotProduct, mulVec, mul_apply, map_apply, Rat.coe_castHom]
  push_cast
  ring

/- English proof (translation)
Take `⟨ν, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨u, v, huv⟩` from `hc`. Establish `hu` using `isUnit_det_map_ratCast hd`. Establish `hint : ∀ i, ∃ k : ℤ, (k : ℚ) = ((b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ fun i => (ν i : ℚ)) i`. Introduce `i`.

Establish `h : QuadraticMap.polar (halfQuadraticModOne (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹)) ν (Pi.single i 1) = 0` using `hx (Submodule.Quotient.mk (Pi.single i 1))`. Rewrite `h` using `[polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), AddCircle.coe_eq_zero_iff]`. Take `⟨k, hk⟩` from `h`. Use `⟨k, ?_⟩` and prove the remaining obligations. Simplify `hk` using `[dotProduct, Pi.single_apply]`.

Use `choose w hw using hint`. Establish `huv' : u.map ((↑) : ℤ → ℚ) * b.map (↑) + v.map (↑) * d.map (↑) = 1`. Use `congrArg (Int.castRingHom ℚ).mapMatrix huv` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, map_mul, map_one]`. Then use the resulting hypothesis. Use `(Submodule.Quotient.mk_eq_zero _).2 ⟨u *ᵥ w + v *ᵥ ν, ?_⟩` and prove the remaining obligations.

Establish `h1 : (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) = (d.map ((↑) : ℤ → ℚ))⁻¹ *ᵥ fun i => (ν i : ℚ)`. Establish `: (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) = (fun i => ((u *ᵥ w) i : ℚ)) + fun i => ((v *ᵥ ν) i : ℚ)` using `by ext; simp`. Rewrite using `[this, intCast_mulVec, intCast_mulVec, funext hw, mulVec_mulVec, ← add_mulVec]`. Use `congr 1`. Use `conv_rhs => rw [← Matrix.one_mul (d.map ((↑) : ℤ → ℚ))⁻¹, ← huv', Matrix.add_mul, Matrix.mul_assoc _ (d.map _), mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.mul_assoc]`.

Establish `h2` using `intCast_mulVec d (u *ᵥ w + v *ᵥ ν)`. Rewrite `h2` using `[h1, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]`. Use extensionality with `i`. Conclude with `congrFun h2 i` after adjusting the coercions.
-/
theorem pairQuadraticForm_nondegenerate (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    (x : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)
    (hx : ∀ y, QuadraticMap.polar (pairQuadraticForm hd hs he) x y = 0) : x = 0 := by
  obtain ⟨ν, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨u, v, huv⟩ := hc
  have hu := isUnit_det_map_ratCast hd
  have hint : ∀ i, ∃ k : ℤ, (k : ℚ) = ((b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ
      fun i => (ν i : ℚ)) i := by
    intro i
    have h : QuadraticMap.polar
        (halfQuadraticModOne (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹)) ν (Pi.single i 1) = 0 :=
      hx (Submodule.Quotient.mk (Pi.single i 1))
    rw [polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), AddCircle.coe_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    simpa [dotProduct, Pi.single_apply] using hk
  choose w hw using hint
  have huv' : u.map ((↑) : ℤ → ℚ) * b.map (↑) + v.map (↑) * d.map (↑) = 1 := by
    have := congrArg (Int.castRingHom ℚ).mapMatrix huv
    rwa [map_add, map_mul, map_mul, map_one] at this
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨u *ᵥ w + v *ᵥ ν, ?_⟩
  have h1 : (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) =
      (d.map ((↑) : ℤ → ℚ))⁻¹ *ᵥ fun i => (ν i : ℚ) := by
    have : (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) =
        (fun i => ((u *ᵥ w) i : ℚ)) + fun i => ((v *ᵥ ν) i : ℚ) := by ext; simp
    rw [this, intCast_mulVec, intCast_mulVec, funext hw, mulVec_mulVec, ← add_mulVec]
    congr 1
    conv_rhs => rw [← Matrix.one_mul (d.map ((↑) : ℤ → ℚ))⁻¹, ← huv', Matrix.add_mul,
      Matrix.mul_assoc _ (d.map _), mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.mul_assoc]
  have h2 := intCast_mulVec d (u *ᵥ w + v *ᵥ ν)
  rw [h1, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec] at h2
  ext i
  exact_mod_cast congrFun h2 i

/- English proof (translation)
Establish `hinj : Function.Injective d.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]`. Conclude with `fun v hv => eq_zero_of_mulVec_eq_zero hd hv`. Rewrite using `[← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← LinearMap.det_toLin']`. Both sides reduce to the same expression.
-/
theorem natCard_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    Nat.card ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) = d.det.natAbs := by
  have hinj : Function.Injective d.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    exact fun v hv => eq_zero_of_mulVec_eq_zero hd hv
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← LinearMap.det_toLin']
  rfl

/- English proof (translation)
The claim follows from `Nat.finite_of_card_ne_zero (by rw [natCard_quotient_range_mulVecLin hd]; simpa using hd)`.
-/
theorem finite_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    Finite ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_quotient_range_mulVecLin hd]; simpa using hd)

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `D.eq_nat_or_neg`. Simplify using the standard rewrite rules. Establish `: ∀ a : ZMod 4, ZMod.χ₄ (-a) = -ZMod.χ₄ a` using `by decide`. Simplify using `[this]`.
-/
theorem chi_four_natAbs_mul (D : ℤ) :
    ZMod.χ₄ (D.natAbs : ZMod 4) * D.natAbs = ZMod.χ₄ (D : ZMod 4) * D := by
  obtain ⟨m, rfl | rfl⟩ := D.eq_nat_or_neg
  · simp
  · have : ∀ a : ZMod 4, ZMod.χ₄ (-a) = -ZMod.χ₄ a := by decide
    simp [this]

/- English proof (translation)
Establish `hd : d.det ≠ 0` using `by rintro h; simp [h] at hodd`. Establish `hcard` using `natCard_quotient_range_mulVecLin hd`. Rewrite `hcard` using `[Nat.card_eq_fintype_card]`. Rewrite using `[sq_quadraticGaussSum (by rw [hcard]; exact hodd.natAbs) _ (pairQuadraticForm_nondegenerate hd hs he hc), hcard]`. Rewrite using `[← Int.cast_natCast (R := ℂ), ← Int.cast_mul, chi_four_natAbs_mul, Int.cast_mul]`.
-/
theorem sq_sum_pairQuadraticForm (hodd : Odd d.det) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    [Fintype ((n → ℤ) ⧸ LinearMap.range d.mulVecLin)] :
    (∑ x, ratCircleChar (pairQuadraticForm (by rintro h; simp [h] at hodd) hs he x)) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by
  have hd : d.det ≠ 0 := by rintro h; simp [h] at hodd
  have hcard := natCard_quotient_range_mulVecLin hd
  rw [Nat.card_eq_fintype_card] at hcard
  rw [sq_quadraticGaussSum (by rw [hcard]; exact hodd.natAbs) _
    (pairQuadraticForm_nondegenerate hd hs he hc), hcard]
  rw [← Int.cast_natCast (R := ℂ), ← Int.cast_mul, chi_four_natAbs_mul, Int.cast_mul]

omit [DecidableEq n] in

/- English proof (translation)
Rewrite using `[even_iff_two_dvd]`. Simplify using `only [dotProduct, mulVec, mul_apply]`. Conclude with `dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_sum fun j _ => Dvd.dvd.mul_right (dvd_sum fun k _ => (hb k j).mul_left _) _) _`.
-/
theorem even_dotProduct_mulVec_of_two_dvd (hb : ∀ i j, 2 ∣ b i j) (d : Matrix n n ℤ) (μ : n → ℤ) :
    Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ) := by
  rw [even_iff_two_dvd]
  simp only [dotProduct, mulVec, mul_apply]
  exact dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_sum fun j _ => Dvd.dvd.mul_right
    (dvd_sum fun k _ => (hb k j).mul_left _) _) _

/- English proof (translation)
Use `letI := Fintype.ofBijective _ hr`. Rewrite using `[← sq_sum_pairQuadraticForm hodd hs he hc]`. Use `congr 1`. Conclude with `Fintype.sum_bijective _ hr _ _ fun k => (ratCircleChar_pairQuadraticForm_mk _ hs he _).symm`.
-/
theorem sq_sum_exp_pair (hodd : Odd d.det) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    {ι : Type*} [Fintype ι] (r : ι → n → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)) :
    (∑ k, Complex.exp (Real.pi * Complex.I *
        ((fun i => (r k i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (r k i : ℂ)))) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by
  letI := Fintype.ofBijective _ hr
  rw [← sq_sum_pairQuadraticForm hodd hs he hc]
  congr 1
  exact Fintype.sum_bijective _ hr _ _ fun k => (ratCircleChar_pairQuadraticForm_mk _ hs he _).symm

/- English proof (translation)
Rewrite `h` using `[SymplecticGroup.mem_iff', J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Take `⟨-, h1, -, h2⟩` from `h`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul] at h1 h2`. Use `⟨?_, -cᵀ, aᵀ, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.IsSymm, transpose_mul, transpose_transpose]`.

Conclude with `(add_neg_eq_zero.1 h2).symm`. Rewrite using `[← neg_inj, ← h1, Matrix.neg_mul, neg_add, neg_neg]`.
-/
theorem symm_coprime_of_mem_symplecticGroup {a c : Matrix n n ℤ}
    (h : fromBlocks a b c d ∈ symplecticGroup n ℤ) :
    (dᵀ * b).IsSymm ∧ ∃ u v : Matrix n n ℤ, u * b + v * d = 1 := by
  rw [SymplecticGroup.mem_iff', J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  obtain ⟨-, h1, -, h2⟩ := h
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2
  refine ⟨?_, -cᵀ, aᵀ, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_transpose]
    exact (add_neg_eq_zero.1 h2).symm
  · rw [← neg_inj, ← h1, Matrix.neg_mul, neg_add, neg_neg]

/- English proof (translation)
Use `haveI := finite_quotient_range_mulVecLin hd`. Set `e` to `(Finite.equivFinOfCardEq (natCard_quotient_range_mulVecLin hd)).symm`. Use `⟨fun k => (e k).out, ?_⟩` and prove the remaining obligations. Use `e.bijective using 2` and compare the differences between its conclusion and the goal. Conclude with `Submodule.Quotient.mk_out _`.
-/
theorem exists_representatives_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    ∃ r : Fin d.det.natAbs → n → ℤ, Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin) := by
  haveI := finite_quotient_range_mulVecLin hd
  let e := (Finite.equivFinOfCardEq (natCard_quotient_range_mulVecLin hd)).symm
  refine ⟨fun k => (e k).out, ?_⟩
  convert e.bijective using 2
  exact Submodule.Quotient.mk_out _

end Matrices

end GlobalTheory
