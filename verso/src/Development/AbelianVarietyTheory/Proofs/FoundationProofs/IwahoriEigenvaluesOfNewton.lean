import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.PremisesModel

noncomputable section

open Polynomial

namespace GlobalTheory.IwahoriEigen

/- English proof (translation)
Set `c : ℕ → R` to `fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f.derivative.eval b)`. Establish `hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f.derivative.eval (c n))` using `fun n => rfl`. Establish `hc_mod : ∀ n, c n ≡ a₀ [SMOD I]`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => rfl`. Consider the case `succ n ih`. Rewrite using `[hc, sub_eq_add_neg, ← add_zero a₀]`. Use `ih.add ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, Ideal.neg_mem_iff]`.

Use `I.mul_mem_right _ ?_` and prove the remaining obligations. Rewrite `h₁`, the goal using `[← SModEq.zero]`. Conclude with `(ih.eval f).trans h₁`. Establish `hf'c : ∀ n, IsUnit (f.derivative.eval (c n))`. Introduce `n`.

Use `isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)` as an intermediate fact. Apply `IsUnit.of_map (Ideal.Quotient.mk I)` to reduce the goal to its premises. Use `convert! h₂ using 1`. Conclude with `SModEq.def.mp ((hc_mod n).eval _)`. Establish `hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁`. Consider the case `succ n ih`. Take `⟨k, hk⟩` from `exists_mul_sq_add_linear_part_eq_eval_add f (c n) (-(f.eval (c n) * Ring.inverse (f.derivative.eval (c n))))`.

Establish `hu` using `Ring.mul_inverse_cancel _ (hf'c n)`. Establish `e : f.eval (c (n + 1)) = k * (Ring.inverse (f.derivative.eval (c n))) ^ 2 * (f.eval (c n)) ^ 2`. Rewrite using `[hc, sub_eq_add_neg, ← hk]`. Take the linear combination `(-f.eval (c n)) * hu`. Rewrite using `[e]`.

Use `Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (show n + 1 + 1 ≤ (n + 1) * 2 by omega) ?_)` and prove the remaining obligations. Rewrite using `[pow_mul]`. Conclude with `Ideal.pow_mem_pow ih _`. Establish `aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)]`. Introduce `m n hmn`.

Rewrite using `[← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Use `clear hmn`. Proceed by induction on `k with`. Consider the case `zero => rw [add_zero]`.

Consider the case `succ k ih`. Rewrite using `[← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]`. Use `ih.add ?_` and prove the remaining obligations. Use `symm`. Rewrite using `[SModEq.zero, Ideal.neg_mem_iff]`.

Use `Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))` and prove the remaining obligations. Rewrite using `[add_assoc]`. Conclude with `le_self_add`. Take `⟨a, ha⟩` from `IsPrecomplete.prec' c (aux _ _)`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations.

It suffices to establish `∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this`. Introduce `n`. Specialize `ha n`. Rewrite `ha`, the goal using `[← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]`. Use `(ha.symm.eval f).trans ?_` and prove the remaining obligations.

Rewrite using `[SModEq.zero]`. Conclude with `Ideal.pow_le_pow_right le_self_add (hfcI _)`. Specialize `ha (0 + 1)`. Rewrite `ha` using `[zero_add, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]`. Rewrite using `[← SModEq.sub_mem]`.

Conclude with `ha.symm.trans (hc_mod 1)`.
-/
theorem hensel_of_complete {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b =>
    b - f.eval b * Ring.inverse (f.derivative.eval b)
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f.derivative.eval (c n)) :=
    fun n => rfl
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f.derivative.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih =>
      obtain ⟨k, hk⟩ := exists_mul_sq_add_linear_part_eq_eval_add f (c n)
        (-(f.eval (c n) * Ring.inverse (f.derivative.eval (c n))))
      have hu := Ring.mul_inverse_cancel _ (hf'c n)
      have e : f.eval (c (n + 1)) =
          k * (Ring.inverse (f.derivative.eval (c n))) ^ 2 * (f.eval (c n)) ^ 2 := by
        rw [hc, sub_eq_add_neg, ← hk]
        linear_combination (-f.eval (c n)) * hu
      rw [e]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (show n + 1 + 1 ≤ (n + 1) * 2 by omega) ?_)
      rw [pow_mul]
      exact Ideal.pow_mem_pow ih _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [zero_add, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha
    rw [← SModEq.sub_mem]
    exact ha.symm.trans (hc_mod 1)

/- English proof (translation)
Establish `hd : C (ϖ ^ (e + 1)) ∣ P.comp (C (ϖ ^ b) * X) - (monomial i (u * ϖ ^ e) + monomial (i + 1) (w * ϖ ^ e))`. Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `j`. Rewrite using `[coeff_sub, comp_C_mul_X_coeff, coeff_add, coeff_monomial, coeff_monomial]`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `[h0]`. Distinguish the cases in `hj' : j = i + 1`. Substitute `hj'` using the available equality. Simplify using `[h1]`.

Rewrite using `[if_neg (Ne.symm hj), if_neg (Ne.symm hj')]`. Simplify using `using h2 j hj hj'`. Take `⟨R, hR⟩` from `hd`. Use `set y₀ : Oˣ := -(u * w⁻¹) with hy₀`. Establish `hy : (u : O) + w * y₀ = 0`.

Establish `: (w : O) * (w⁻¹ : Oˣ) = 1` using `w.mul_inv`. Rewrite using `[hy₀]`. Use `push_cast`. Take the linear combination `(-(u : O)) * this`. Establish `hm : ∀ z : O, ϖ * z ∈ Ideal.span {ϖ}` using `fun z => Ideal.mem_span_singleton.2 (dvd_mul_right _ _)`.

Take `⟨y, hy1, hy2⟩` from `hensel_of_complete (Ideal.span {ϖ}) (X ^ i * (C (u : O) + C (w : O) * X) + C ϖ * R) (y₀ : O) (by simpa [hy] using hm _) (by`. Establish `: eval (y₀ : O) (derivative (X ^ i * (C (u : O) + C (w : O) * X) + C ϖ * R)) = (y₀ : O) ^ i * w + ϖ * eval (y₀ : O) (derivative R)`. Simplify using `[derivative_mul, hy, mul_comm (w : O) ((y₀ : O) ^ i)]`. Rewrite using `[this, map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hm _), add_zero]`. Conclude with `((y₀.isUnit.pow i).mul w.isUnit).map _)`.

Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `h3 : y ∈ IsLocalRing.maximalIdeal O` using `hn`. Establish `h4 : y - y₀ ∈ IsLocalRing.maximalIdeal O` using `(Ideal.span_singleton_le_iff_mem _).2 hϖ hy2`. Establish `h5` using `sub_mem h3 h4`.

Rewrite `h5` using `[sub_sub_cancel]`. Conclude with `h5 y₀.isUnit`. Establish `h3` using `congrArg (eval y) hR`. Establish `h4 : y ^ i * (u + w * y) + ϖ * eval y R = 0` using `by simpa using hy1`. Simplify using `only [eval_sub, eval_comp, eval_mul, eval_C, eval_X, eval_add, eval_monomial] at h3`.

Rewrite using `[IsRoot.def]`. Take the linear combination `h3 + ϖ ^ e * h4`.
-/
theorem exists_root_of_side {O : Type*} [CommRing O] [IsLocalRing O] (ϖ : O)
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (Ideal.span {ϖ}) O]
    (P : O[X]) (i b e : ℕ) (u w : Oˣ)
    (h0 : P.coeff i * (ϖ ^ b) ^ i = u * ϖ ^ e)
    (h1 : P.coeff (i + 1) * (ϖ ^ b) ^ (i + 1) = w * ϖ ^ e)
    (h2 : ∀ j, j ≠ i → j ≠ i + 1 → ϖ ^ (e + 1) ∣ P.coeff j * (ϖ ^ b) ^ j) :
    ∃ y : O, IsUnit y ∧ P.IsRoot (ϖ ^ b * y) := by
  have hd : C (ϖ ^ (e + 1)) ∣ P.comp (C (ϖ ^ b) * X) -
      (monomial i (u * ϖ ^ e) + monomial (i + 1) (w * ϖ ^ e)) := by
    rw [C_dvd_iff_dvd_coeff]
    intro j
    rw [coeff_sub, comp_C_mul_X_coeff, coeff_add, coeff_monomial, coeff_monomial]
    by_cases hj : j = i
    · subst hj
      simp [h0]
    by_cases hj' : j = i + 1
    · subst hj'
      simp [h1]
    rw [if_neg (Ne.symm hj), if_neg (Ne.symm hj')]
    simpa using h2 j hj hj'
  obtain ⟨R, hR⟩ := hd
  set y₀ : Oˣ := -(u * w⁻¹) with hy₀
  have hy : (u : O) + w * y₀ = 0 := by
    have : (w : O) * (w⁻¹ : Oˣ) = 1 := w.mul_inv
    rw [hy₀]
    push_cast
    linear_combination (-(u : O)) * this
  have hm : ∀ z : O, ϖ * z ∈ Ideal.span {ϖ} := fun z =>
    Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  obtain ⟨y, hy1, hy2⟩ := hensel_of_complete (Ideal.span {ϖ})
    (X ^ i * (C (u : O) + C (w : O) * X) + C ϖ * R) (y₀ : O) (by simpa [hy] using hm _) (by
      have : eval (y₀ : O) (derivative (X ^ i * (C (u : O) + C (w : O) * X) + C ϖ * R)) =
          (y₀ : O) ^ i * w + ϖ * eval (y₀ : O) (derivative R) := by
        simp [derivative_mul, hy, mul_comm (w : O) ((y₀ : O) ^ i)]
      rw [this, map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hm _), add_zero]
      exact ((y₀.isUnit.pow i).mul w.isUnit).map _)
  refine ⟨y, ?_, ?_⟩
  · by_contra hn
    have h3 : y ∈ IsLocalRing.maximalIdeal O := hn
    have h4 : y - y₀ ∈ IsLocalRing.maximalIdeal O :=
      (Ideal.span_singleton_le_iff_mem _).2 hϖ hy2
    have h5 := sub_mem h3 h4
    rw [sub_sub_cancel] at h5
    exact h5 y₀.isUnit
  · have h3 := congrArg (eval y) hR
    have h4 : y ^ i * (u + w * y) + ϖ * eval y R = 0 := by simpa using hy1
    simp only [eval_sub, eval_comp, eval_mul, eval_C, eval_X, eval_add, eval_monomial] at h3
    rw [IsRoot.def]
    linear_combination h3 + ϖ ^ e * h4

def tailSum {r : ℕ} (b : Fin r → ℕ) (j : ℕ) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin r => j ≤ (l : ℕ)), b l

/- English proof (translation)
Unfold `tailSum`. Establish `: Finset.univ.filter (fun l : Fin r => (j : ℕ) ≤ (l : ℕ)) = insert j (Finset.univ.filter (fun l : Fin r => (j : ℕ) + 1 ≤ (l : ℕ)))`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, Finset.sum_insert (by simp), add_comm]`.
-/
theorem tailSum_succ {r : ℕ} (b : Fin r → ℕ) (j : Fin r) :
    tailSum b j = tailSum b (j + 1) + b j := by
  unfold tailSum
  have : Finset.univ.filter (fun l : Fin r => (j : ℕ) ≤ (l : ℕ)) =
      insert j (Finset.univ.filter (fun l : Fin r => (j : ℕ) + 1 ≤ (l : ℕ))) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

/- English proof (translation)
Establish `hi` using `i.2`. Establish `A : ∀ d j : ℕ, j + d = i → tailSum b i + b i * i + d ≤ tailSum b j + b i * j`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro j h`.

Simplify using `[← h]`. Consider the case `succ d ih`. Introduce `j h`. Establish `h2` using `ih (j + 1) (by omega)`. Establish `h3` using `tailSum_succ b ⟨j, by omega⟩`.

Establish `h4 : b i < b ⟨j, by omega⟩` using `hb (by rw [Fin.lt_def]; simp only; omega)`. Simplify using `only at h3`. Rewrite `h2` using `[mul_add, mul_one]`. Use linear arithmetic over natural numbers and integers. Establish `B : ∀ d : ℕ, i + 1 + d ≤ r → tailSum b i + b i * i + d ≤ tailSum b (i + 1 + d) + b i * (i + 1 + d)`.

Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro _`. Rewrite using `[tailSum_succ b i]`. Simplify using `only [add_zero]`.

Use the polynomial consequences of the given equalities and inequalities. Consider the case `succ d ih`. Introduce `h`. Establish `h2` using `ih (by omega)`. Establish `h3` using `tailSum_succ b ⟨i + 1 + d, by omega⟩`.

Establish `h4 : b ⟨i + 1 + d, by omega⟩ < b i` using `hb (by rw [Fin.lt_def]; simp only; omega)`. Simplify using `only at h3`. Rewrite using `[← add_assoc (i + 1 : ℕ) d 1, mul_add _ _ 1, mul_one]`. Use linear arithmetic over natural numbers and integers. Break down `lt_or_gt_of_ne h0 with h | h` into its components or cases.

Use `A (i - j) j (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨d, rfl⟩ : ∃ d, j = i + 1 + d` from `⟨j - i - 1, by omega⟩`. Use `B d hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem tailSum_lt {r : ℕ} {b : Fin r → ℕ} (hb : StrictAnti b) (i : Fin r) (j : ℕ) (hj : j ≤ r)
    (h0 : j ≠ i) (h1 : j ≠ i + 1) :
    tailSum b i + b i * i + 1 ≤ tailSum b j + b i * j := by
  have hi := i.2
  have A : ∀ d j : ℕ, j + d = i → tailSum b i + b i * i + d ≤ tailSum b j + b i * j := by
    intro d
    induction d with
    | zero => intro j h; simp [← h]
    | succ d ih =>
      intro j h
      have h2 := ih (j + 1) (by omega)
      have h3 := tailSum_succ b ⟨j, by omega⟩
      have h4 : b i < b ⟨j, by omega⟩ := hb (by rw [Fin.lt_def]; simp only; omega)
      simp only at h3
      rw [mul_add, mul_one] at h2
      omega
  have B : ∀ d : ℕ, i + 1 + d ≤ r →
      tailSum b i + b i * i + d ≤ tailSum b (i + 1 + d) + b i * (i + 1 + d) := by
    intro d
    induction d with
    | zero => intro _; rw [tailSum_succ b i]; simp only [add_zero]; nlinarith
    | succ d ih =>
      intro h
      have h2 := ih (by omega)
      have h3 := tailSum_succ b ⟨i + 1 + d, by omega⟩
      have h4 : b ⟨i + 1 + d, by omega⟩ < b i := hb (by rw [Fin.lt_def]; simp only; omega)
      simp only at h3
      rw [← add_assoc (i + 1 : ℕ) d 1, mul_add _ _ 1, mul_one]
      omega
  rcases lt_or_gt_of_ne h0 with h | h
  · have := A (i - j) j (by omega)
    omega
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
    have := B d hj
    omega

/- English proof (translation)
Take `⟨u, hu⟩` from `h i i.2.le`. Take `⟨w, hw⟩` from `h (i + 1) i.2`. Use `exists_root_of_side ϖ hϖ P i (b i) (tailSum b i + b i * i) u w ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hu]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hw, tailSum_succ b i]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j h0 h1`. Distinguish the cases in `hj : j ≤ r`. Take `⟨z, hz⟩` from `h j hj`.

Rewrite using `[hz, mul_assoc, ← pow_mul, ← pow_add]`. Conclude with `(pow_dvd_pow _ (tailSum_lt hb i j hj h0 h1)).mul_left _`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem exists_root_of_coeff {O : Type*} [CommRing O] [IsLocalRing O] (ϖ : O)
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (Ideal.span {ϖ}) O]
    {r : ℕ} {b : Fin r → ℕ} (hb : StrictAnti b) (P : O[X]) (hP : P.natDegree ≤ r)
    (h : ∀ j ≤ r, ∃ u : Oˣ, P.coeff j = u * ϖ ^ tailSum b j) (i : Fin r) :
    ∃ y : O, IsUnit y ∧ P.IsRoot (ϖ ^ b i * y) := by
  obtain ⟨u, hu⟩ := h i i.2.le
  obtain ⟨w, hw⟩ := h (i + 1) i.2
  refine exists_root_of_side ϖ hϖ P i (b i) (tailSum b i + b i * i) u w ?_ ?_ ?_
  · rw [hu]; ring
  · rw [hw, tailSum_succ b i]; ring
  · intro j h0 h1
    by_cases hj : j ≤ r
    · obtain ⟨z, hz⟩ := h j hj
      rw [hz, mul_assoc, ← pow_mul, ← pow_add]
      exact (pow_dvd_pow _ (tailSum_lt hb i j hj h0 h1)).mul_left _
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

section Valued

open GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup Filter Topology WithZero

variable {F : Type} [Field F] [Valued F ℤᵐ⁰]

/- English proof (translation)
Proceed by induction on `g using WithZero.expRecOn with`. Consider the case `zero => simp`. Consider the case `exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_one_iff_le_exp (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

/- English proof (translation)
Use `(Valuation.integer.integers (Valued.v : Valuation F ℤᵐ⁰)).le_iff_dvd (x := x) (y := π ^ n)` as an intermediate fact. Rewrite `this` using `[map_pow, map_pow]`. Conclude with `this.symm`.
-/
theorem pow_dvd_iff (π x : Int F) (n : ℕ) :
    π ^ n ∣ x ↔ Valued.v (x : F) ≤ Valued.v (π : F) ^ n := by
  have := (Valuation.integer.integers (Valued.v : Valuation F ℤᵐ⁰)).le_iff_dvd (x := x) (y := π ^ n)
  rw [map_pow, map_pow] at this
  exact this.symm

/- English proof (translation)
Establish `hπ1 : Valued.v (π : F) < 1` using `(lt_one_iff_le_exp _).2 hπ.le`. Establish `hπ0 : (π : F) ≠ 0`. Introduce `h`. Rewrite `hπ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`.

Use `{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Ideal.mul_top, SModEq.zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_dvd_iff] at hx`. Assume the negation of the conclusion as `h0`. Establish `h1 : Valued.v (x : F) ≠ 0` using `by simpa using h0`. Take `⟨n, hn⟩` from `exists_pow_lt₀ hπ1 (Units.mk0 _ h1)`.

Conclude with `hn.not_ge (hx n)`. Simplify using `only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_dvd_iff] at hf ⊢`. Set `g : ℕ → F` to `fun n => (f n : F)`. Establish `hc : Cauchy (map g atTop)`. Rewrite using `[Valued.cauchy_iff]`.

Use `⟨map_neBot, fun γ => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `exists_pow_lt₀ hπ1 (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass (Valued.v : Valuation F ℤᵐ⁰)))) γ)`. Use `⟨g '' Set.Ici n, image_mem_map (Ici_mem_atTop n), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`. Rewrite using `[Valuation.restrict_lt_iff_lt_embedding]`.

Use `lt_of_le_of_lt ?_ hn` and prove the remaining obligations. Establish `h1` using `hf (m := n) (n := a) ha`. Establish `h2` using `hf (m := n) (n := b) hb`. Establish `e : g b - g a = ((f n - f a : Int F) : F) - ((f n - f b : Int F) : F)`. Simplify using `only [g]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Valuation.map_sub_le _ h1 h2`. Take `⟨l, hl⟩` from `CompleteSpace.complete hc`.

Establish `key : ∀ n, Valued.v (g n - l) ≤ Valued.v (π : F) ^ n`. Introduce `n`. Establish `hU : {y : F | (Valued.v : Valuation F ℤᵐ⁰).restrict (y - l) < (Valued.v : Valuation F ℤᵐ⁰).restrict ((π : F) ^ n)} ∈ 𝓝 l`. Rewrite using `[Valued.mem_nhds]`. Conclude with `⟨Units.mk0 ((Valued.v : Valuation F ℤᵐ⁰).restrict ((π : F) ^ n)) (by simp [hπ0]), subset_rfl⟩`.

Establish `hm` using `hl hU`. Rewrite `hm` using `[mem_map, mem_atTop_sets]`. Take `⟨N, hN⟩` from `hm`. Establish `h1 : (Valued.v : Valuation F ℤᵐ⁰).restrict (g (max N n) - l) < (Valued.v : Valuation F ℤᵐ⁰).restrict ((π : F) ^ n)` using `hN (max N n) (le_max_left _ _)`. Rewrite `h1` using `[Valuation.restrict_lt_iff, map_pow]`.

Establish `h2` using `hf (m := n) (n := max N n) (le_max_right _ _)`. Establish `e : g n - l = ((f n - f (max N n) : Int F) : F) + (g (max N n) - l)`. Simplify using `only [g]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Valuation.map_add_le _ h2 h1.le`. Establish `hl1 : l ∈ Int F`. Establish `e : l = g 0 - (g 0 - l)` using `by ring`. Rewrite using `[e]`.

Conclude with `sub_mem (f 0).2 (show Valued.v (g 0 - l) ≤ 1 by simpa using key 0)`. Conclude with `⟨⟨l, hl1⟩, fun n => key n⟩`.
-/
theorem isAdicComplete_span [CompleteSpace F] (π : Int F)
    (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) : IsAdicComplete (Ideal.span {π}) (Int F) := by
  have hπ1 : Valued.v (π : F) < 1 := (lt_one_iff_le_exp _).2 hπ.le
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, pow_dvd_iff] at hx
    by_contra h0
    have h1 : Valued.v (x : F) ≠ 0 := by simpa using h0
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (Units.mk0 _ h1)
    exact hn.not_ge (hx n)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, pow_dvd_iff] at hf ⊢
  let g : ℕ → F := fun n => (f n : F)
  have hc : Cauchy (map g atTop) := by
    rw [Valued.cauchy_iff]
    refine ⟨map_neBot, fun γ => ?_⟩
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass (Valued.v : Valuation F ℤᵐ⁰)))) γ)
    refine ⟨g '' Set.Ici n, image_mem_map (Ici_mem_atTop n), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [Valuation.restrict_lt_iff_lt_embedding]
    refine lt_of_le_of_lt ?_ hn
    have h1 := hf (m := n) (n := a) ha
    have h2 := hf (m := n) (n := b) hb
    have e : g b - g a = ((f n - f a : Int F) : F) - ((f n - f b : Int F) : F) := by
      simp only [g]; push_cast; ring
    rw [e]
    exact Valuation.map_sub_le _ h1 h2
  obtain ⟨l, hl⟩ := CompleteSpace.complete hc
  have key : ∀ n, Valued.v (g n - l) ≤ Valued.v (π : F) ^ n := by
    intro n
    have hU : {y : F | (Valued.v : Valuation F ℤᵐ⁰).restrict (y - l) <
        (Valued.v : Valuation F ℤᵐ⁰).restrict ((π : F) ^ n)} ∈ 𝓝 l := by
      rw [Valued.mem_nhds]
      exact ⟨Units.mk0 ((Valued.v : Valuation F ℤᵐ⁰).restrict ((π : F) ^ n)) (by simp [hπ0]),
        subset_rfl⟩
    have hm := hl hU
    rw [mem_map, mem_atTop_sets] at hm
    obtain ⟨N, hN⟩ := hm
    have h1 : (Valued.v : Valuation F ℤᵐ⁰).restrict (g (max N n) - l) <
        (Valued.v : Valuation F ℤᵐ⁰).restrict ((π : F) ^ n) := hN (max N n) (le_max_left _ _)
    rw [Valuation.restrict_lt_iff, map_pow] at h1
    have h2 := hf (m := n) (n := max N n) (le_max_right _ _)
    have e : g n - l = ((f n - f (max N n) : Int F) : F) + (g (max N n) - l) := by
      simp only [g]; push_cast; ring
    rw [e]
    exact Valuation.map_add_le _ h2 h1.le
  have hl1 : l ∈ Int F := by
    have e : l = g 0 - (g 0 - l) := by ring
    rw [e]
    exact sub_mem (f 0).2 (show Valued.v (g 0 - l) ≤ 1 by simpa using key 0)
  exact ⟨⟨l, hl1⟩, fun n => key n⟩

/- English proof (translation)
The claim follows from `(Valuation.integer.integers (Valued.v : Valuation F ℤᵐ⁰)).isUnit_iff_valuation_eq_one`.
-/
theorem isUnit_iff (x : Int F) : IsUnit x ↔ Valued.v (x : F) = 1 :=
  (Valuation.integer.integers (Valued.v : Valuation F ℤᵐ⁰)).isUnit_iff_valuation_eq_one

/- English proof (translation)
Establish `h1 : (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)) g).val.BlockTriangular id` using `hg`. Establish `h2` using `(Matrix.isUnit_iff_isUnit_det _).1 (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)) g).isUnit`. Rewrite `h2` using `[Matrix.det_of_upperTriangular h1]`. Establish `h3` using `isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h2`. Establish `: Nontrivial (Int F ⧸ maxId F)` using `Ideal.Quotient.nontrivial_iff.2 (by`.

Rewrite using `[Ideal.ne_top_iff_one]`. Introduce `h`. Establish `: Valued.v ((1 : Int F) : F) < (1 : ℤᵐ⁰)` using `h`. Simplify using `at this)`. Rewrite using `[isUnit_iff]`.

Assume the negation of the conclusion as `hn`. Establish `h4 : (g : Matrix (Fin r) (Fin r) (Int F)) i i ∈ maxId F` using `lt_of_le_of_ne ((g : Matrix (Fin r) (Fin r) (Int F)) i i).2 hn`. Conclude with `h3.ne_zero (Ideal.Quotient.eq_zero_iff_mem.2 h4)`.
-/
theorem isUnit_diag {r : ℕ} (g : GL (Fin r) (Int F)) (hg : g ∈ iwahoriInt F r) (i : Fin r) :
    IsUnit ((g : Matrix (Fin r) (Fin r) (Int F)) i i) := by
  have h1 : (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)) g).val.BlockTriangular
    id := hg
  have h2 := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)) g).isUnit
  rw [Matrix.det_of_upperTriangular h1] at h2
  have h3 := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h2
  have : Nontrivial (Int F ⧸ maxId F) := Ideal.Quotient.nontrivial_iff.2 (by
    rw [Ideal.ne_top_iff_one]
    intro h
    have : Valued.v ((1 : Int F) : F) < (1 : ℤᵐ⁰) := h
    simp at this)
  rw [isUnit_iff]
  by_contra hn
  have h4 : (g : Matrix (Fin r) (Fin r) (Int F)) i i ∈ maxId F :=
    lt_of_le_of_ne ((g : Matrix (Fin r) (Fin r) (Int F)) i i).2 hn
  exact h3.ne_zero (Ideal.Quotient.eq_zero_iff_mem.2 h4)

end Valued

open GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup WithZero in

/- English proof (translation)
Introduce `F _ _ _ ϖ hϖ r a ha g hg`. Take `⟨_, ⟨i₁, hi₁, rfl⟩, _, ⟨i₂, hi₂, rfl⟩, hg⟩` from `hg`. Establish `hπ1 : Valued.v ϖ < 1` using `(lt_one_iff_le_exp _).2 hϖ.le`. Establish `hπ0 : ϖ ≠ 0`. Introduce `h`.

Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Set `π : Int F` to `⟨ϖ, hπ1.le⟩`. Establish `: IsLocalRing (Int F)` using `inferInstanceAs (IsLocalRing (Valued.v : Valuation F ℤᵐ⁰).valuationSubring)`. Use `isAdicComplete_span π hϖ` as an intermediate fact.

Establish `hm : π ∈ IsLocalRing.maximalIdeal (Int F)` using `fun h => hπ1.ne ((isUnit_iff π).1 h)`. Choose the witnesses or unpack the hypotheses as in `⟨N, hNa⟩ : ∃ N : ℤ, ∀ i, N ≤ a i := by`. Take `⟨N, hN⟩` from `(Set.finite_range a).bddBelow`. Conclude with `⟨N, fun i => hN ⟨i, rfl⟩⟩`. Set `b : Fin r → ℕ` to `fun i => (a i - N).toNat`.

Establish `hab : ∀ i, a i = N + b i` using `fun i => by`. Use `hNa i` as an intermediate fact. Simplify using `only [b]`. Use linear arithmetic over natural numbers and integers. Establish `hb : StrictAnti b` using `fun i j h => by`.

Use `ha h` as an intermediate fact. Rewrite `this` using `[hab, hab]`. Use linear arithmetic over natural numbers and integers. Establish `hlow : ∀ k : GL (Fin r) (Int F), k ∈ iwahoriInt F r → ∀ i j, j < i → π ∣ (k : Matrix (Fin r) (Fin r) (Int F)) i j` using `fun k hk i j h => by`. Rewrite using `[← pow_one π, pow_dvd_iff, pow_one]`.

Conclude with `((lt_one_iff_le_exp _).1 ((mem_iwahoriInt_iff F r k).1 hk i j h)).trans hϖ.ge`. Use `set G : Matrix (Fin r) (Fin r) (Int F) := (i₁ : Matrix (Fin r) (Fin r) (Int F)) * Matrix.diagonal (fun i => π ^ b i) * i₂ with hG`. Establish `hroot` using `exists_root_of_coeff π hm hb G.charpoly (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) (fun j hj => by`. Use `hN (Int F) π hm r b hb i₁ i₂ (isUnit_diag _ hi₁) (isUnit_diag _ hi₂) (hlow _ hi₁) (hlow _ hi₂) (r - j) (Nat.sub_le _ _)` as an intermediate fact. Rewrite using `[Nat.sub_sub_self hj] at this)` and apply the resulting hypothesis.

Use `choose y hy hyr using hroot`. Establish `hgG : g = ϖ ^ N • G.map (Int F).subtype`. Establish `: diagPow ϖ a = ϖ ^ N • (Matrix.diagonal (fun i => π ^ b i)).map (Int F).subtype`. Rewrite using `[Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_smul, diagPow]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[hab, zpow_add₀ hπ0]`. Simplify using `[π]`. Rewrite using `[hg, this, hG, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]`. Both sides reduce to the same expression.

Set `x : Fin r → F` to `fun i => ϖ ^ N * ((π ^ b i * y i : Int F) : F)`. Establish `hv : ∀ i, Valued.v (x i) = WithZero.exp (-(a i))` using `fun i => by`. Establish `h1` using `(isUnit_iff _).1 (hy i)`. Simplify using `only [x, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_zpow₀, map_pow, π, hϖ, h1, mul_one]`. Rewrite using `[← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, hab]`.

Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective x` using `fun i j h => by`. Establish `h1` using `hv i`.

Rewrite `h1` using `[h, hv j, WithZero.exp_inj]`. Conclude with `ha.injective (by omega)`. Establish `hx : ∀ i, g.charpoly.IsRoot (x i)` using `fun i => by`. Establish `h1 : ((G.map (Int F).subtype).charpoly).IsRoot ((π ^ b i * y i : Int F) : F)`. Rewrite using `[Matrix.charpoly_map]`.

Conclude with `(hyr i).map`. Rewrite `h1`, the goal using `[IsRoot.def, Matrix.eval_charpoly]`. Establish `: Matrix.scalar (Fin r) (x i) - g = ϖ ^ N • (Matrix.scalar (Fin r) ((π ^ b i * y i : Int F) : F) - G.map (Int F).subtype)`. Rewrite using `[hgG, smul_sub]`. Use `congr 1`.

Rewrite using `[Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]`. Both sides reduce to the same expression. Rewrite using `[this, Matrix.det_smul, h1, mul_zero]`. Establish `hprod : g.charpoly = ∏ i, (X - C (x i))`. Use `eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _) g.charpoly_monic ?_ ?_` and prove the remaining obligations.

Conclude with `Finset.prod_dvd_of_coprime (fun i _ j _ h => pairwise_coprime_X_sub_C hinj h) fun i _ => dvd_iff_isRoot.2 (hx i)`. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card]`. Simplify using the standard rewrite rules. Conclude with `⟨⟨x, hinj, hprod, hv⟩, by rw [hprod]; exact separable_prod_X_sub_C_iff.2 hinj⟩`.
-/
theorem iwahoriEigenvalues_of_newton (hN : Formalism.PacketSums.IwahoriNewton) : IwahoriEigenvalues := by
  intro F _ _ _ ϖ hϖ r a ha g hg
  obtain ⟨_, ⟨i₁, hi₁, rfl⟩, _, ⟨i₂, hi₂, rfl⟩, hg⟩ := hg
  have hπ1 : Valued.v ϖ < 1 := (lt_one_iff_le_exp _).2 hϖ.le
  have hπ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  let π : Int F := ⟨ϖ, hπ1.le⟩
  have : IsLocalRing (Int F) :=
    inferInstanceAs (IsLocalRing (Valued.v : Valuation F ℤᵐ⁰).valuationSubring)
  have := isAdicComplete_span π hϖ
  have hm : π ∈ IsLocalRing.maximalIdeal (Int F) := fun h => hπ1.ne ((isUnit_iff π).1 h)
  obtain ⟨N, hNa⟩ : ∃ N : ℤ, ∀ i, N ≤ a i := by
    obtain ⟨N, hN⟩ := (Set.finite_range a).bddBelow
    exact ⟨N, fun i => hN ⟨i, rfl⟩⟩
  let b : Fin r → ℕ := fun i => (a i - N).toNat
  have hab : ∀ i, a i = N + b i := fun i => by
    have := hNa i
    simp only [b]
    omega
  have hb : StrictAnti b := fun i j h => by
    have := ha h
    rw [hab, hab] at this
    omega
  have hlow : ∀ k : GL (Fin r) (Int F), k ∈ iwahoriInt F r → ∀ i j, j < i →
      π ∣ (k : Matrix (Fin r) (Fin r) (Int F)) i j := fun k hk i j h => by
    rw [← pow_one π, pow_dvd_iff, pow_one]
    exact ((lt_one_iff_le_exp _).1 ((mem_iwahoriInt_iff F r k).1 hk i j h)).trans hϖ.ge
  set G : Matrix (Fin r) (Fin r) (Int F) :=
    (i₁ : Matrix (Fin r) (Fin r) (Int F)) * Matrix.diagonal (fun i => π ^ b i) * i₂ with hG
  have hroot := exists_root_of_coeff π hm hb G.charpoly
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) (fun j hj => by
      have := hN (Int F) π hm r b hb i₁ i₂ (isUnit_diag _ hi₁) (isUnit_diag _ hi₂)
        (hlow _ hi₁) (hlow _ hi₂) (r - j) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hj] at this)
  choose y hy hyr using hroot
  have hgG : g = ϖ ^ N • G.map (Int F).subtype := by
    have : diagPow ϖ a = ϖ ^ N • (Matrix.diagonal (fun i => π ^ b i)).map (Int F).subtype := by
      rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_smul, diagPow]
      congr 1
      funext i
      rw [hab, zpow_add₀ hπ0]
      simp [π]
    rw [hg, this, hG, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  let x : Fin r → F := fun i => ϖ ^ N * ((π ^ b i * y i : Int F) : F)
  have hv : ∀ i, Valued.v (x i) = WithZero.exp (-(a i)) := fun i => by
    have h1 := (isUnit_iff _).1 (hy i)
    simp only [x, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_zpow₀, map_pow, π, hϖ, h1,
      mul_one]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, hab]
    congr 1
    simp
    ring
  have hinj : Function.Injective x := fun i j h => by
    have h1 := hv i
    rw [h, hv j, WithZero.exp_inj] at h1
    exact ha.injective (by omega)
  have hx : ∀ i, g.charpoly.IsRoot (x i) := fun i => by
    have h1 : ((G.map (Int F).subtype).charpoly).IsRoot ((π ^ b i * y i : Int F) : F) := by
      rw [Matrix.charpoly_map]
      exact (hyr i).map
    rw [IsRoot.def, Matrix.eval_charpoly] at h1 ⊢
    have : Matrix.scalar (Fin r) (x i) - g =
        ϖ ^ N • (Matrix.scalar (Fin r) ((π ^ b i * y i : Int F) : F) - G.map (Int F).subtype) := by
      rw [hgG, smul_sub]
      congr 1
      rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      rfl
    rw [this, Matrix.det_smul, h1, mul_zero]
  have hprod : g.charpoly = ∏ i, (X - C (x i)) := by
    refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _) g.charpoly_monic ?_ ?_
    · exact Finset.prod_dvd_of_coprime
        (fun i _ j _ h => pairwise_coprime_X_sub_C hinj h) fun i _ => dvd_iff_isRoot.2 (hx i)
    · rw [Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card]
      simp
  exact ⟨⟨x, hinj, hprod, hv⟩, by rw [hprod]; exact separable_prod_X_sub_C_iff.2 hinj⟩

/- English proof (translation)
The claim follows from `iwahoriEigenvalues_of_newton GlobalTheory.IwahoriNewtonTest.intersectionNumber_baseChange`.
-/
theorem iwahoriEigenvalues : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues :=
  iwahoriEigenvalues_of_newton GlobalTheory.IwahoriNewtonTest.intersectionNumber_baseChange

end GlobalTheory.IwahoriEigen
