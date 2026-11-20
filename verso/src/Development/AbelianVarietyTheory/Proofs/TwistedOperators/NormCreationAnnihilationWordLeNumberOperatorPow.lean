import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `T H κ _ _ _ _ _ Φ a c M r r' hr hr' hadj hcomm hM hMa hMc l d hl hld`. Establish `hreal : ∀ (s : ℝ) (x : T), RCLike.re (inner ℂ (Φ x) (Φ ((s : ℂ) • x))) = s * ‖Φ x‖ ^ 2`. Introduce `s x`. Rewrite using `[map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Simplify using `[Complex.mul_re]`.

Use `left`. Rewrite using `[← Complex.ofReal_pow, Complex.ofReal_re]`. Establish `hca : ∀ j x, RCLike.re (inner ℂ (Φ x) (Φ (c j (a j x)))) = ‖Φ (a j x)‖ ^ 2`. Introduce `j x`. Rewrite using `[← inner_conj_symm, hadj, RCLike.conj_re, inner_self_eq_norm_sq]`.

Establish `hMx : ∀ x, M x = ∑ j, c j (a j x) + (r : ℂ) • x`. Introduce `x`. Substitute `hM` using the available equality. Simplify using `[Module.End.mul_apply]`. Establish `hQeq : ∀ x, RCLike.re (inner ℂ (Φ x) (Φ (M x))) = ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2`.

Introduce `x`. Rewrite using `[hMx, map_add, inner_add_right, map_add, ← hreal, map_sum, inner_sum, map_sum]`. Simplify using `only [hca]`. Establish `hQ : ∀ x, ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 ≤ ‖Φ x‖ * ‖Φ (M x)‖`. Introduce `x`.

Rewrite using `[← hQeq]`. Conclude with `(RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)`. Establish `hsum : ∀ x, 0 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2` using `fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)`. Establish `hrx : ∀ x, r * ‖Φ x‖ ≤ ‖Φ (M x)‖`. Introduce `x`.

Break down `(norm_nonneg (Φ x)).eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0, mul_zero]`. Conclude with `norm_nonneg _`. Use `le_of_mul_le_mul_left ?_ hpos` and prove the remaining obligations. Use polynomial arithmetic with `[hQ x, hsum x]`.

Establish `hx : ∀ x, ‖Φ x‖ ≤ ‖Φ (M x)‖`. Introduce `x`. Use polynomial arithmetic with `[hrx x, norm_nonneg (Φ x)]`. Establish `hsq : ∀ x u, 0 ≤ u → u ^ 2 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 → u ≤ ‖Φ (M x)‖`. Introduce `x u hu h`.

Establish `h1` using `hQ x`. Establish `h2` using `mul_le_mul_of_nonneg_right (hx x) (norm_nonneg (Φ (M x)))`. Establish `h3 : u ^ 2 ≤ ‖Φ (M x)‖ ^ 2` using `by nlinarith`. Conclude with `(pow_le_pow_iff_left₀ hu (norm_nonneg _) two_ne_zero).1 h3`. Establish `ha : ∀ j x, ‖Φ (a j x)‖ ≤ ‖Φ (M x)‖`.

Introduce `j x`. Use `hsq x _ (norm_nonneg _) ?_` and prove the remaining obligations. Use `Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)` as an intermediate fact. Establish `: 0 ≤ r * ‖Φ x‖ ^ 2` using `mul_nonneg (by linarith) (sq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hac : ∀ j, a j * c j = c j * a j + (r' : ℂ) • 1` using `fun j => sub_eq_iff_eq_add'.1 (hcomm j)`. Establish `hc : ∀ j x, ‖Φ (c j x)‖ ≤ ‖Φ (M x)‖`. Introduce `j x`. Use `hsq x _ (norm_nonneg _) ?_` and prove the remaining obligations. Establish `e : ‖Φ (c j x)‖ ^ 2 = ‖Φ (a j x)‖ ^ 2 + r' * ‖Φ x‖ ^ 2`.

Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), hadj, ← Module.End.mul_apply, hac, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, map_add, inner_add_right, map_add, hca, hreal]`. Use `Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)` as an intermediate fact. Establish `: r' * ‖Φ x‖ ^ 2 ≤ r * ‖Φ x‖ ^ 2` using `mul_le_mul_of_nonneg_right hr' (sq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC : ∀ s : ℝ, Commute M (M + (s : ℂ) • 1)` using `fun s => (Commute.refl M).add_right ((Commute.one_right M).smul_right _)`.

Establish `hshift : ∀ (s : ℝ), |s| ≤ r → ∀ y, ‖Φ ((M + (s : ℂ) • 1) y)‖ ≤ 2 * ‖Φ (M y)‖`. Introduce `s hs y`. Rewrite using `[LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpow : ∀ (s : ℝ), |s| ≤ r → ∀ k y, ‖Φ (((M + (s : ℂ) • 1) ^ k) y)‖ ≤ 2 ^ k * ‖Φ ((M ^ k) y)‖`.

Introduce `s hs k`. Proceed by induction on `k with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `y`. Establish `e` using `LinearMap.congr_fun ((hC s).pow_left k).eq y`. Rewrite `e` using `[Module.End.mul_apply, Module.End.mul_apply]`. Rewrite using `[pow_succ (M + (s : ℂ) • 1) k, Module.End.mul_apply, pow_succ' M k, Module.End.mul_apply]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcommx : ∀ (s : ℝ) (k : ℕ) x, M (((M + (s : ℂ) • 1) ^ k) x) = ((M + (s : ℂ) • 1) ^ k) (M x)`. Introduce `s k x`. Establish `e` using `LinearMap.congr_fun ((hC s).pow_right k).eq x`. Rewrite `e` using `[Module.End.mul_apply, Module.End.mul_apply]`. Conclude with `e`.

Establish `hMka : ∀ j (k : ℕ) x, (M ^ k) (a j x) = a j (((M + ((-r : ℝ) : ℂ) • 1) ^ k) x)`. Introduce `j k x`. Establish `hs : SemiconjBy (a j) (M + ((-r : ℝ) : ℂ) • 1) M`. Unfold `SemiconjBy`. Rewrite using `[hMa j]`.

Use `push_cast`. Rewrite using `[neg_smul, ← sub_eq_add_neg]`. Establish `e` using `LinearMap.congr_fun (hs.pow_right k).eq x`. Rewrite `e` using `[Module.End.mul_apply, Module.End.mul_apply]`. Conclude with `e.symm`.

Establish `hMkc : ∀ j (k : ℕ) x, (M ^ k) (c j x) = c j (((M + (r : ℂ) • 1) ^ k) x)`. Introduce `j k x`. Establish `hs : SemiconjBy (c j) (M + (r : ℂ) • 1) M`. Unfold `SemiconjBy`. Rewrite using `[hMc j]`.

Establish `e` using `LinearMap.congr_fun (hs.pow_right k).eq x`. Rewrite `e` using `[Module.End.mul_apply, Module.End.mul_apply]`. Conclude with `e.symm`. Establish `hra : |(-r)| ≤ r` using `by rw [abs_neg, abs_of_nonneg (by linarith)]`. Establish `hrc : |r| ≤ r` using `by rw [abs_of_nonneg (by linarith)]`.

Establish `hPa : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (a j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖`. Introduce `j k`. Use `⟨2 ^ k, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hMka]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hPc : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (c j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖`. Introduce `j k`. Use `⟨2 ^ k, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hMkc]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hP : ∀ X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c), ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (X x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖`. Introduce `X hX`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem X h`. Break down `h with ⟨j, rfl⟩ | ⟨j, rfl⟩` into its components or cases.

Conclude with `hPa j`. Conclude with `hPc j`. Consider the case `zero => intro k; exact ⟨0, fun x => by simp⟩`. Consider the case `add X Y _ _ hX hY`. Introduce `k`.

Take `⟨C1, h1⟩` from `hX k`. Take `⟨C2, h2⟩` from `hY k`. Use `⟨C1 + C2, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, map_add, map_add]`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `smul s X _ hX`. Introduce `k`. Take `⟨C1, h1⟩` from `hX k`. Use `⟨‖s‖ * C1, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, map_smul, map_smul, norm_smul, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (h1 x) (norm_nonneg _)`. Establish `hlist : ∀ l : List (Module.End ℂ T), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) → ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Φ ((M ^ k) (l.prod x))‖ ≤ C * ‖Φ ((M ^ (k + l.length)) x)‖`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _ k; exact ⟨1, zero_le_one, fun x => by simp⟩`.

Consider the case `cons X l ih`. Introduce `hXl k`. Take `⟨C1, h1⟩` from `hP X (hXl X (by simp)) k`. Take `⟨C2, hC2, h2⟩` from `ih (fun Y hY => hXl Y (List.mem_cons_of_mem _ hY)) (k + 1)`. Use `⟨max C1 0 * C2, mul_nonneg (le_max_right _ _) hC2, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[List.prod_cons, Module.End.mul_apply, List.length_cons]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, show k + (l.length + 1) = k + 1 + l.length by omega]`. Establish `hmono : ∀ x n i, ‖Φ ((M ^ n) x)‖ ≤ ‖Φ ((M ^ (n + i)) x)‖`. Introduce `x n i`.

Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [← add_assoc, pow_succ', Module.End.mul_apply]`. Conclude with `ih.trans (hx _)`. Take `⟨C, hC0, h⟩` from `hlist l hl 0`.

Use `⟨C, fun x => ?_⟩` and prove the remaining obligations. Establish `h'` using `h x`. Rewrite `h'` using `[pow_zero, Module.End.one_apply, zero_add]`. Take `⟨i, rfl⟩` from `Nat.exists_eq_add_of_le hld`. Conclude with `h'.trans (mul_le_mul_of_nonneg_left (hmono x _ i) hC0)`.
-/
theorem norm_word_le_number_pow : ∀ (T H κ : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype κ] (Φ : T →ₗ[ℂ] H) (a c : κ → Module.End ℂ T) (M : Module.End ℂ T) (r r' : ℝ), 1 ≤ r → r' ≤ r → (∀ j x y, inner ℂ (Φ (c j x)) (Φ y) = inner ℂ (Φ x) (Φ (a j y))) → (∀ j, a j * c j - c j * a j = (r' : ℂ) • 1) → M = ∑ j, c j * a j + (r : ℂ) • 1 → (∀ j, M * a j = a j * (M - (r : ℂ) • 1)) → (∀ j, M * c j = c j * (M + (r : ℂ) • 1)) → ∀ (l : List (Module.End ℂ T)) (d : ℕ), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) → l.length ≤ d → ∃ C : ℝ, ∀ x, ‖Φ (l.prod x)‖ ≤ C * ‖Φ ((M ^ d) x)‖ := by
  intro T H κ _ _ _ _ _ Φ a c M r r' hr hr' hadj hcomm hM hMa hMc l d hl hld

  have hreal : ∀ (s : ℝ) (x : T), RCLike.re (inner ℂ (Φ x) (Φ ((s : ℂ) • x))) = s * ‖Φ x‖ ^ 2 := by
    intro s x
    rw [map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
    left; rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hca : ∀ j x, RCLike.re (inner ℂ (Φ x) (Φ (c j (a j x)))) = ‖Φ (a j x)‖ ^ 2 := by
    intro j x
    rw [← inner_conj_symm, hadj, RCLike.conj_re, inner_self_eq_norm_sq]
  have hMx : ∀ x, M x = ∑ j, c j (a j x) + (r : ℂ) • x := by
    intro x; subst hM; simp [Module.End.mul_apply]
  have hQeq : ∀ x, RCLike.re (inner ℂ (Φ x) (Φ (M x))) = ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 := by
    intro x
    rw [hMx, map_add, inner_add_right, map_add, ← hreal, map_sum, inner_sum, map_sum]
    simp only [hca]
  have hQ : ∀ x, ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 ≤ ‖Φ x‖ * ‖Φ (M x)‖ := by
    intro x; rw [← hQeq]; exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hsum : ∀ x, 0 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2 := fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hrx : ∀ x, r * ‖Φ x‖ ≤ ‖Φ (M x)‖ := by
    intro x
    rcases (norm_nonneg (Φ x)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · refine le_of_mul_le_mul_left ?_ hpos
      nlinarith [hQ x, hsum x]
  have hx : ∀ x, ‖Φ x‖ ≤ ‖Φ (M x)‖ := by
    intro x; nlinarith [hrx x, norm_nonneg (Φ x)]
  have hsq : ∀ x u, 0 ≤ u → u ^ 2 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 → u ≤ ‖Φ (M x)‖ := by
    intro x u hu h
    have h1 := hQ x
    have h2 := mul_le_mul_of_nonneg_right (hx x) (norm_nonneg (Φ (M x)))
    have h3 : u ^ 2 ≤ ‖Φ (M x)‖ ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hu (norm_nonneg _) two_ne_zero).1 h3
  have ha : ∀ j x, ‖Φ (a j x)‖ ≤ ‖Φ (M x)‖ := by
    intro j x
    refine hsq x _ (norm_nonneg _) ?_
    have := Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have : 0 ≤ r * ‖Φ x‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hac : ∀ j, a j * c j = c j * a j + (r' : ℂ) • 1 := fun j => sub_eq_iff_eq_add'.1 (hcomm j)
  have hc : ∀ j x, ‖Φ (c j x)‖ ≤ ‖Φ (M x)‖ := by
    intro j x
    refine hsq x _ (norm_nonneg _) ?_
    have e : ‖Φ (c j x)‖ ^ 2 = ‖Φ (a j x)‖ ^ 2 + r' * ‖Φ x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hadj, ← Module.End.mul_apply, hac, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, map_add, inner_add_right, map_add, hca, hreal]
    have := Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have : r' * ‖Φ x‖ ^ 2 ≤ r * ‖Φ x‖ ^ 2 := mul_le_mul_of_nonneg_right hr' (sq_nonneg _)
    linarith
  have hC : ∀ s : ℝ, Commute M (M + (s : ℂ) • 1) := fun s =>
    (Commute.refl M).add_right ((Commute.one_right M).smul_right _)
  have hshift : ∀ (s : ℝ), |s| ≤ r → ∀ y, ‖Φ ((M + (s : ℂ) • 1) y)‖ ≤ 2 * ‖Φ (M y)‖ := by
    intro s hs y
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul]
    calc ‖Φ (M y) + (s : ℂ) • Φ y‖ ≤ ‖Φ (M y)‖ + ‖(s : ℂ) • Φ y‖ := norm_add_le _ _
      _ = ‖Φ (M y)‖ + |s| * ‖Φ y‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖Φ (M y)‖ + r * ‖Φ y‖ := by gcongr
      _ ≤ 2 * ‖Φ (M y)‖ := by linarith [hrx y]
  have hpow : ∀ (s : ℝ), |s| ≤ r → ∀ k y, ‖Φ (((M + (s : ℂ) • 1) ^ k) y)‖ ≤ 2 ^ k * ‖Φ ((M ^ k) y)‖ := by
    intro s hs k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      have e := LinearMap.congr_fun ((hC s).pow_left k).eq y
      rw [Module.End.mul_apply, Module.End.mul_apply] at e
      rw [pow_succ (M + (s : ℂ) • 1) k, Module.End.mul_apply, pow_succ' M k, Module.End.mul_apply]
      calc ‖Φ (((M + (s : ℂ) • 1) ^ k) ((M + (s : ℂ) • 1) y))‖
          ≤ 2 ^ k * ‖Φ ((M ^ k) ((M + (s : ℂ) • 1) y))‖ := ih _
        _ = 2 ^ k * ‖Φ ((M + (s : ℂ) • 1) ((M ^ k) y))‖ := by rw [e]
        _ ≤ 2 ^ k * (2 * ‖Φ (M ((M ^ k) y))‖) := by gcongr; exact hshift s hs _
        _ = 2 ^ (k + 1) * ‖Φ (M ((M ^ k) y))‖ := by ring
  have hcommx : ∀ (s : ℝ) (k : ℕ) x, M (((M + (s : ℂ) • 1) ^ k) x) = ((M + (s : ℂ) • 1) ^ k) (M x) := by
    intro s k x
    have e := LinearMap.congr_fun ((hC s).pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e
  have hMka : ∀ j (k : ℕ) x, (M ^ k) (a j x) = a j (((M + ((-r : ℝ) : ℂ) • 1) ^ k) x) := by
    intro j k x
    have hs : SemiconjBy (a j) (M + ((-r : ℝ) : ℂ) • 1) M := by
      unfold SemiconjBy; rw [hMa j]; push_cast; rw [neg_smul, ← sub_eq_add_neg]
    have e := LinearMap.congr_fun (hs.pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e.symm
  have hMkc : ∀ j (k : ℕ) x, (M ^ k) (c j x) = c j (((M + (r : ℂ) • 1) ^ k) x) := by
    intro j k x
    have hs : SemiconjBy (c j) (M + (r : ℂ) • 1) M := by
      unfold SemiconjBy; rw [hMc j]
    have e := LinearMap.congr_fun (hs.pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e.symm
  have hra : |(-r)| ≤ r := by rw [abs_neg, abs_of_nonneg (by linarith)]
  have hrc : |r| ≤ r := by rw [abs_of_nonneg (by linarith)]
  have hPa : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (a j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro j k; refine ⟨2 ^ k, fun x => ?_⟩
    rw [hMka]
    calc _ ≤ ‖Φ (M (((M + ((-r : ℝ) : ℂ) • 1) ^ k) x))‖ := ha j _
      _ = ‖Φ (((M + ((-r : ℝ) : ℂ) • 1) ^ k) (M x))‖ := by rw [hcommx]
      _ ≤ 2 ^ k * ‖Φ ((M ^ k) (M x))‖ := hpow _ hra k _
      _ = 2 ^ k * ‖Φ ((M ^ (k + 1)) x)‖ := by rw [pow_succ M k, Module.End.mul_apply]
  have hPc : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (c j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro j k; refine ⟨2 ^ k, fun x => ?_⟩
    rw [hMkc]
    calc _ ≤ ‖Φ (M (((M + (r : ℂ) • 1) ^ k) x))‖ := hc j _
      _ = ‖Φ (((M + (r : ℂ) • 1) ^ k) (M x))‖ := by rw [hcommx]
      _ ≤ 2 ^ k * ‖Φ ((M ^ k) (M x))‖ := hpow _ hrc k _
      _ = 2 ^ k * ‖Φ ((M ^ (k + 1)) x)‖ := by rw [pow_succ M k, Module.End.mul_apply]
  have hP : ∀ X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c), ∀ k : ℕ, ∃ C : ℝ,
      ∀ x, ‖Φ ((M ^ k) (X x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X h =>
      rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact hPa j
      · exact hPc j
    | zero => intro k; exact ⟨0, fun x => by simp⟩
    | add X Y _ _ hX hY =>
      intro k
      obtain ⟨C1, h1⟩ := hX k
      obtain ⟨C2, h2⟩ := hY k
      refine ⟨C1 + C2, fun x => ?_⟩
      rw [LinearMap.add_apply, map_add, map_add]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ C1 * _ + C2 * _ := add_le_add (h1 x) (h2 x)
        _ = _ := by ring
    | smul s X _ hX =>
      intro k
      obtain ⟨C1, h1⟩ := hX k
      refine ⟨‖s‖ * C1, fun x => ?_⟩
      rw [LinearMap.smul_apply, map_smul, map_smul, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 x) (norm_nonneg _)
  have hlist : ∀ l : List (Module.End ℂ T), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) →
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Φ ((M ^ k) (l.prod x))‖ ≤ C * ‖Φ ((M ^ (k + l.length)) x)‖ := by
    intro l
    induction l with
    | nil => intro _ k; exact ⟨1, zero_le_one, fun x => by simp⟩
    | cons X l ih =>
      intro hXl k
      obtain ⟨C1, h1⟩ := hP X (hXl X (by simp)) k
      obtain ⟨C2, hC2, h2⟩ := ih (fun Y hY => hXl Y (List.mem_cons_of_mem _ hY)) (k + 1)
      refine ⟨max C1 0 * C2, mul_nonneg (le_max_right _ _) hC2, fun x => ?_⟩
      rw [List.prod_cons, Module.End.mul_apply, List.length_cons]
      calc _ ≤ C1 * ‖Φ ((M ^ (k + 1)) (l.prod x))‖ := h1 _
        _ ≤ max C1 0 * ‖Φ ((M ^ (k + 1)) (l.prod x))‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C1 0 * (C2 * ‖Φ ((M ^ (k + 1 + l.length)) x)‖) :=
            mul_le_mul_of_nonneg_left (h2 x) (le_max_right _ _)
        _ = max C1 0 * C2 * ‖Φ ((M ^ (k + (l.length + 1))) x)‖ := by
            rw [mul_assoc, show k + (l.length + 1) = k + 1 + l.length by omega]
  have hmono : ∀ x n i, ‖Φ ((M ^ n) x)‖ ≤ ‖Φ ((M ^ (n + i)) x)‖ := by
    intro x n i
    induction i with
    | zero => simp
    | succ i ih => rw [← add_assoc, pow_succ', Module.End.mul_apply]; exact ih.trans (hx _)
  obtain ⟨C, hC0, h⟩ := hlist l hl 0
  refine ⟨C, fun x => ?_⟩
  have h' := h x
  rw [pow_zero, Module.End.one_apply, zero_add] at h'
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hld
  exact h'.trans (mul_le_mul_of_nonneg_left (hmono x _ i) hC0)

end GlobalTheory
