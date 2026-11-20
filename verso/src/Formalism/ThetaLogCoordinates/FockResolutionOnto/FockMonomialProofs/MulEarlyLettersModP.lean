import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementE
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FiltrationBotHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Gen

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)

/- English proof (translation)
Simplify using `[dpow]`.
-/
theorem dpow_zero (c : Fin r) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : dpow p LL j c 0 h = h := by
  simp [dpow]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[zero_add, pow_one, pow_zero, glAct_mul, Nat.cast_one, one_smul, Module.End.one_apply]`. Conclude with `add_comm _ _`. Consider the case `succ k ih`.

Establish `e1 : ∀ n y, glAct p LL j 0 c (((glAct p LL j 0 c) ^ n) y) = ((glAct p LL j 0 c) ^ (n + 1)) y`. Introduce `n y`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Rewrite using `[← e1 (k + 1), ih, map_add, map_smul, glAct_mul, glAct_mul, hx, zero_mul, zero_add, e1, e1]`. Use `push_cast`.

Simplify using `only [add_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem pow_mul_of_sq (c : Fin r) (x g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : glAct p LL j 0 c (glAct p LL j 0 c x) = 0) (k : ℕ) :
    ((glAct p LL j 0 c) ^ (k + 1)) (x * g) = x * ((glAct p LL j 0 c) ^ (k + 1)) g +
      ((k + 1 : ℕ) : ℚ_[p]) • (glAct p LL j 0 c x * ((glAct p LL j 0 c) ^ k) g) := by
  induction k with
  | zero =>
    rw [zero_add, pow_one, pow_zero, glAct_mul, Nat.cast_one, one_smul, Module.End.one_apply]
    exact add_comm _ _
  | succ k ih =>
    have e1 : ∀ n y, glAct p LL j 0 c (((glAct p LL j 0 c) ^ n) y) = ((glAct p LL j 0 c) ^ (n + 1)) y := by
      intro n y
      rw [pow_succ', Module.End.mul_apply]
    rw [← e1 (k + 1), ih, map_add, map_smul, glAct_mul, glAct_mul, hx, zero_mul, zero_add, e1, e1]
    push_cast
    simp only [add_smul, one_smul]
    abel

/- English proof (translation)
Simplify using `only [dpow, LinearMap.smul_apply]`. Rewrite using `[pow_mul_of_sq p LL j c x g hx k, smul_add, smul_smul, mul_smul_comm, mul_smul_comm]`. Use `congr 2`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`.

Establish `h1 : ((k : ℚ_[p]) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Establish `h2 : (k.factorial : ℚ_[p]) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero k`. Clear the denominators using the available nonvanishing facts.
-/
theorem dpow_succ_mul (c : Fin r) (x g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : glAct p LL j 0 c (glAct p LL j 0 c x) = 0) (k : ℕ) :
    dpow p LL j c (k + 1) (x * g) = x * dpow p LL j c (k + 1) g + glAct p LL j 0 c x * dpow p LL j c k g := by
  simp only [dpow, LinearMap.smul_apply]
  rw [pow_mul_of_sq p LL j c x g hx k, smul_add, smul_smul, mul_smul_comm, mul_smul_comm]
  congr 2
  rw [Nat.factorial_succ]
  push_cast
  have h1 : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h2 : (k.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero => rw [dpow_zero, dpow_zero]`. Consider the case `succ k => rw [dpow_succ_mul p LL j c x g (by rw [hx, map_zero]) k, hx, zero_mul, add_zero]`.
-/
theorem dpow_mul_of_zero (c : Fin r) (x g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : glAct p LL j 0 c x = 0) (k : ℕ) :
    dpow p LL j c k (x * g) = x * dpow p LL j c k g := by
  cases k with
  | zero => rw [dpow_zero, dpow_zero]
  | succ k => rw [dpow_succ_mul p LL j c x g (by rw [hx, map_zero]) k, hx, zero_mul, add_zero]

/- English proof (translation)
Take `⟨i, c'⟩` from `v`. Rewrite using `[glAct_X]`. Use `split_ifs with h1 h2 h3 h3`. Rewrite using `[glAct_X, if_pos h1, if_pos h2, if_neg hc]`. Conclude with `map_zero _`.

Rewrite using `[map_neg, glAct_X, if_pos h1, if_neg h2, if_neg (Ne.symm hc), neg_zero]`. Conclude with `map_zero _`. Conclude with `map_zero _`.
-/
theorem glAct_sq_X (c : Fin r) (hc : c ≠ 0) (v : Fin N × Fin r) :
    glAct p LL j 0 c (glAct p LL j 0 c (X v)) = 0 := by
  obtain ⟨i, c'⟩ := v
  rw [glAct_X]
  split_ifs with h1 h2 h3 h3
  · rw [glAct_X, if_pos h1, if_pos h2, if_neg hc]
  · exact map_zero _
  · rw [map_neg, glAct_X, if_pos h1, if_neg h2, if_neg (Ne.symm hc), neg_zero]
  · exact map_zero _
  · exact map_zero _

/- English proof (translation)
Take `⟨i, c'⟩` from `v`. Rewrite using `[glAct_X]`. Use `split_ifs`. Conclude with `(X_mul_int_iff _ _).2 hg`. Rewrite using `[zero_mul]`.

Conclude with `Submodule.zero_mem _`. Rewrite using `[neg_mul]`. Conclude with `Submodule.neg_mem _ ((X_mul_int_iff _ _).2 hg)`. Rewrite using `[zero_mul]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[zero_mul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem glAct_X_mul_int (c : Fin r) (v : Fin N × Fin r) (g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hg : g ∈ IntPol p (Fin N × Fin r)) : glAct p LL j 0 c (X v) * g ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨i, c'⟩ := v
  rw [glAct_X]
  split_ifs
  · exact (X_mul_int_iff _ _).2 hg
  · rw [zero_mul]; exact Submodule.zero_mem _
  · rw [neg_mul]; exact Submodule.neg_mem _ ((X_mul_int_iff _ _).2 hg)
  · rw [zero_mul]; exact Submodule.zero_mem _
  · rw [zero_mul]; exact Submodule.zero_mem _

/- English proof (translation)
Unfold `glAct`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glAct_C (c d : Fin r) (a : ℚ_[p]) : glAct p LL j c d (C a) = 0 := by
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [dpow, LinearMap.smul_apply]`. Rewrite using `[pow_succ, Module.End.mul_apply, glAct_C, map_zero, smul_zero]`.
-/
theorem dpow_succ_C (c : Fin r) (a : ℚ_[p]) (k : ℕ) : dpow p LL j c (k + 1) (C a) = 0 := by
  simp only [dpow, LinearMap.smul_apply]
  rw [pow_succ, Module.End.mul_apply, glAct_C, map_zero, smul_zero]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Introduce `k`. Rewrite using `[map_C]`. Consider the cases of `k with`.

Consider the case `zero`. Rewrite using `[dpow_zero, intPol_iff_norm]`. Introduce `m`. Rewrite using `[coeff_C]`. Use `split_ifs`.

Conclude with `PadicInt.norm_le_one a`. Simplify using the standard rewrite rules. Consider the case `succ k => rw [dpow_succ_C]`. Conclude with `Submodule.zero_mem _`. Consider the case `add f g hf hg`.

Introduce `k`. Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ (hf k) (hg k)`. Consider the case `mul_X f v hf`. Introduce `k`.

Rewrite using `[map_mul, map_X, mul_comm]`. Consider the cases of `k with`. Consider the case `zero`. Rewrite using `[dpow_zero, X_mul_int_iff]`. Use `hf 0` as an intermediate fact.

Rewrite `this` using `[dpow_zero]`. Then use the resulting hypothesis. Consider the case `succ k`. Rewrite using `[dpow_succ_mul p LL j c _ _ (glAct_sq_X p LL j c hc v) k]`. Conclude with `Submodule.add_mem _ ((X_mul_int_iff _ _).2 (hf _)) (glAct_X_mul_int p LL j c v _ (hf k))`.
-/
theorem dpow_int_map (c : Fin r) (hc : c ≠ 0) (P : MvPolynomial (Fin N × Fin r) ℤ_[p]) :
    ∀ k, dpow p LL j c k (map (algebraMap ℤ_[p] ℚ_[p]) P) ∈ IntPol p (Fin N × Fin r) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro k
    rw [map_C]
    cases k with
    | zero =>
      rw [dpow_zero, intPol_iff_norm]
      intro m
      rw [coeff_C]
      split_ifs
      · exact PadicInt.norm_le_one a
      · simp
    | succ k => rw [dpow_succ_C]; exact Submodule.zero_mem _
  | add f g hf hg =>
    intro k
    rw [map_add, map_add]
    exact Submodule.add_mem _ (hf k) (hg k)
  | mul_X f v hf =>
    intro k
    rw [map_mul, map_X, mul_comm]
    cases k with
    | zero =>
      rw [dpow_zero, X_mul_int_iff]
      have := hf 0
      rwa [dpow_zero] at this
    | succ k =>
      rw [dpow_succ_mul p LL j c _ _ (glAct_sq_X p LL j c hc v) k]
      exact Submodule.add_mem _ ((X_mul_int_iff _ _).2 (hf _)) (glAct_X_mul_int p LL j c v _ (hf k))

/- English proof (translation)
Take `⟨P, rfl⟩` from `LinearMap.mem_range.mp hh`. Conclude with `dpow_int_map p LL j c hc P k`.
-/
theorem dpow_int (c : Fin r) (hc : c ≠ 0) (k : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hh : h ∈ IntPol p (Fin N × Fin r)) : dpow p LL j c k h ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hh
  exact dpow_int_map p LL j c hc P k

noncomputable abbrev dw (l : List (Fin r × ℕ)) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (l.map fun ck => dpow p LL j ck.1 ck.2).prod

/- English proof (translation)
Simplify using `only [dw, List.map_cons, List.prod_cons]`. Both sides reduce to the same expression.
-/
theorem dw_cons (ck : Fin r × ℕ) (l : List (Fin r × ℕ)) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    dw p LL j (ck :: l) F = dpow p LL j ck.1 ck.2 (dw p LL j l F) := by
  simp only [dw, List.map_cons, List.prod_cons]; rfl

/- English proof (translation)
Simplify using `only [dw, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]`. Both sides reduce to the same expression.
-/
theorem dw_snoc (ck : Fin r × ℕ) (l : List (Fin r × ℕ)) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    dw p LL j (l ++ [ck]) F = dw p LL j l (dpow p LL j ck.1 ck.2 F) := by
  simp only [dw, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]; rfl

variable (M : WithTop ℤ)

/- English proof (translation)
Introduce `x hx l hl`. Establish `: dw p LL j l x ∈ S`. Proceed by induction on `l with`. Consider the case `nil => exact hx`. Consider the case `cons ck l ih`.

Rewrite using `[dw_cons]`. Conclude with `hS _ (ih fun a ha => hl a (List.mem_cons_of_mem _ ha)) _ (hl ck List.mem_cons_self) _`. Conclude with `hs _ this`.
-/
theorem modCond_of_stable (S : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ x ∈ S, ∀ c : Fin r, c ≠ 0 → ∀ k, dpow p LL j c k x ∈ S)
    (hs : ∀ x ∈ S, ∀ m : Fin N × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M) → ‖coeff m x‖ < 1) :
    ∀ x ∈ S, ModCond p LL j M x := by
  intro x hx l hl
  have : dw p LL j l x ∈ S := by
    induction l with
    | nil => exact hx
    | cons ck l ih =>
      rw [dw_cons]
      exact hS _ (ih fun a ha => hl a (List.mem_cons_of_mem _ ha)) _ (hl ck List.mem_cons_self) _
  exact hs _ this

/- English proof (translation)
The claim follows from `hh [] (by simp)`.
-/
theorem modCond_small (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hh : ModCond p LL j M h) :
    ∀ m : Fin N × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M) → ‖coeff m h‖ < 1 :=
  hh [] (by simp)

/- English proof (translation)
Introduce `l hl m hm`. Use `hh (l ++ [(c, k)]) (by` as an intermediate fact. Introduce `a ha`. Break down `List.mem_append.mp ha with ha | ha` into its components or cases. Conclude with `hl a ha`.

Rewrite using `[List.mem_singleton.mp ha]`. Conclude with `hc) m hm`. Establish `e` using `dw_snoc p LL j (c, k) l h`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem modCond_dpow (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hh : ModCond p LL j M h) (c : Fin r) (hc : c ≠ 0)
    (k : ℕ) : ModCond p LL j M (dpow p LL j c k h) := by
  intro l hl m hm
  have := hh (l ++ [(c, k)]) (by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hl a ha
    · rw [List.mem_singleton.mp ha]; exact hc) m hm
  have e := dw_snoc p LL j (c, k) l h
  rw [e] at this
  exact this

/- English proof (translation)
Introduce `l _ m _`. Rewrite using `[map_zero, coeff_zero, norm_zero]`. Conclude with `one_pos`.
-/
theorem modCond_zero : ModCond p LL j M (0 : MvPolynomial (Fin N × Fin r) ℚ_[p]) := by
  intro l _ m _
  rw [map_zero, coeff_zero, norm_zero]
  exact one_pos

/- English proof (translation)
Introduce `l hl m hm`. Rewrite using `[map_add, coeff_add]`. Conclude with `lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt (hf l hl m hm) (hg l hl m hm))`.
-/
theorem modCond_add (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : ModCond p LL j M f)
    (hg : ModCond p LL j M g) : ModCond p LL j M (f + g) := by
  intro l hl m hm
  rw [map_add, coeff_add]
  exact lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt (hf l hl m hm) (hg l hl m hm))

/- English proof (translation)
Introduce `l hl m hm`. Rewrite using `[map_neg, coeff_neg, norm_neg]`. Conclude with `hf l hl m hm`.
-/
theorem modCond_neg (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : ModCond p LL j M f) :
    ModCond p LL j M (-f) := by
  intro l hl m hm
  rw [map_neg, coeff_neg, norm_neg]
  exact hf l hl m hm

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `modCond_add p LL j M _ _ hf (modCond_neg p LL j M _ hg)`.
-/
theorem modCond_sub (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : ModCond p LL j M f)
    (hg : ModCond p LL j M g) : ModCond p LL j M (f - g) := by
  rw [sub_eq_add_neg]
  exact modCond_add p LL j M _ _ hf (modCond_neg p LL j M _ hg)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact hb`. Consider the case `cons ck l ih`. Rewrite using `[dw_cons]`. Conclude with `dpow_int p LL j _ (hl ck List.mem_cons_self) _ _ (ih fun a ha => hl a (List.mem_cons_of_mem _ ha))`.
-/
theorem dw_int (l : List (Fin r × ℕ)) (hl : ∀ ck ∈ l, ck.1 ≠ 0) (b : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hb : b ∈ IntPol p (Fin N × Fin r)) : dw p LL j l b ∈ IntPol p (Fin N × Fin r) := by
  induction l with
  | nil => exact hb
  | cons ck l ih =>
    rw [dw_cons]
    exact dpow_int p LL j _ (hl ck List.mem_cons_self) _ _ (ih fun a ha => hl a (List.mem_cons_of_mem _ ha))

/- English proof (translation)
Introduce `l hl m _`. Rewrite using `[map_smul, coeff_smul, smul_eq_mul, norm_mul]`. Establish `h1` using `intPol_norm _ (dw_int p LL j l hl b hb) m`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem modCond_p_smul (b : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hb : b ∈ IntPol p (Fin N × Fin r)) :
    ModCond p LL j M ((p : ℚ_[p]) • b) := by
  intro l hl m _
  rw [map_smul, coeff_smul, smul_eq_mul, norm_mul]
  have h1 := intPol_norm _ (dw_int p LL j l hl b hb) m
  calc ‖(p : ℚ_[p])‖ * ‖coeff m (dw p LL j l b)‖ ≤ ‖(p : ℚ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact Padic.norm_p_lt_one

end Gen

/- English proof (translation)
Introduce `p _ N r _ LL j c k hc h hh`. Conclude with `dpow_int p LL j c hc k h hh`.
-/
theorem divided_power_integral : DpowInt := by
  intro p _ N r _ LL j c k hc h hh
  exact dpow_int p LL j c hc k h hh

/- English proof (translation)
Introduce `p _ N r _ LL j M h hh`. Use `modCond_of_stable p LL j M (YCond p (r := r) LL j M : Set _) ?_ ?_ h hh` and prove the remaining obligations. Introduce `x hx c _ k`. Simplify using `only [dpow, LinearMap.smul_apply]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Proceed by induction on `k with`. Consider the case `zero => exact hx`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `ycond_glStable LL j M 0 c _ ih`.

Introduce `x hx m hm`. Establish `h1` using `ycond_le_supp LL j M hx`. Rewrite `h1` using `[mem_restrictSupport_iff]`. Establish `: coeff m x = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hm (h1 (Finset.mem_coe.mpr (mem_support_iff.mpr hne)))`. Rewrite using `[this, norm_zero]`. Conclude with `one_pos`.
-/
theorem mod_p_of_conditions : ModOfY := by
  intro p _ N r _ LL j M h hh
  refine modCond_of_stable p LL j M (YCond p (r := r) LL j M : Set _) ?_ ?_ h hh
  · intro x hx c _ k
    simp only [dpow, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact ycond_glStable LL j M 0 c _ ih
  · intro x hx m hm
    have h1 := ycond_le_supp LL j M hx
    rw [mem_restrictSupport_iff] at h1
    have : coeff m x = 0 := by
      by_contra hne
      exact hm (h1 (Finset.mem_coe.mpr (mem_support_iff.mpr hne)))
    rw [this, norm_zero]
    exact one_pos

/- English proof (translation)
Introduce `p _ K r _ LL j M c h hj hh`. Establish `hlt : ¬ ((Fin.last K : Fin (K + 1)) : ℕ) < j` using `by rw [Fin.val_last]; omega`. Use `modCond_of_stable p LL j M {g | ModCond p LL j M (X (Fin.last K, c) * g)} ?_ ?_ h hh` and prove the remaining obligations. Introduce `x hx a ha k show ModCond p LL j M _`. Rewrite using `[← dpow_mul_of_zero p LL j a _ _ (by rw [glAct_X, if_neg hlt]) k]`.

Conclude with `modCond_dpow p LL j M _ hx a ha k`. Introduce `x hx m hm`. Use `modCond_small p LL j M _ hx (Finsupp.single (Fin.last K, c) 1 + m) (by rw [wt_single_add, if_neg hlt, zero_mul, add_zero]; exact hm)` as an intermediate fact. Rewrite `this` using `[coeff_X_mul]`. Then use the resulting hypothesis.
-/
theorem mul_early_letters_mod_p : MulEarlyModP := by
  intro p _ K r _ LL j M c h hj hh
  have hlt : ¬ ((Fin.last K : Fin (K + 1)) : ℕ) < j := by rw [Fin.val_last]; omega
  refine modCond_of_stable p LL j M {g | ModCond p LL j M (X (Fin.last K, c) * g)} ?_ ?_ h hh
  · intro x hx a ha k
    show ModCond p LL j M _
    rw [← dpow_mul_of_zero p LL j a _ _ (by rw [glAct_X, if_neg hlt]) k]
    exact modCond_dpow p LL j M _ hx a ha k
  · intro x hx m hm
    have := modCond_small p LL j M _ hx (Finsupp.single (Fin.last K, c) 1 + m)
      (by rw [wt_single_add, if_neg hlt, zero_mul, add_zero]; exact hm)
    rwa [coeff_X_mul] at this

section Last

variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)

/- English proof (translation)
Introduce `m hm`. Rewrite using `[coeff_X_mul']`. Use `split_ifs with hs`. Apply `hg` to reduce the goal to its premises. Introduce `hle`.

Apply `hm` to reduce the goal to its premises. Establish `e : Finsupp.single (Fin.last K, c') 1 + (m - Finsupp.single (Fin.last K, c') 1) = m` using `add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))`. Rewrite using `[← e, last_wt LL j hj hv]`. Rewrite `hle` using `[← withTop_shift]`. Use `le_trans ?_ hle` and prove the remaining obligations.

Apply the tactic sequence `exact_mod_cast (by split_ifs <;> omega)`. Rewrite using `[norm_zero]`. Conclude with `one_pos`.
-/
theorem small_last_mul (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c' : Fin r)
    (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hg : ∀ m : Fin (K + 1) × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M + ((-1 : ℤ) : WithTop ℤ)) →
      ‖coeff m g‖ < 1) :
    ∀ m : Fin (K + 1) × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M) →
      ‖coeff m (X (Fin.last K, c') * g)‖ < 1 := by
  classical
  intro m hm
  rw [coeff_X_mul']
  split_ifs with hs
  · apply hg
    intro hle
    apply hm
    have e : Finsupp.single (Fin.last K, c') 1 + (m - Finsupp.single (Fin.last K, c') 1) = m :=
      add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))
    rw [← e, last_wt LL j hj hv]
    rw [← withTop_shift] at hle
    refine le_trans ?_ hle
    exact_mod_cast (by split_ifs <;> omega)
  · rw [norm_zero]; exact one_pos

/- English proof (translation)
Use `modCond_of_stable p LL j M {f | ∃ g g' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p], ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g ∧ ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g' ∧ f = X (Fin.last K, c') * g + X (Fin.last K, (0 : Fin r)) * g'} ?_ ?_ _ ⟨g, g', hg, hg', rfl⟩` and prove the remaining obligations. Introduce and unpack `x ⟨g, g', hg, hg', rfl⟩ a ha k`. Consider the cases of `k with`. Consider the case `zero => rw [dpow_zero]`. Conclude with `⟨g, g', hg, hg', rfl⟩`.

Consider the case `succ k`. Use `⟨dpow p LL j a (k + 1) g, (if a = c' then dpow p LL j a k g else 0) + dpow p LL j a (k + 1) g', modCond_dpow p LL j _ _ hg a ha _, modCond_add p LL j _ _ _ ?_ (modCond_dpow p LL j _ _ hg' a ha _), ?_⟩` and prove the remaining obligations. Use `split_ifs`. Conclude with `modCond_dpow p LL j _ _ hg a ha _`. Conclude with `modCond_zero p LL j _`.

Apply the tactic sequence `rw [map_add, dpow_succ_mul p LL j a _ _ (glAct_sq_X p LL j a ha _), dpow_succ_mul p LL j a _ _ (glAct_sq_X p LL j a ha _), last_X p LL j hj hv, last_X p LL j hj hv, if_neg ha] split_ifs <;> ring`. Introduce and unpack `x ⟨g, g', hg, hg', rfl⟩ m hm`. Rewrite using `[coeff_add]`. Conclude with `lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt (small_last_mul p LL j M hj hv _ _ (modCond_small p LL j _ _ hg) m hm) (small_last_mul p LL j M hj hv _ _ (modCond_small p LL j _ _ hg') m hm))`.
-/
theorem modCond_last_fwd (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c' : Fin r)
    (g g' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hg : ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g) (hg' : ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g') :
    ModCond p LL j M (X (Fin.last K, c') * g + X (Fin.last K, (0 : Fin r)) * g') := by
  refine modCond_of_stable p LL j M {f | ∃ g g' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
    ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g ∧ ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g' ∧
      f = X (Fin.last K, c') * g + X (Fin.last K, (0 : Fin r)) * g'} ?_ ?_ _ ⟨g, g', hg, hg', rfl⟩
  · rintro x ⟨g, g', hg, hg', rfl⟩ a ha k
    cases k with
    | zero => rw [dpow_zero]; exact ⟨g, g', hg, hg', rfl⟩
    | succ k =>
      refine ⟨dpow p LL j a (k + 1) g, (if a = c' then dpow p LL j a k g else 0) + dpow p LL j a (k + 1) g',
        modCond_dpow p LL j _ _ hg a ha _, modCond_add p LL j _ _ _ ?_ (modCond_dpow p LL j _ _ hg' a ha _), ?_⟩
      · split_ifs
        · exact modCond_dpow p LL j _ _ hg a ha _
        · exact modCond_zero p LL j _
      · rw [map_add, dpow_succ_mul p LL j a _ _ (glAct_sq_X p LL j a ha _),
          dpow_succ_mul p LL j a _ _ (glAct_sq_X p LL j a ha _), last_X p LL j hj hv, last_X p LL j hj hv, if_neg ha]
        split_ifs <;> ring
  · rintro x ⟨g, g', hg, hg', rfl⟩ m hm
    rw [coeff_add]
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _)
      (max_lt (small_last_mul p LL j M hj hv _ _ (modCond_small p LL j _ _ hg) m hm)
        (small_last_mul p LL j M hj hv _ _ (modCond_small p LL j _ _ hg') m hm))

/- English proof (translation)
Use `modCond_of_stable p LL j _ {g | ModCond p LL j M (X (Fin.last K, (0 : Fin r)) * g)} ?_ ?_ g hg` and prove the remaining obligations. Introduce `x hx a ha k show ModCond p LL j M _`. Rewrite using `[← dpow_mul_of_zero p LL j a _ _ (by rw [last_X p LL j hj hv, if_neg ha]) k]`. Conclude with `modCond_dpow p LL j M _ hx a ha k`. Introduce `x hx m hm`.

Use `modCond_small p LL j M _ hx (Finsupp.single (Fin.last K, (0 : Fin r)) 1 + m) (by rw [last_wt LL j hj hv, if_pos rfl, withTop_shift]; exact hm)` as an intermediate fact. Rewrite `this` using `[coeff_X_mul]`. Then use the resulting hypothesis.
-/
theorem modCond_last_zero (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true)
    (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hg : ModCond p LL j M (X (Fin.last K, (0 : Fin r)) * g)) :
    ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g := by
  refine modCond_of_stable p LL j _ {g | ModCond p LL j M (X (Fin.last K, (0 : Fin r)) * g)} ?_ ?_ g hg
  · intro x hx a ha k
    show ModCond p LL j M _
    rw [← dpow_mul_of_zero p LL j a _ _ (by rw [last_X p LL j hj hv, if_neg ha]) k]
    exact modCond_dpow p LL j M _ hx a ha k
  · intro x hx m hm
    have := modCond_small p LL j M _ hx (Finsupp.single (Fin.last K, (0 : Fin r)) 1 + m)
      (by rw [last_wt LL j hj hv, if_pos rfl, withTop_shift]; exact hm)
    rwa [coeff_X_mul] at this

end Last

/- English proof (translation)
Introduce `p _ K r _ LL j M c h hj hv hU`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Conclude with `modCond_last_zero p LL j M hj hv h hU`. Establish `hstep : ∀ k, ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c (k + 1) h) → ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c k h)`.

Introduce `k hk`. Apply `modCond_last_zero p LL j M hj hv` to reduce the goal to its premises. Establish `h1` using `modCond_dpow p LL j M _ hU c hc (k + 1)`. Rewrite `h1` using `[dpow_succ_mul p LL j c _ _ (glAct_sq_X p LL j c hc _), last_X p LL j hj hv, if_pos rfl]`. Establish `h2` using `modCond_last_fwd p LL j M hj hv c _ 0 hk (modCond_zero p LL j _)`.

Establish `h3` using `modCond_sub p LL j M _ _ h1 h2`. Establish `e : X (Fin.last K, (0 : Fin r)) * dpow p LL j c k h = X (Fin.last K, c) * dpow p LL j c (k + 1) h + X (Fin.last K, (0 : Fin r)) * dpow p LL j c k h - (X (Fin.last K, c) * dpow p LL j c (k + 1) h + X (Fin.last K, (0 : Fin r)) * 0)` using `by ring`. Rewrite using `[e]`. Conclude with `h3`. Establish `hdown : ∀ n, ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c n h) → ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) h`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro hn`. Rewrite `hn` using `[dpow_zero]`. Then use the resulting hypothesis. Consider the case `succ n ih => exact fun hn => ih (hstep n hn)`.

Take `⟨n, hn⟩` from `raise_nil p LL j c hc h`. Use `hdown n ?_` and prove the remaining obligations. Establish `: dpow p LL j c n h = 0`. Simplify using `only [dpow, LinearMap.smul_apply]`. Rewrite using `[hn, smul_zero]`.

Rewrite using `[this]`. Conclude with `modCond_zero p LL j _`.
-/
theorem mul_last_letter_mod_p : MulLastModP := by
  intro p _ K r _ LL j M c h hj hv hU
  by_cases hc : c = 0
  · subst hc
    exact modCond_last_zero p LL j M hj hv h hU
  · have hstep : ∀ k, ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c (k + 1) h) →
        ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c k h) := by
      intro k hk
      apply modCond_last_zero p LL j M hj hv
      have h1 := modCond_dpow p LL j M _ hU c hc (k + 1)
      rw [dpow_succ_mul p LL j c _ _ (glAct_sq_X p LL j c hc _), last_X p LL j hj hv, if_pos rfl] at h1
      have h2 := modCond_last_fwd p LL j M hj hv c _ 0 hk (modCond_zero p LL j _)
      have h3 := modCond_sub p LL j M _ _ h1 h2
      have e : X (Fin.last K, (0 : Fin r)) * dpow p LL j c k h =
          X (Fin.last K, c) * dpow p LL j c (k + 1) h + X (Fin.last K, (0 : Fin r)) * dpow p LL j c k h -
            (X (Fin.last K, c) * dpow p LL j c (k + 1) h + X (Fin.last K, (0 : Fin r)) * 0) := by ring
      rw [e]
      exact h3
    have hdown : ∀ n, ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c n h) →
        ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) h := by
      intro n
      induction n with
      | zero => intro hn; rwa [dpow_zero] at hn
      | succ n ih => exact fun hn => ih (hstep n hn)
    obtain ⟨n, hn⟩ := raise_nil p LL j c hc h
    refine hdown n ?_
    have : dpow p LL j c n h = 0 := by
      simp only [dpow, LinearMap.smul_apply]
      rw [hn, smul_zero]
    rw [this]
    exact modCond_zero p LL j _

/- English proof (translation)
Rewrite `hx`, the goal using `[intPol_iff_norm]`. Introduce `m`. Rewrite using `[coeff_compP]`. Use `split_ifs`. Conclude with `hx m`.

Simplify using the standard rewrite rules.
-/
theorem compP_mem_intPol {p : ℕ} [Fact p.Prime] {σ : Type} (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ ℚ_[p])
    (hx : x ∈ IntPol p σ) : compP Pr x ∈ IntPol p σ := by
  classical
  rw [intPol_iff_norm] at hx ⊢
  intro m
  rw [coeff_compP]
  split_ifs
  · exact hx m
  · simp

/- English proof (translation)
Introduce `p _ K r _ LL q J M ρ hv hlift h hY hint a ha b hb heq`. Use `set a' := compP (fun m' => MultiDeg LL (Finsupp.single (Fin.last K, ρ) 1 + m')) a with ha'`. Use `set b' := compP (fun m => MultiDeg LL m) b with hb'`. Establish `ha'int : a' ∈ IntPol p (Fin (K + 1) × Fin r)` using `compP_mem_intPol _ a ha`. Establish `hb'int : b' ∈ IntPol p (Fin (K + 1) × Fin r)` using `compP_mem_intPol _ b hb`.

Establish `hpol : h ∈ Pol p r LL` using `hY.1`. Unfold `Pol at hpol`. Rewrite `hpol` using `[mem_restrictSupport_iff]`. Establish `heq' : h = X (Fin.last K, ρ) * a' + (p : ℚ_[p]) • b'`. Use extensionality with `m`.

Establish `h0` using `congrArg (coeff m) heq`. Rewrite `h0` using `[coeff_add, coeff_smul, coeff_X_mul']`. Rewrite using `[coeff_add, coeff_smul, coeff_X_mul', coeff_compP, coeff_compP]`. Distinguish the cases in `hm : MultiDeg LL m`. Rewrite using `[h0, if_pos hm]`.

Use `congr 1`. Use `split_ifs with hs h1`. Both sides reduce to the same expression. It suffices to derive a contradiction. Apply `h1` to reduce the goal to its premises.

Rewrite using `[add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))]`. Conclude with `hm`. Both sides reduce to the same expression. Establish `hz : coeff m h = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hm (hpol (Finset.mem_coe.mpr (mem_support_iff.mpr hne)))`. Rewrite using `[hz, if_neg hm, smul_zero, add_zero]`. Use `split_ifs with hs h1`. It suffices to derive a contradiction. Rewrite `h1` using `[add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))]`.

Conclude with `hm h1`. Both sides reduce to the same expression. Both sides reduce to the same expression. Distinguish the cases in `ho : LL.deg (Fin.last K) = 0`. Establish `hz : a' = 0`.

Use extensionality with `m`. Rewrite using `[coeff_compP, if_neg, coeff_zero]`. Introduce `hm`. Establish `h1` using `hm (Fin.last K)`. Rewrite `h1` using `[ho]`.

Establish `h2` using `(Finset.sum_eq_zero_iff.mp h1) ρ (Finset.mem_univ _)`. Simplify using `at h2`. Use `⟨0, Submodule.zero_mem _, b', hb'int, by rw [mul_zero]; exact Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[heq', hz]`. Establish `he : 1 ≤ LL.deg (Fin.last K)` using `Nat.one_le_iff_ne_zero.mpr ho`.

Establish `ha'pol : a' ∈ Pol p r (setLast LL (LL.deg (Fin.last K) - 1))`. Unfold `Pol`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe, mem_support_iff, coeff_compP]`.

Use `split_ifs at hm with h1`. Conclude with `(multiDeg_pow LL ρ 1 he m).1 h1`. Conclude with `absurd rfl hm`. Establish `hXa : ∀ k, ModCond p LL (J k) (M k) (X (Fin.last K, ρ) * a')`. Introduce `k`.

Establish `e : X (Fin.last K, ρ) * a' = h - (p : ℚ_[p]) • b'` using `by rw [heq']; abel`. Rewrite using `[e]`. Conclude with `modCond_sub p LL _ _ _ _ (mod_p_of_conditions p (K + 1) r LL _ _ h ((Submodule.mem_iInf _).1 hY.2 k)) (modCond_p_smul p LL _ _ b' hb'int)`. Establish `hak : ∀ k, ModCond p (setLast LL (LL.deg (Fin.last K) - 1)) (J k) (shiftLastLetterThresholds K J M 1 k) a'`. Introduce `k`.

Use `show ModCond p LL (J k) (shiftLastLetterThresholds K J M 1 k) a'`. Unfold `shiftLastLetterThresholds`. Use `split_ifs with hk`. Rewrite using `[Nat.cast_one]`. Conclude with `mul_last_letter_mod_p p K r LL (J k) (M k) ρ a' hk hv (hXa k)`.

Conclude with `mul_early_letters_mod_p p K r LL (J k) (M k) ρ a' (by omega) (hXa k)`. Take `⟨h1, hh1Y, hh1int, b1, hb1, e1⟩` from `hlift a' ⟨ha'pol, ha'int⟩ hak`. Use `⟨h1, hh1int, X (Fin.last K, ρ) * b1 + b', Submodule.add_mem _ ((X_mul_int_iff _ _).2 hb1) hb'int, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `(pol_pow (p := p) LL ρ 1 he h1).2 hh1Y.1` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.

Rewrite using `[SetLike.mem_coe, Submodule.mem_iInf]`. Introduce `k`. Use `(yCond_pow (p := p) LL hv ρ 1 (J k) (M k) h1).2 ((Submodule.mem_iInf _).1 hh1Y.2 k)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Rewrite using `[heq', e1, mul_add, mul_smul_comm, smul_add, add_assoc]`.
-/
theorem divided_power_mod_p_of : DivModPOf := by
  classical
  intro p _ K r _ LL q J M ρ hv hlift h hY hint a ha b hb heq
  set a' := compP (fun m' => MultiDeg LL (Finsupp.single (Fin.last K, ρ) 1 + m')) a with ha'
  set b' := compP (fun m => MultiDeg LL m) b with hb'
  have ha'int : a' ∈ IntPol p (Fin (K + 1) × Fin r) := compP_mem_intPol _ a ha
  have hb'int : b' ∈ IntPol p (Fin (K + 1) × Fin r) := compP_mem_intPol _ b hb
  have hpol : h ∈ Pol p r LL := hY.1
  unfold Pol at hpol
  rw [mem_restrictSupport_iff] at hpol
  have heq' : h = X (Fin.last K, ρ) * a' + (p : ℚ_[p]) • b' := by
    ext m
    have h0 := congrArg (coeff m) heq
    rw [coeff_add, coeff_smul, coeff_X_mul'] at h0
    rw [coeff_add, coeff_smul, coeff_X_mul', coeff_compP, coeff_compP]
    by_cases hm : MultiDeg LL m
    · rw [h0, if_pos hm]
      congr 1
      split_ifs with hs h1
      · rfl
      · exfalso
        apply h1
        rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr
          (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))]
        exact hm
      · rfl
    · have hz : coeff m h = 0 := by
        by_contra hne
        exact hm (hpol (Finset.mem_coe.mpr (mem_support_iff.mpr hne)))
      rw [hz, if_neg hm, smul_zero, add_zero]
      split_ifs with hs h1
      · exfalso
        rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr
          (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))] at h1
        exact hm h1
      · rfl
      · rfl
  by_cases ho : LL.deg (Fin.last K) = 0
  · have hz : a' = 0 := by
      ext m
      rw [coeff_compP, if_neg, coeff_zero]
      intro hm
      have h1 := hm (Fin.last K)
      rw [ho] at h1
      have h2 := (Finset.sum_eq_zero_iff.mp h1) ρ (Finset.mem_univ _)
      simp at h2
    refine ⟨0, Submodule.zero_mem _, b', hb'int, by rw [mul_zero]; exact Submodule.zero_mem _, ?_⟩
    rw [heq', hz]
  · have he : 1 ≤ LL.deg (Fin.last K) := Nat.one_le_iff_ne_zero.mpr ho
    have ha'pol : a' ∈ Pol p r (setLast LL (LL.deg (Fin.last K) - 1)) := by
      unfold Pol
      rw [mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_coe, mem_support_iff, coeff_compP] at hm
      split_ifs at hm with h1
      · exact (multiDeg_pow LL ρ 1 he m).1 h1
      · exact absurd rfl hm
    have hXa : ∀ k, ModCond p LL (J k) (M k) (X (Fin.last K, ρ) * a') := by
      intro k
      have e : X (Fin.last K, ρ) * a' = h - (p : ℚ_[p]) • b' := by rw [heq']; abel
      rw [e]
      exact modCond_sub p LL _ _ _ _ (mod_p_of_conditions p (K + 1) r LL _ _ h ((Submodule.mem_iInf _).1 hY.2 k))
        (modCond_p_smul p LL _ _ b' hb'int)
    have hak : ∀ k, ModCond p (setLast LL (LL.deg (Fin.last K) - 1)) (J k) (shiftLastLetterThresholds K J M 1 k) a' := by
      intro k
      show ModCond p LL (J k) (shiftLastLetterThresholds K J M 1 k) a'
      unfold shiftLastLetterThresholds
      split_ifs with hk
      · rw [Nat.cast_one]
        exact mul_last_letter_mod_p p K r LL (J k) (M k) ρ a' hk hv (hXa k)
      · exact mul_early_letters_mod_p p K r LL (J k) (M k) ρ a' (by omega) (hXa k)
    obtain ⟨h1, hh1Y, hh1int, b1, hb1, e1⟩ := hlift a' ⟨ha'pol, ha'int⟩ hak
    refine ⟨h1, hh1int, X (Fin.last K, ρ) * b1 + b',
      Submodule.add_mem _ ((X_mul_int_iff _ _).2 hb1) hb'int, ⟨?_, ?_⟩, ?_⟩
    · have := (pol_pow (p := p) LL ρ 1 he h1).2 hh1Y.1
      rwa [pow_one] at this
    · rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro k
      have := (yCond_pow (p := p) LL hv ρ 1 (J k) (M k) h1).2 ((Submodule.mem_iInf _).1 hh1Y.2 k)
      rwa [pow_one] at this
    · rw [heq', e1, mul_add, mul_smul_comm, smul_add, add_assoc]

end Formalism.InvariantFactorPaths.L4
