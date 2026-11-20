import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreShape
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasW

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < (i : ℕ)` using `Nat.pos_of_ne_zero hne`. Establish `hN : 0 < N` using `lt_of_le_of_lt (Nat.zero_le _) i.isLt`. Establish `h0 : (⟨0, hN⟩ : Fin N) < i`. Rewrite using `[Fin.lt_def]`.

Conclude with `hpos`. Establish `e1` using `hdom _ h0`. Establish `e2` using `hg' ⟨0, hN⟩ (ne_of_lt h0)`. Establish `e3` using `hf _ h0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem top_idx {N : ℕ} (f g : Fin N → ℚ) (i : Fin N) (hdom : ∀ i', i' < i → g i ≤ g i')
    (hg : g i = f i + 1) (hg' : ∀ i', i' ≠ i → g i' = f i') (hf : ∀ i', i' < i → f i' = f i) :
    (i : ℕ) = 0 := by
  by_contra hne
  have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hne
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h0 : (⟨0, hN⟩ : Fin N) < i := by
    rw [Fin.lt_def]
    exact hpos
  have e1 := hdom _ h0
  have e2 := hg' ⟨0, hN⟩ (ne_of_lt h0)
  have e3 := hf _ h0
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hlt : (j : ℕ) + 1 < N`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h0 : j < (⟨(j : ℕ) + 1, hlt⟩ : Fin N)`.

Rewrite using `[Fin.lt_def]`. Conclude with `Nat.lt_succ_self _`. Establish `e1` using `hdom _ h0`. Establish `e2` using `hg' ⟨(j : ℕ) + 1, hlt⟩ (ne_of_gt h0)`. Establish `e3` using `hf _ h0`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bot_idx {N : ℕ} (f g : Fin N → ℚ) (j : Fin N) (hdom : ∀ j', j < j' → g j' ≤ g j)
    (hg : g j = f j - 1) (hg' : ∀ j', j' ≠ j → g j' = f j') (hf : ∀ j', j < j' → f j' = f j) :
    (j : ℕ) + 1 = N := by
  by_contra hne
  have hlt : (j : ℕ) + 1 < N := by
    have := j.isLt
    omega
  have h0 : j < (⟨(j : ℕ) + 1, hlt⟩ : Fin N) := by
    rw [Fin.lt_def]
    exact Nat.lt_succ_self _
  have e1 := hdom _ h0
  have e2 := hg' ⟨(j : ℕ) + 1, hlt⟩ (ne_of_gt h0)
  have e3 := hf _ h0
  linarith

/- English proof (translation)
Establish `h' : RootTo (fun x => ν x + τ) a b (fun x => La x + τ)` using `fun x => by`. Use `h x` as an intermediate fact. Simplify using `only`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[casW_root hab h']`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cas_lt {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) (τ : ℚ)
    (hlt : (r : ℚ) + s < 2 * (La b - La a) + 2 + (rho2 b - rho2 a)) :
    casW (fun x => La x + τ) + ((r : ℚ) + s) < casW (fun x => ν x + τ) := by
  have h' : RootTo (fun x => ν x + τ) a b (fun x => La x + τ) := fun x => by
    have := h x
    simp only
    linarith
  rw [casW_root hab h']
  linarith

/- English proof (translation)
Use `abs_add_le x 1` as an intermediate fact. Rewrite `this` using `[abs_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem abs_up (x : ℚ) : |x + 1| - |x| ≤ 1 := by
  have := abs_add_le x 1
  rw [abs_one] at this
  linarith

/- English proof (translation)
Establish `h` using `abs_add_le x (-1)`. Rewrite `h` using `[abs_neg, abs_one, ← sub_eq_add_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem abs_down (x : ℚ) : |x - 1| - |x| ≤ 1 := by
  have h := abs_add_le x (-1)
  rw [abs_neg, abs_one, ← sub_eq_add_neg] at h
  linarith

/- English proof (translation)
Establish `h1 : (1 : ℚ) ≤ m` using `by exact_mod_cast hm`. Rewrite using `[abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ) - 1), abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abs_pos_down {m : ℕ} (hm : 0 < m) : |(m : ℚ) - 1| - |(m : ℚ)| = -1 := by
  have h1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ) - 1), abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ))]
  ring

/- English proof (translation)
Establish `: (1 : ℚ) ≤ m` using `by exact_mod_cast hm`. Rewrite using `[abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abs_neg_up {m : ℕ} (hm : 0 < m) : |-(m : ℚ) + 1| - |-(m : ℚ)| = -1 := by
  have : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i j hR hi hj hpos`. Establish `hne : (Sum.inr j : Ix r s) ≠ Sum.inl i` using `Sum.inr_ne_inl`. Take `⟨ea, eb, eo⟩` from `cw_root hne hR`. Establish `h0 : (i : ℕ) = 0`.

Use `top_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ eb ?_ hi` and prove the remaining obligations. Introduce `i' hi'`. Conclude with `hD (.inl i') (.inl i) hi'`. Introduce `i' hi'`. Conclude with `eo _ Sum.inl_ne_inr (fun e => hi' (Sum.inl_injective e))`.

Establish `h1 : (j : ℕ) + 1 = s`. Use `bot_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ ea ?_ hj` and prove the remaining obligations. Introduce `j' hj'`. Conclude with `hD (.inr j) (.inr j') hj'`. Introduce `j' hj'`.

Conclude with `eo _ (fun e => hj' (Sum.inr_injective e)) Sum.inr_ne_inl`. Establish `h0' : ((i : ℕ) : ℚ) = 0` using `by exact_mod_cast h0`. Establish `h1' : ((j : ℕ) : ℚ) + 1 = s` using `by exact_mod_cast h1`. Simplify using `only [rho2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `i j hR hj hi hpos`. Establish `hne : (Sum.inl i : Ix r s) ≠ Sum.inr j` using `Sum.inl_ne_inr`. Take `⟨ea, eb, eo⟩` from `cw_root hne hR`. Establish `h0 : (j : ℕ) = 0`. Use `top_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ eb ?_ hj` and prove the remaining obligations.

Introduce `j' hj'`. Conclude with `hD (.inr j') (.inr j) hj'`. Introduce `j' hj'`. Conclude with `eo _ Sum.inr_ne_inl (fun e => hj' (Sum.inr_injective e))`. Establish `h1 : (i : ℕ) + 1 = r`.

Use `bot_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ ea ?_ hi` and prove the remaining obligations. Introduce `i' hi'`. Conclude with `hD (.inl i) (.inl i') hi'`. Introduce `i' hi'`. Conclude with `eo _ (fun e => hi' (Sum.inl_injective e)) Sum.inl_ne_inr`.

Establish `h0' : ((j : ℕ) : ℚ) = 0` using `by exact_mod_cast h0`. Establish `h1' : ((i : ℕ) : ℚ) + 1 = r` using `by exact_mod_cast h1`. Simplify using `only [rho2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem extreme {r s : ℕ} {ν La : Ix r s → ℚ} (hD : Dom ν) :
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inr j) (.inl i) La →
      (∀ i', i' < i → La (.inl i') = La (.inl i)) → (∀ j', j < j' → La (.inr j') = La (.inr j)) →
      0 < La (.inl i) - La (.inr j) →
      (r : ℚ) + s < 2 * (La (.inl i) - La (.inr j)) + 2 + (rho2 (.inl i : Ix r s) - rho2 (.inr j : Ix r s))) ∧
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inl i) (.inr j) La →
      (∀ j', j' < j → La (.inr j') = La (.inr j)) → (∀ i', i < i' → La (.inl i') = La (.inl i)) →
      0 < La (.inr j) - La (.inl i) →
      (r : ℚ) + s < 2 * (La (.inr j) - La (.inl i)) + 2 + (rho2 (.inr j : Ix r s) - rho2 (.inl i : Ix r s))) := by
  constructor
  · intro i j hR hi hj hpos
    have hne : (Sum.inr j : Ix r s) ≠ Sum.inl i := Sum.inr_ne_inl
    obtain ⟨ea, eb, eo⟩ := cw_root hne hR
    have h0 : (i : ℕ) = 0 := by
      refine top_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ eb ?_ hi
      · intro i' hi'
        exact hD (.inl i') (.inl i) hi'
      · intro i' hi'
        exact eo _ Sum.inl_ne_inr (fun e => hi' (Sum.inl_injective e))
    have h1 : (j : ℕ) + 1 = s := by
      refine bot_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ ea ?_ hj
      · intro j' hj'
        exact hD (.inr j) (.inr j') hj'
      · intro j' hj'
        exact eo _ (fun e => hj' (Sum.inr_injective e)) Sum.inr_ne_inl
    have h0' : ((i : ℕ) : ℚ) = 0 := by exact_mod_cast h0
    have h1' : ((j : ℕ) : ℚ) + 1 = s := by exact_mod_cast h1
    simp only [rho2]
    linarith
  · intro i j hR hj hi hpos
    have hne : (Sum.inl i : Ix r s) ≠ Sum.inr j := Sum.inl_ne_inr
    obtain ⟨ea, eb, eo⟩ := cw_root hne hR
    have h0 : (j : ℕ) = 0 := by
      refine top_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ eb ?_ hj
      · intro j' hj'
        exact hD (.inr j') (.inr j) hj'
      · intro j' hj'
        exact eo _ Sum.inr_ne_inl (fun e => hj' (Sum.inr_injective e))
    have h1 : (i : ℕ) + 1 = r := by
      refine bot_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ ea ?_ hi
      · intro i' hi'
        exact hD (.inl i) (.inl i') hi'
      · intro i' hi'
        exact eo _ (fun e => hi' (Sum.inl_injective e)) Sum.inl_ne_inr
    have h0' : ((j : ℕ) : ℚ) = 0 := by exact_mod_cast h0
    have h1' : ((i : ℕ) : ℚ) + 1 = r := by exact_mod_cast h1
    simp only [rho2]
    linarith

/- English proof (translation)
Take `⟨hs, hu⟩` from `shape_pos hp hq hn hm c0 h1 h2`. Use `⟨hs, hu, ?_⟩` and prove the remaining obligations. Introduce `ν a b hab hR hD hS hdeg`. Establish `hne : a ≠ b`. Introduce and unpack `rfl`.

Apply the tactic sequence `rcases a with k | l <;> exact hab trivial`. Apply `cas_lt hne hR` to reduce the goal to its premises. Establish `hdr` using `degW_root (cPair p q) hne hR`. Rewrite `hdr` using `[degW_laPos hp hq]`. Establish `e1 : c0 - cPair r s = n` using `by linarith`.

Establish `e2 : c0 + cPair r s = m` using `by linarith`. Rewrite `hdeg` using `[degW_const, e1, e2, Nat.abs_cast, Nat.abs_cast]`. Establish `hA` using `abs_up (shiftNu (cPair p q) (laPos p q r s n m) b)`. Establish `hB` using `abs_down (shiftNu (cPair p q) (laPos p q r s n m) a)`. Establish `hBeq : |shiftNu (cPair p q) (laPos p q r s n m) a - 1| - |shiftNu (cPair p q) (laPos p q r s n m) a| = 1`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨ea, eb, eo⟩` from `cw_root hne hR`. Establish `hn' : (0 : ℚ) < n` using `by exact_mod_cast hn`. Establish `hm' : (0 : ℚ) < m` using `by exact_mod_cast hm`. Apply the tactic sequence `rcases a with k | l <;> rcases b with k' | l'`.

Conclude with `absurd trivial hab`. Establish `sa : shiftNu (cPair p q) (laPos p q r s n m) (Sum.inl k) = (if (k : ℕ) < p then (n : ℚ) else 0)` using `by show (if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q - cPair p q = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hk : p ≤ (k : ℕ)`. Assume the negation of the conclusion as `hk`.

Use `push_neg at hk`. Rewrite `hBeq` using `[sa, if_pos hk, abs_pos_down hn]`. Evaluate the numerical expressions using `at hBeq`. Establish `hl : (l' : ℕ) < q`. Assume the negation of the conclusion as `hl`.

Use `push_neg at hl`. Establish `h5 : ν (Sum.inr l') + cPair p q ≤ 0` using `hS.2.1 l' hl`. Establish `e : ν (Sum.inr l') = (if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q + 1` using `eb`. Rewrite `e` using `[if_neg (not_lt.mpr hl)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(extreme hD).2 k l' hR ?_ ?_ ?_` and prove the remaining obligations. Introduce `j' hj'`. Establish `hj'' : (j' : ℕ) < q` using `lt_trans (Fin.lt_def.mp hj') hl`. Use `show (if (j' : ℕ) < q then (m : ℚ) else 0) - cPair p q = (if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q`. Rewrite using `[if_pos hj'', if_pos hl]`.

Introduce `i' hi'`. Establish `hi'' : ¬ ((i' : ℕ) < p)` using `not_lt.mpr (le_trans hk (le_of_lt (Fin.lt_def.mp hi')))`. Use `show (if (i' : ℕ) < p then (n : ℚ) else 0) + cPair p q = (if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q`. Rewrite using `[if_neg hi'', if_neg (not_lt.mpr hk)]`. Use `show (0 : ℚ) < ((if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q) - ((if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q)`.

Rewrite using `[if_pos hl, if_neg (not_lt.mpr hk)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `sa : shiftNu (cPair p q) (laPos p q r s n m) (Sum.inr l) = (if (l : ℕ) < q then (m : ℚ) else 0)` using `by show (if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q + cPair p q = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hl : q ≤ (l : ℕ)`.

Assume the negation of the conclusion as `hl`. Use `push_neg at hl`. Rewrite `hBeq` using `[sa, if_pos hl, abs_pos_down hm]`. Evaluate the numerical expressions using `at hBeq`. Establish `hk : (k' : ℕ) < p`.

Assume the negation of the conclusion as `hk`. Use `push_neg at hk`. Establish `h5 : ν (Sum.inl k') - cPair p q ≤ 0` using `hS.1 k' hk`. Establish `e : ν (Sum.inl k') = (if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q + 1` using `eb`. Rewrite `e` using `[if_neg (not_lt.mpr hk)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(extreme hD).1 k' l hR ?_ ?_ ?_` and prove the remaining obligations. Introduce `i' hi'`. Establish `hi'' : (i' : ℕ) < p` using `lt_trans (Fin.lt_def.mp hi') hk`. Use `show (if (i' : ℕ) < p then (n : ℚ) else 0) + cPair p q = (if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q`.

Rewrite using `[if_pos hi'', if_pos hk]`. Introduce `j' hj'`. Establish `hj'' : ¬ ((j' : ℕ) < q)` using `not_lt.mpr (le_trans hl (le_of_lt (Fin.lt_def.mp hj')))`. Use `show (if (j' : ℕ) < q then (m : ℚ) else 0) - cPair p q = (if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q`. Rewrite using `[if_neg hj'', if_neg (not_lt.mpr hl)]`.

Use `show (0 : ℚ) < ((if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q) - ((if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q)`. Rewrite using `[if_pos hk, if_neg (not_lt.mpr hl)]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd trivial hab`.
-/
theorem comb_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 τ : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s)
    (w1 : (0 : ℚ) < n + 2 * cPair p q) (w2 : (0 : ℚ) < m - 2 * cPair p q) :
    CombOK p q c0 τ (laPos p q r s n m) := by
  obtain ⟨hs, hu⟩ := shape_pos hp hq hn hm c0 h1 h2
  refine ⟨hs, hu, ?_⟩
  intro ν a b hab hR hD hS hdeg
  have hne : a ≠ b := by
    rintro rfl
    rcases a with k | l <;> exact hab trivial
  apply cas_lt hne hR
  have hdr := degW_root (cPair p q) hne hR
  rw [degW_laPos hp hq] at hdr
  have e1 : c0 - cPair r s = n := by linarith
  have e2 : c0 + cPair r s = m := by linarith
  rw [degW_const, e1, e2, Nat.abs_cast, Nat.abs_cast] at hdeg
  have hA := abs_up (shiftNu (cPair p q) (laPos p q r s n m) b)
  have hB := abs_down (shiftNu (cPair p q) (laPos p q r s n m) a)
  have hBeq : |shiftNu (cPair p q) (laPos p q r s n m) a - 1| -
      |shiftNu (cPair p q) (laPos p q r s n m) a| = 1 := by
    linarith
  obtain ⟨ea, eb, eo⟩ := cw_root hne hR
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  rcases a with k | l <;> rcases b with k' | l'
  · exact absurd trivial hab
  · have sa : shiftNu (cPair p q) (laPos p q r s n m) (Sum.inl k) =
        (if (k : ℕ) < p then (n : ℚ) else 0) := by
      show (if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q - cPair p q = _
      ring
    have hk : p ≤ (k : ℕ) := by
      by_contra hk
      push_neg at hk
      rw [sa, if_pos hk, abs_pos_down hn] at hBeq
      norm_num at hBeq
    have hl : (l' : ℕ) < q := by
      by_contra hl
      push_neg at hl
      have h5 : ν (Sum.inr l') + cPair p q ≤ 0 := hS.2.1 l' hl
      have e : ν (Sum.inr l') = (if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q + 1 := eb
      rw [if_neg (not_lt.mpr hl)] at e
      linarith
    refine (extreme hD).2 k l' hR ?_ ?_ ?_
    · intro j' hj'
      have hj'' : (j' : ℕ) < q := lt_trans (Fin.lt_def.mp hj') hl
      show (if (j' : ℕ) < q then (m : ℚ) else 0) - cPair p q =
        (if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q
      rw [if_pos hj'', if_pos hl]
    · intro i' hi'
      have hi'' : ¬ ((i' : ℕ) < p) := not_lt.mpr (le_trans hk (le_of_lt (Fin.lt_def.mp hi')))
      show (if (i' : ℕ) < p then (n : ℚ) else 0) + cPair p q =
        (if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q
      rw [if_neg hi'', if_neg (not_lt.mpr hk)]
    · show (0 : ℚ) < ((if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q) -
        ((if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q)
      rw [if_pos hl, if_neg (not_lt.mpr hk)]
      linarith
  · have sa : shiftNu (cPair p q) (laPos p q r s n m) (Sum.inr l) =
        (if (l : ℕ) < q then (m : ℚ) else 0) := by
      show (if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q + cPair p q = _
      ring
    have hl : q ≤ (l : ℕ) := by
      by_contra hl
      push_neg at hl
      rw [sa, if_pos hl, abs_pos_down hm] at hBeq
      norm_num at hBeq
    have hk : (k' : ℕ) < p := by
      by_contra hk
      push_neg at hk
      have h5 : ν (Sum.inl k') - cPair p q ≤ 0 := hS.1 k' hk
      have e : ν (Sum.inl k') = (if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q + 1 := eb
      rw [if_neg (not_lt.mpr hk)] at e
      linarith
    refine (extreme hD).1 k' l hR ?_ ?_ ?_
    · intro i' hi'
      have hi'' : (i' : ℕ) < p := lt_trans (Fin.lt_def.mp hi') hk
      show (if (i' : ℕ) < p then (n : ℚ) else 0) + cPair p q =
        (if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q
      rw [if_pos hi'', if_pos hk]
    · intro j' hj'
      have hj'' : ¬ ((j' : ℕ) < q) := not_lt.mpr (le_trans hl (le_of_lt (Fin.lt_def.mp hj')))
      show (if (j' : ℕ) < q then (m : ℚ) else 0) - cPair p q =
        (if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q
      rw [if_neg hj'', if_neg (not_lt.mpr hl)]
    · show (0 : ℚ) < ((if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q) -
        ((if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q)
      rw [if_pos hk, if_neg (not_lt.mpr hl)]
      linarith
  · exact absurd trivial hab

/- English proof (translation)
Take `⟨hs, hu⟩` from `shape_neg hq hp hn hm c0 h1 h2`. Use `⟨hs, hu, ?_⟩` and prove the remaining obligations. Introduce `ν a b hab hR hD hS hdeg`. Establish `hne : a ≠ b`. Introduce and unpack `rfl`.

Apply the tactic sequence `rcases a with k | l <;> exact hab trivial`. Apply `cas_lt hne hR` to reduce the goal to its premises. Establish `hdr` using `degW_root (cPair p q) hne hR`. Rewrite `hdr` using `[degW_laNeg hq hp]`. Establish `e1 : c0 - cPair r s = -(m : ℚ)` using `by linarith`.

Establish `e2 : c0 + cPair r s = -(n : ℚ)` using `by linarith`. Rewrite `hdeg` using `[degW_const, e1, e2, abs_neg, abs_neg, Nat.abs_cast, Nat.abs_cast]`. Establish `hA` using `abs_up (shiftNu (cPair p q) (laNeg p q r s n m) b)`. Establish `hB` using `abs_down (shiftNu (cPair p q) (laNeg p q r s n m) a)`. Establish `hAeq : |shiftNu (cPair p q) (laNeg p q r s n m) b + 1| - |shiftNu (cPair p q) (laNeg p q r s n m) b| = 1`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨ea, eb, eo⟩` from `cw_root hne hR`. Establish `hn' : (0 : ℚ) < n` using `by exact_mod_cast hn`. Establish `hm' : (0 : ℚ) < m` using `by exact_mod_cast hm`. Apply the tactic sequence `rcases a with k | l <;> rcases b with k' | l'`.

Conclude with `absurd trivial hab`. Establish `sb : shiftNu (cPair p q) (laNeg p q r s n m) (Sum.inr l') = (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0)` using `by show (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q + cPair p q = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hl : ¬ (s ≤ (l' : ℕ) + p)`. Introduce `hl`.

Rewrite `hAeq` using `[sb, if_pos hl, abs_neg_up hm]`. Evaluate the numerical expressions using `at hAeq`. Establish `hk : r ≤ (k : ℕ) + q`. Assume the negation of the conclusion as `hk`. Use `push_neg at hk`.

Establish `h5 : 0 ≤ ν (Sum.inl k) - cPair p q` using `hS.2.2.1 k hk`. Establish `e : ν (Sum.inl k) = (if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q - 1` using `ea`. Rewrite `e` using `[if_neg (not_le.mpr hk)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(extreme hD).2 k l' hR ?_ ?_ ?_` and prove the remaining obligations.

Introduce `j' hj'`. Establish `hj'' : ¬ (s ≤ (j' : ℕ) + p)`. Use `Fin.lt_def.mp hj'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `show (if s ≤ (j' : ℕ) + p then -(m : ℚ) else 0) - cPair p q = (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q`.

Rewrite using `[if_neg hj'', if_neg hl]`. Introduce `i' hi'`. Establish `hi'' : r ≤ (i' : ℕ) + q`. Use `Fin.lt_def.mp hi'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `show (if r ≤ (i' : ℕ) + q then -(n : ℚ) else 0) + cPair p q = (if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q`. Rewrite using `[if_pos hi'', if_pos hk]`. Use `show (0 : ℚ) < ((if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q) - ((if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q)`. Rewrite using `[if_neg hl, if_pos hk]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `sb : shiftNu (cPair p q) (laNeg p q r s n m) (Sum.inl k') = (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0)` using `by show (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q - cPair p q = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hk : ¬ (r ≤ (k' : ℕ) + q)`. Introduce `hk`. Rewrite `hAeq` using `[sb, if_pos hk, abs_neg_up hn]`.

Evaluate the numerical expressions using `at hAeq`. Establish `hl : s ≤ (l : ℕ) + p`. Assume the negation of the conclusion as `hl`. Use `push_neg at hl`. Establish `h5 : 0 ≤ ν (Sum.inr l) + cPair p q` using `hS.2.2.2 l hl`.

Establish `e : ν (Sum.inr l) = (if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q - 1` using `ea`. Rewrite `e` using `[if_neg (not_le.mpr hl)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(extreme hD).1 k' l hR ?_ ?_ ?_` and prove the remaining obligations. Introduce `i' hi'`.

Establish `hi'' : ¬ (r ≤ (i' : ℕ) + q)`. Use `Fin.lt_def.mp hi'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `show (if r ≤ (i' : ℕ) + q then -(n : ℚ) else 0) + cPair p q = (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q`. Rewrite using `[if_neg hi'', if_neg hk]`.

Introduce `j' hj'`. Establish `hj'' : s ≤ (j' : ℕ) + p`. Use `Fin.lt_def.mp hj'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `show (if s ≤ (j' : ℕ) + p then -(m : ℚ) else 0) - cPair p q = (if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q`.

Rewrite using `[if_pos hj'', if_pos hl]`. Use `show (0 : ℚ) < ((if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q) - ((if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q)`. Rewrite using `[if_neg hk, if_pos hl]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd trivial hab`.
-/
theorem comb_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 τ : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s)
    (w1 : (0 : ℚ) < m + 2 * cPair p q) (w2 : (0 : ℚ) < n - 2 * cPair p q) :
    CombOK p q c0 τ (laNeg p q r s n m) := by
  obtain ⟨hs, hu⟩ := shape_neg hq hp hn hm c0 h1 h2
  refine ⟨hs, hu, ?_⟩
  intro ν a b hab hR hD hS hdeg
  have hne : a ≠ b := by
    rintro rfl
    rcases a with k | l <;> exact hab trivial
  apply cas_lt hne hR
  have hdr := degW_root (cPair p q) hne hR
  rw [degW_laNeg hq hp] at hdr
  have e1 : c0 - cPair r s = -(m : ℚ) := by linarith
  have e2 : c0 + cPair r s = -(n : ℚ) := by linarith
  rw [degW_const, e1, e2, abs_neg, abs_neg, Nat.abs_cast, Nat.abs_cast] at hdeg
  have hA := abs_up (shiftNu (cPair p q) (laNeg p q r s n m) b)
  have hB := abs_down (shiftNu (cPair p q) (laNeg p q r s n m) a)
  have hAeq : |shiftNu (cPair p q) (laNeg p q r s n m) b + 1| -
      |shiftNu (cPair p q) (laNeg p q r s n m) b| = 1 := by
    linarith
  obtain ⟨ea, eb, eo⟩ := cw_root hne hR
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  rcases a with k | l <;> rcases b with k' | l'
  · exact absurd trivial hab
  · have sb : shiftNu (cPair p q) (laNeg p q r s n m) (Sum.inr l') =
        (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) := by
      show (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q + cPair p q = _
      ring
    have hl : ¬ (s ≤ (l' : ℕ) + p) := by
      intro hl
      rw [sb, if_pos hl, abs_neg_up hm] at hAeq
      norm_num at hAeq
    have hk : r ≤ (k : ℕ) + q := by
      by_contra hk
      push_neg at hk
      have h5 : 0 ≤ ν (Sum.inl k) - cPair p q := hS.2.2.1 k hk
      have e : ν (Sum.inl k) = (if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q - 1 := ea
      rw [if_neg (not_le.mpr hk)] at e
      linarith
    refine (extreme hD).2 k l' hR ?_ ?_ ?_
    · intro j' hj'
      have hj'' : ¬ (s ≤ (j' : ℕ) + p) := by
        have := Fin.lt_def.mp hj'
        omega
      show (if s ≤ (j' : ℕ) + p then -(m : ℚ) else 0) - cPair p q =
        (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q
      rw [if_neg hj'', if_neg hl]
    · intro i' hi'
      have hi'' : r ≤ (i' : ℕ) + q := by
        have := Fin.lt_def.mp hi'
        omega
      show (if r ≤ (i' : ℕ) + q then -(n : ℚ) else 0) + cPair p q =
        (if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q
      rw [if_pos hi'', if_pos hk]
    · show (0 : ℚ) < ((if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q) -
        ((if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q)
      rw [if_neg hl, if_pos hk]
      linarith
  · have sb : shiftNu (cPair p q) (laNeg p q r s n m) (Sum.inl k') =
        (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) := by
      show (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q - cPair p q = _
      ring
    have hk : ¬ (r ≤ (k' : ℕ) + q) := by
      intro hk
      rw [sb, if_pos hk, abs_neg_up hn] at hAeq
      norm_num at hAeq
    have hl : s ≤ (l : ℕ) + p := by
      by_contra hl
      push_neg at hl
      have h5 : 0 ≤ ν (Sum.inr l) + cPair p q := hS.2.2.2 l hl
      have e : ν (Sum.inr l) = (if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q - 1 := ea
      rw [if_neg (not_le.mpr hl)] at e
      linarith
    refine (extreme hD).1 k' l hR ?_ ?_ ?_
    · intro i' hi'
      have hi'' : ¬ (r ≤ (i' : ℕ) + q) := by
        have := Fin.lt_def.mp hi'
        omega
      show (if r ≤ (i' : ℕ) + q then -(n : ℚ) else 0) + cPair p q =
        (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q
      rw [if_neg hi'', if_neg hk]
    · intro j' hj'
      have hj'' : s ≤ (j' : ℕ) + p := by
        have := Fin.lt_def.mp hj'
        omega
      show (if s ≤ (j' : ℕ) + p then -(m : ℚ) else 0) - cPair p q =
        (if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q
      rw [if_pos hj'', if_pos hl]
    · show (0 : ℚ) < ((if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q) -
        ((if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q)
      rw [if_neg hk, if_pos hl]
      linarith
  · exact absurd trivial hab

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩` from `h`. Establish `hn2 : 2 * nD D = D.κ + 2 * D.y - D.d`. Unfold `nD`. Use `Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)` and prove the remaining obligations. Simplify using `only [RealData.y, RealData.d]`.

Use linear arithmetic over natural numbers and integers. Establish `hm2 : 2 * mD D = D.κ + D.d - 2 * D.y`. Unfold `mD`. Use `Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)` and prove the remaining obligations. Simplify using `only [RealData.y, RealData.d]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [RealData.y, RealData.d] at hn2 hm2`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `all_goals try simp only [RealData.R, RealData.S, RealData.P, RealData.Q, RealData.P', RealData.Q', RealData.y, RealData.d]`. Apply the tactic sequence `all_goals omega`.
-/
theorem nat_facts {D : RealData} (h : D.Hyp) :
    D.R + D.p + D.q = D.a + D.a' ∧ D.S = D.p + D.q ∧ D.P + D.p = D.a ∧ D.Q = D.p ∧ D.P' = D.q ∧
      D.Q' + D.q = D.a' ∧ 2 * nD D + D.a + D.a' = D.κ + 2 * D.p + 2 * D.q ∧
      2 * mD D + 2 * D.p + 2 * D.q = D.κ + D.a + D.a' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hn2 : 2 * nD D = D.κ + 2 * D.y - D.d := by
    unfold nD
    refine Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)
    simp only [RealData.y, RealData.d]
    omega
  have hm2 : 2 * mD D = D.κ + D.d - 2 * D.y := by
    unfold mD
    refine Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)
    simp only [RealData.y, RealData.d]
    omega
  simp only [RealData.y, RealData.d] at hn2 hm2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [RealData.R, RealData.S, RealData.P, RealData.Q, RealData.P', RealData.Q',
    RealData.y, RealData.d]
  all_goals omega

/- English proof (translation)
Take `⟨e1, e2, e3, e4, e5, e6, e7, e8⟩` from `nat_facts h`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by positivity, by positivity⟩` and prove the remaining obligations. Conclude with `e1` after adjusting the coercions. Conclude with `e2` after adjusting the coercions. Conclude with `e3` after adjusting the coercions.

Conclude with `e4` after adjusting the coercions. Conclude with `e5` after adjusting the coercions. Conclude with `e6` after adjusting the coercions. Conclude with `e7` after adjusting the coercions. Conclude with `e8` after adjusting the coercions.

Conclude with `h.h2` after adjusting the coercions. Conclude with `h.h5` after adjusting the coercions. Conclude with `h.a_gt` after adjusting the coercions.
-/
theorem rat_facts {D : RealData} (h : D.Hyp) :
    (D.R : ℚ) + D.p + D.q = D.a + D.a' ∧ (D.S : ℚ) = D.p + D.q ∧ (D.P : ℚ) + D.p = D.a ∧ (D.Q : ℚ) = D.p ∧
      (D.P' : ℚ) = D.q ∧ (D.Q' : ℚ) + D.q = D.a' ∧ 2 * (nD D : ℚ) + D.a + D.a' = D.κ + 2 * D.p + 2 * D.q ∧
      2 * (mD D : ℚ) + 2 * D.p + 2 * D.q = D.κ + D.a + D.a' ∧ (D.a : ℚ) + D.a' < D.κ ∧
      2 * ((D.p : ℚ) + D.q) < D.a' ∧ (D.a' : ℚ) < D.a ∧ (0 : ℚ) ≤ D.p ∧ (0 : ℚ) ≤ D.q := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by positivity, by positivity⟩
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3
  · exact_mod_cast e4
  · exact_mod_cast e5
  · exact_mod_cast e6
  · exact_mod_cast e7
  · exact_mod_cast e8
  · exact_mod_cast h.h2
  · exact_mod_cast h.h5
  · exact_mod_cast h.a_gt

/- English proof (translation)
Take `⟨e1, e2, e3, e4, e5, e6, e7, e8⟩` from `nat_facts h`. Take `⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩` from `rat_facts h`. Use `h.h2` as an intermediate fact. Use `h.h5` as an intermediate fact. Use `h.a_gt` as an intermediate fact.

Use `⟨by omega, by omega, ?_, ?_, by omega, by omega, by omega, by omega⟩` and prove the remaining obligations. Simplify using `only [cPair]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [cPair]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nm_facts {D : RealData} (h : D.Hyp) :
    0 < nD D ∧ 0 < mD D ∧ ((D.κ : ℚ) / 2 = nD D + cPair D.R D.S) ∧ ((D.κ : ℚ) / 2 = mD D - cPair D.R D.S) ∧
      D.P ≤ D.R ∧ D.Q ≤ D.S ∧ D.Q' ≤ D.R ∧ D.P' ≤ D.S := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := rat_facts h
  have := h.h2; have := h.h5; have := h.a_gt
  refine ⟨by omega, by omega, ?_, ?_, by omega, by omega, by omega, by omega⟩
  · simp only [cPair]; linarith
  · simp only [cPair]; linarith

/- English proof (translation)
Take `⟨e1, e2, e3, e4, e5, e6, e7, e8⟩` from `nat_facts h`. Take `⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩` from `rat_facts h`. Use function extensionality and compare the values at `x`. Break down `x with k | l` into its components or cases. Simplify using `only [laNeg, laPos, cPair]`.

Distinguish the cases in `hk : (k : ℕ) < D.P`. Rewrite using `[if_pos hk, if_neg (by omega)]; linarith`. Rewrite using `[if_neg hk, if_pos (by omega)]; linarith`. Simplify using `only [laNeg, laPos, cPair]`. Distinguish the cases in `hk : (l : ℕ) < D.Q`.

Rewrite using `[if_pos hk, if_neg (by omega)]; linarith`. Rewrite using `[if_neg hk, if_pos (by omega)]; linarith`.
-/
theorem la_eq {D : RealData} (h : D.Hyp) :
    (fun x => laNeg D.P' D.Q' D.R D.S (nD D) (mD D) x + (D.κ : ℚ) / 2) =
      fun x => laPos D.P D.Q D.R D.S (nD D) (mD D) x + 0 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := rat_facts h
  funext x
  rcases x with k | l
  · simp only [laNeg, laPos, cPair]
    by_cases hk : (k : ℕ) < D.P
    · rw [if_pos hk, if_neg (by omega)]; linarith
    · rw [if_neg hk, if_pos (by omega)]; linarith
  · simp only [laNeg, laPos, cPair]
    by_cases hk : (l : ℕ) < D.Q
    · rw [if_pos hk, if_neg (by omega)]; linarith
    · rw [if_neg hk, if_pos (by omega)]; linarith

/- English proof (translation)
Take `⟨hn, hm, e1, e2, hP, hQ, -, -⟩` from `nm_facts h`. Take `⟨f1, f2, f3, f4, f5, f6, f7, f8, g1, g2, g3, g4, g5⟩` from `rat_facts h`. Apply the tactic sequence `refine comb_pos hP hQ hn hm _ _ e1 e2 ?_ ?_ <;> simp only [cPair] <;> linarith`.
-/
theorem combV {D : RealData} (h : D.Hyp) :
    CombOK D.P D.Q ((D.κ : ℚ) / 2) 0 (laPos D.P D.Q D.R D.S (nD D) (mD D)) := by
  obtain ⟨hn, hm, e1, e2, hP, hQ, -, -⟩ := nm_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, g1, g2, g3, g4, g5⟩ := rat_facts h
  refine comb_pos hP hQ hn hm _ _ e1 e2 ?_ ?_ <;> simp only [cPair] <;> linarith

/- English proof (translation)
Take `⟨hn, hm, e1, e2, -, -, hQ, hP⟩` from `nm_facts h`. Take `⟨f1, f2, f3, f4, f5, f6, f7, f8, g1, g2, g3, g4, g5⟩` from `rat_facts h`. Apply the tactic sequence `refine comb_neg hQ hP hn hm _ _ (by linarith) (by linarith) ?_ ?_ <;> simp only [cPair] <;> linarith`.
-/
theorem combV' {D : RealData} (h : D.Hyp) :
    CombOK D.P' D.Q' (-((D.κ : ℚ) / 2)) ((D.κ : ℚ) / 2) (laNeg D.P' D.Q' D.R D.S (nD D) (mD D)) := by
  obtain ⟨hn, hm, e1, e2, -, -, hQ, hP⟩ := nm_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, g1, g2, g3, g4, g5⟩ := rat_facts h
  refine comb_neg hQ hP hn hm _ _ (by linarith) (by linarith) ?_ ?_ <;> simp only [cPair] <;> linarith

end PositivityTheory.KReal

end
