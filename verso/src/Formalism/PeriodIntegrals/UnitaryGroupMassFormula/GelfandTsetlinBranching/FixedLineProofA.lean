import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ProdMkPtA

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p v hp => simp [hp]`.
-/
theorem eval_aeval_poly_A {σ : Type*} (Y : σ → Polynomial ℂ) (f : MvPolynomial σ ℂ) (e : ℂ) :
    (aeval Y f).eval e = eval (fun v => (Y v).eval e) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `hne : i ≠ i'`. Introduce `e`. Rewrite `hii` using `[e]`.

Use linear arithmetic over natural numbers and integers. Establish `hlt' : Fin.castSucc i < Fin.castSucc i'`. Rewrite using `[Fin.castSucc_lt_castSucc_iff, Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Use `set νp := ν (Fin.castSucc i') with hνp`.

Set `dv : ℂ → Fin n → ℂ` to `fun e a => if a = i then e else if a = i' then -1 / e else 1`. Set `zz : ℂ → Fin (n + 1) → ℂ` to `fun e s => if s = Fin.castSucc i' then -1 / e else 1`. Set `Y : Fin (n + 1) × Fin (n + 1) → Polynomial ℂ` to `fun v => Fin.lastCases (if v.2 = Fin.castSucc i' then 0 else 1) (fun a => Fin.lastCases 0 (fun k => if a = i then (if k = i then Polynomial.X else if k = i' then 1 else 0) else if a = i' then (if k = i then 1 else 0) else (if k = a then 1 else 0)) v.2) v.1`. Establish `hpt : ∀ e : ℂ, e ≠ 0 → (fun v => (Y v).eval e) = lhwline_rowOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e)))`. Introduce `e he`.

Use function extensionality and compare the values at `v`. Take `⟨ρ, s⟩` from `v`. Proceed by induction on `ρ using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `s using Fin.lastCases with`.

Consider the case `last`. Simplify using `[Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, (Fin.castSucc_lt_last i').ne', (Fin.castSucc_lt_last i).ne']`. Consider the case `cast k`. Simplify using `only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.castSucc_inj, (Fin.castSucc_lt_last i').ne', if_false]`. Distinguish the cases in `hk : k = i'`.

Substitute `hk` using the available equality. Simplify using `[hne]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hk]`. Consider the case `cast a`.

Proceed by induction on `s using Fin.lastCases with`. Consider the case `last`. Simplify using `[Y, lhwline_rowOp, lhwline_colOp, mkPtA, (Fin.castSucc_lt_last i').ne']`. Consider the case `cast k`. Simplify using `only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, dv, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.castSucc_inj]`.

Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality. Establish `hai : a ≠ i'` using `hne`. Distinguish the cases in `hk : k = a`. Substitute `hk` using the available equality.

Simplify using `[hai]`. Distinguish the cases in `hk' : k = i'`. Substitute `hk'` using the available equality. Simplify using `[hai, hk, Ne.symm hai, hne, Ne.symm hne]`. Clear the denominators using the available nonvanishing facts.

Simplify using `[hai, hk, hk']`. Distinguish the cases in `ha' : a = i'`. Substitute `ha'` using the available equality. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using `[ha, hne, Ne.symm hne]`. Clear the denominators using the available nonvanishing facts. Distinguish the cases in `hk' : k = a`. Substitute `hk'` using the available equality. Simplify using `[ha, hk, hne, Ne.symm hne]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[ha, hk, hk', Ne.symm hk']`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using `[ha, ha', Ne.symm ha, hne, Ne.symm hne]`. Distinguish the cases in `hk' : k = i'`. Substitute `hk'` using the available equality. Simplify using `[ha, ha', hk, Ne.symm ha', Ne.symm ha]`. Apply the tactic sequence `by_cases hka : k = a <;> simp [ha, ha', hk, hk', hka, Ne.symm ha, Ne.symm ha']`.

Establish `hval : ∀ e : ℂ, e ≠ 0 → (aeval Y f).eval e = coeff (mStarA kap ν) f * (e ^ kap i * (-1 / e) ^ νp)`. Introduce `e he`. Establish `e1` using `hR (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e))) (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt' (by simp)`. Establish `e2` using `hC (mkPtA (dv e) (zz e)) (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt'`. Simplify using `only at e1 e2`.

Rewrite using `[eval_aeval_poly_A, hpt e he, e1, e2, eval_D_A kap ν f hcol hrow _ (mkPtA_D _ _), prod_mkPtA]`. Use `congr 1`. Establish `h1 : ∏ a, dv e a ^ kap a = e ^ kap i * (-1 / e) ^ kap i'`. Establish `: ∀ a, dv e a ^ kap a = (if a = i then e ^ kap i else 1) * (if a = i' then (-1 / e) ^ kap i' else 1)`. Introduce `a`.

Distinguish the cases in `h1 : a = i`. Substitute `h1` using the available equality. Simplify using `[dv, hne]`. Distinguish the cases in `h2 : a = i'`. Substitute `h2` using the available equality.

Simplify using `[dv, h1]`. Simplify using `[dv, h1, h2]`. Rewrite using `[Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]`. Establish `h2 : ∏ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) = (-1 / e) ^ (νp - kap i')`. Establish `: ∀ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) = if k = i' then (-1 / e) ^ (νp - kap i') else 1`.

Introduce `k`. Distinguish the cases in `hk : k = i'`. Substitute `hk` using the available equality. Simplify using `[zz, hνp]`. Simplify using `[zz, hk]`.

Rewrite using `[Finset.prod_congr rfl (fun k _ => this k), Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]`. Establish `h3 : zz e (Fin.last n) = 1`. Simplify using `[zz, (Fin.castSucc_lt_last i').ne']`. Rewrite using `[h1, h2, h3, one_pow, mul_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]`. Use `set p := aeval Y f with hp`.

Use `set q : Polynomial ℂ := p * Polynomial.X ^ νp - Polynomial.C (coeff (mStarA kap ν) f * (-1) ^ νp) * Polynomial.X ^ (kap i) with hq`. Establish `hq0 : q = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Apply `Set.Infinite.mono _ (Set.finite_singleton (0 : ℂ)).infinite_compl` to reduce the goal to its premises. Introduce `e he`.

Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff] at he`. Simplify using `only [Set.mem_setOf_eq, Polynomial.IsRoot, hq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hval e he]`. Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hco` using `congrArg (fun r : Polynomial ℂ => r.coeff (kap i)) hq0`. Simplify using `only [hq, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', Polynomial.coeff_C_mul_X_pow, if_neg (not_le.mpr hlt), if_pos rfl, Polynomial.coeff_zero, zero_sub, neg_eq_zero] at hco`. Simplify using `at hco`. Break down `hco with h | h` into its components or cases. Conclude with `hc h`.

It suffices to derive a contradiction. Rewrite `h` using `[← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow, Polynomial.coeff_C_zero]`. Conclude with `pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h`.
-/
theorem eps_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) f ν)
    (hrow : ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (hR : RInvA (fun x => eval x f)) (hC : lhwline_CInv (fun x => eval x f))
    (hc : coeff (mStarA kap ν) f ≠ 0) (i i' : Fin n) (hii : i'.val = i.val + 1)
    (hle : kap i' ≤ ν (Fin.castSucc i')) : ν (Fin.castSucc i') ≤ kap i := by
  by_contra hlt
  push Not at hlt
  have hne : i ≠ i' := by
    intro e
    rw [e] at hii
    omega
  have hlt' : Fin.castSucc i < Fin.castSucc i' := by
    rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def]
    omega
  set νp := ν (Fin.castSucc i') with hνp
  let dv : ℂ → Fin n → ℂ := fun e a => if a = i then e else if a = i' then -1 / e else 1
  let zz : ℂ → Fin (n + 1) → ℂ := fun e s => if s = Fin.castSucc i' then -1 / e else 1
  let Y : Fin (n + 1) × Fin (n + 1) → Polynomial ℂ := fun v =>
    Fin.lastCases (if v.2 = Fin.castSucc i' then 0 else 1)
      (fun a => Fin.lastCases 0 (fun k => if a = i then (if k = i then Polynomial.X else if k = i' then 1 else 0)
        else if a = i' then (if k = i then 1 else 0) else (if k = a then 1 else 0)) v.2) v.1
  have hpt : ∀ e : ℂ, e ≠ 0 → (fun v => (Y v).eval e) =
      lhwline_rowOp (Fin.castSucc i) (Fin.castSucc i') (1 / e)
        (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e))) := by
    intro e he
    funext v
    obtain ⟨ρ, s⟩ := v
    induction ρ using Fin.lastCases with
    | last =>
      induction s using Fin.lastCases with
      | last =>
        simp [Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, (Fin.castSucc_lt_last i').ne',
          (Fin.castSucc_lt_last i).ne']
      | cast k =>
        simp only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, Fin.lastCases_castSucc, Fin.lastCases_last,
          Fin.castSucc_inj, (Fin.castSucc_lt_last i').ne', if_false]
        by_cases hk : k = i'
        · subst hk
          simp [hne]
          ring
        · simp [hk]
    | cast a =>
      induction s using Fin.lastCases with
      | last =>
        simp [Y, lhwline_rowOp, lhwline_colOp, mkPtA, (Fin.castSucc_lt_last i').ne']
      | cast k =>
        simp only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, dv, Fin.lastCases_castSucc, Fin.lastCases_last,
          Fin.castSucc_inj]
        by_cases ha : a = i
        · subst ha
          have hai : a ≠ i' := hne
          by_cases hk : k = a
          · subst hk
            simp [hai]
          · by_cases hk' : k = i'
            · subst hk'
              simp [hai, hk, Ne.symm hai, hne, Ne.symm hne]
              field_simp
            · simp [hai, hk, hk']
        · by_cases ha' : a = i'
          · subst ha'
            by_cases hk : k = i
            · subst hk
              simp [ha, hne, Ne.symm hne]
              field_simp
            · by_cases hk' : k = a
              · subst hk'
                simp [ha, hk, hne, Ne.symm hne]
                field_simp
                ring
              · simp [ha, hk, hk', Ne.symm hk']
          · by_cases hk : k = i
            · subst hk
              simp [ha, ha', Ne.symm ha, hne, Ne.symm hne]
            · by_cases hk' : k = i'
              · subst hk'
                simp [ha, ha', hk, Ne.symm ha', Ne.symm ha]
              · by_cases hka : k = a <;> simp [ha, ha', hk, hk', hka, Ne.symm ha, Ne.symm ha']
  have hval : ∀ e : ℂ, e ≠ 0 →
      (aeval Y f).eval e = coeff (mStarA kap ν) f * (e ^ kap i * (-1 / e) ^ νp) := by
    intro e he
    have e1 := hR (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e)))
      (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt' (by simp)
    have e2 := hC (mkPtA (dv e) (zz e)) (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt'
    simp only at e1 e2
    rw [eval_aeval_poly_A, hpt e he, e1, e2, eval_D_A kap ν f hcol hrow _ (mkPtA_D _ _), prod_mkPtA]
    congr 1
    have h1 : ∏ a, dv e a ^ kap a = e ^ kap i * (-1 / e) ^ kap i' := by
      have : ∀ a, dv e a ^ kap a =
          (if a = i then e ^ kap i else 1) * (if a = i' then (-1 / e) ^ kap i' else 1) := by
        intro a
        by_cases h1 : a = i
        · subst h1
          simp [dv, hne]
        · by_cases h2 : a = i'
          · subst h2
            simp [dv, h1]
          · simp [dv, h1, h2]
      rw [Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_ite_eq',
        Finset.prod_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
    have h2 : ∏ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) = (-1 / e) ^ (νp - kap i') := by
      have : ∀ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) =
          if k = i' then (-1 / e) ^ (νp - kap i') else 1 := by
        intro k
        by_cases hk : k = i'
        · subst hk
          simp [zz, hνp]
        · simp [zz, hk]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
    have h3 : zz e (Fin.last n) = 1 := by
      simp [zz, (Fin.castSucc_lt_last i').ne']
    rw [h1, h2, h3, one_pow, mul_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  set p := aeval Y f with hp
  set q : Polynomial ℂ := p * Polynomial.X ^ νp -
    Polynomial.C (coeff (mStarA kap ν) f * (-1) ^ νp) * Polynomial.X ^ (kap i) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro e he
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at he
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hq, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hval e he]
    rw [div_pow]
    field_simp
    ring
  have hco := congrArg (fun r : Polynomial ℂ => r.coeff (kap i)) hq0
  simp only [hq, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', Polynomial.coeff_C_mul_X_pow,
    if_neg (not_le.mpr hlt), if_pos rfl, Polynomial.coeff_zero, zero_sub, neg_eq_zero] at hco
  simp at hco
  rcases hco with h | h
  · exact hc h
  · exfalso
    rw [← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow, Polynomial.coeff_C_zero] at h
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h

/- English proof (translation)
Introduce `n N h lam mu f₁ f₂ hf₁ hf₂ hx₁ hx₂ hne`. Substitute `h` using the available equality. Take `⟨hcol₁, hR₁, hC₁, hrow₁⟩` from `props_A lam mu f₁ hf₁ hx₁`. Take `⟨hcol₂, hR₂, hC₂, hrow₂⟩` from `props_A lam mu f₂ hf₂ hx₂`. Establish `hc₂ : coeff (mStarA (kapA lam mu) lam.natW) f₂ ≠ 0`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Conclude with `vanishA f₂ hR₂ hC₂ (fun D hD => by`. Rewrite using `[eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, h0, zero_mul])`. Use `⟨⟨coeff (mStarA (kapA lam mu) lam.natW) f₁ / coeff (mStarA (kapA lam mu) lam.natW) f₂, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `set c := coeff (mStarA (kapA lam mu) lam.natW) f₁ / coeff (mStarA (kapA lam mu) lam.natW) f₂ with hcdef`. Establish `hg : f₁ - c • f₂ = 0`. Apply `vanishA` to reduce the goal to its premises. Introduce `x a b t hab hb`. Establish `e1` using `hR₁ x a b t hab hb`.

Establish `e2` using `hR₂ x a b t hab hb`. Simplify using `only at e1 e2`. Simplify using `only [map_sub, smul_eval, e1, e2]`. Introduce `x l j c' hlj`. Establish `e1` using `hC₁ x l j c' hlj`.

Establish `e2` using `hC₂ x l j c' hlj`. Simplify using `only at e1 e2`. Simplify using `only [map_sub, smul_eval, e1, e2]`. Introduce `D hD`. Rewrite using `[map_sub, smul_eval, eval_D_A (kapA lam mu) lam.natW f₁ hcol₁ hrow₁ D hD, eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, hcdef]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.mp hg`. Establish `hmS : mStarA (kapA lam mu) lam.natW ∈ f₂.support` using `mem_support_iff.mpr hc₂`. Establish `hmu : ∀ a : Fin n, ((kapA lam mu a : ℕ) : ℤ) + lam.detShift = mu.w a`.

Introduce `a`. Establish `hrd` using `fixed_rowDeg_A lam mu f₂ hx₂ _ hmS a`. Establish `hsum : ∑ s, mStarA (kapA lam mu) lam.natW (Fin.castSucc a, s) = kapA lam mu a`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using the standard rewrite rules.

Rewrite `hrd` using `[hsum]`. Conclude with `hrd`. Establish `hleA : ∀ a : Fin n, kapA lam mu a ≤ lam.natW (Fin.castSucc a)`. Introduce `a`. Establish `hcs : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) = lam.natW (Fin.castSucc a)`.

Rewrite using `[← lhwline_weight_col, hcol₂ hc₂]`. Establish `hcs2 : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) = kapA lam mu a + (lam.natW (Fin.castSucc a) - kapA lam mu a)`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[Finset.sum_ite_eq']`. Use linear arithmetic over natural numbers and integers.

Introduce `i`. Establish `hcast : (⟨i.1, by omega⟩ : Fin (n + 1)) = Fin.castSucc i` using `Fin.ext rfl`. Establish `hnat` using `natW_add_A lam (Fin.castSucc i)`. Establish `h1` using `hmu i`. Establish `h2` using `hleA i`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[hcast]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hi : i.val + 1 < n`. Establish `hcast' : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨i.val + 1, hi⟩` using `Fin.ext rfl`.

Establish `h3` using `eps_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ hR₂ hC₂ hc₂ i ⟨i.val + 1, hi⟩ rfl (hleA ⟨i.val + 1, hi⟩)`. Establish `hnat'` using `natW_add_A lam (Fin.castSucc ⟨i.val + 1, hi⟩)`. Rewrite using `[hcast']`. Use linear arithmetic over natural numbers and integers. Establish `hlast : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n` using `Fin.ext (by simp; omega)`.

Establish `hds : lam.w (Fin.last n) = lam.detShift`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (by omega)]`. Use `congr 1`. Rewrite using `[hlast, hds]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem fixedLine_proof_A : FixedLine := by
  intro n N h lam mu f₁ f₂ hf₁ hf₂ hx₁ hx₂ hne
  subst h
  obtain ⟨hcol₁, hR₁, hC₁, hrow₁⟩ := props_A lam mu f₁ hf₁ hx₁
  obtain ⟨hcol₂, hR₂, hC₂, hrow₂⟩ := props_A lam mu f₂ hf₂ hx₂
  have hc₂ : coeff (mStarA (kapA lam mu) lam.natW) f₂ ≠ 0 := by
    intro h0
    apply hne
    exact vanishA f₂ hR₂ hC₂ (fun D hD => by
      rw [eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, h0, zero_mul])
  refine ⟨⟨coeff (mStarA (kapA lam mu) lam.natW) f₁ / coeff (mStarA (kapA lam mu) lam.natW) f₂, ?_⟩, ?_⟩
  · set c := coeff (mStarA (kapA lam mu) lam.natW) f₁ / coeff (mStarA (kapA lam mu) lam.natW) f₂ with hcdef
    have hg : f₁ - c • f₂ = 0 := by
      apply vanishA
      · intro x a b t hab hb
        have e1 := hR₁ x a b t hab hb
        have e2 := hR₂ x a b t hab hb
        simp only at e1 e2
        simp only [map_sub, smul_eval, e1, e2]
      · intro x l j c' hlj
        have e1 := hC₁ x l j c' hlj
        have e2 := hC₂ x l j c' hlj
        simp only at e1 e2
        simp only [map_sub, smul_eval, e1, e2]
      · intro D hD
        rw [map_sub, smul_eval, eval_D_A (kapA lam mu) lam.natW f₁ hcol₁ hrow₁ D hD,
          eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, hcdef]
        field_simp
        ring
    exact sub_eq_zero.mp hg
  · have hmS : mStarA (kapA lam mu) lam.natW ∈ f₂.support := mem_support_iff.mpr hc₂
    have hmu : ∀ a : Fin n, ((kapA lam mu a : ℕ) : ℤ) + lam.detShift = mu.w a := by
      intro a
      have hrd := fixed_rowDeg_A lam mu f₂ hx₂ _ hmS a
      have hsum : ∑ s, mStarA (kapA lam mu) lam.natW (Fin.castSucc a, s) = kapA lam mu a := by
        rw [Fin.sum_univ_castSucc]
        simp
      rw [hsum] at hrd
      exact hrd
    have hleA : ∀ a : Fin n, kapA lam mu a ≤ lam.natW (Fin.castSucc a) := by
      intro a
      have hcs : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) = lam.natW (Fin.castSucc a) := by
        rw [← lhwline_weight_col, hcol₂ hc₂]
      have hcs2 : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) =
          kapA lam mu a + (lam.natW (Fin.castSucc a) - kapA lam mu a) := by
        rw [Fin.sum_univ_castSucc]
        simp [Finset.sum_ite_eq']
      omega
    intro i
    have hcast : (⟨i.1, by omega⟩ : Fin (n + 1)) = Fin.castSucc i := Fin.ext rfl
    have hnat := natW_add_A lam (Fin.castSucc i)
    have h1 := hmu i
    have h2 := hleA i
    constructor
    · rw [hcast]
      omega
    · by_cases hi : i.val + 1 < n
      · have hcast' : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨i.val + 1, hi⟩ := Fin.ext rfl
        have h3 := eps_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ hR₂ hC₂ hc₂ i ⟨i.val + 1, hi⟩ rfl
          (hleA ⟨i.val + 1, hi⟩)
        have hnat' := natW_add_A lam (Fin.castSucc ⟨i.val + 1, hi⟩)
        rw [hcast']
        omega
      · have hlast : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
        have hds : lam.w (Fin.last n) = lam.detShift := by
          unfold DomWeight.detShift
          rw [dif_pos (by omega)]
          congr 1
        rw [hlast, hds]
        omega

end PI.WGB
