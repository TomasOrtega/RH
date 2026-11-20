import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OmEDiagMonomial

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.Core

open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp`. Establish `hc : ∀ a b : σ, pderiv a (pderiv b (X n : MvPolynomial σ ℂ)) = 0`.

Introduce `a b`. Rewrite using `[pderiv_X, Pi.single_apply]`. Use `split_ifs`. Conclude with `Derivation.map_one_eq_zero _`. Conclude with `map_zero _`.

Simplify using `only [Derivation.leibniz, map_add, smul_eq_mul]`. Rewrite using `[hc i j, hc j i, hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pd_comm {σ : Type*} (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    have hc : ∀ a b : σ, pderiv a (pderiv b (X n : MvPolynomial σ ℂ)) = 0 := by
      intro a b
      rw [pderiv_X, Pi.single_apply]
      split_ifs
      · exact Derivation.map_one_eq_zero _
      · exact map_zero _
    simp only [Derivation.leibniz, map_add, smul_eq_mul]
    rw [hc i j, hc j i, hp]
    ring

/- English proof (translation)
Rewrite using `[fockInner_mul_X, pderiv_mul, pderiv_X_of_ne hne, zero_mul, zero_add, fockInner_X_mul, pd_comm ad ac]`.
-/
theorem key {σ : Type*} (v : MvPolynomial σ ℂ) (ac ad bc bd : σ) (hne : bc ≠ ad) :
    fockInner (pderiv ac (pderiv ad v)) (pderiv bc (pderiv bd v)) =
      fockInner (X bc * pderiv ac v) (X ad * pderiv bd v) := by
  rw [fockInner_mul_X, pderiv_mul, pderiv_X_of_ne hne, zero_mul, zero_add, fockInner_X_mul,
    pd_comm ad ac]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨hi, hj⟩` from `hcon`. Establish `hsplit : α = (α - Finsupp.single i 1 - Finsupp.single j 1) + Finsupp.single i 1 + Finsupp.single j 1`. Use extensionality with `k`.

Rewrite using `[Finsupp.add_apply, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> (try subst_vars) <;> first | omega | exact (hij rfl).elim`. Take `⟨m, hm⟩ : ∃ m, α = m + Finsupp.single i 1 + Finsupp.single j 1` from `⟨_, hsplit⟩`. Establish `hc` using `congrArg (coeff m) h`. Rewrite `hc` using `[coeff_pderiv, coeff_pderiv, coeff_zero, ← hm]`.

Break down `mul_eq_zero.1 hc with h' | h'` into its components or cases. Break down `mul_eq_zero.1 h' with h'' | h''` into its components or cases. Conclude with `hα h''`. Conclude with `Nat.cast_add_one_ne_zero _ h''`. Conclude with `Nat.cast_add_one_ne_zero _ h'`.
-/
theorem coeff_zero_of_dd {σ : Type*} (v : MvPolynomial σ ℂ) (i j : σ) (hij : i ≠ j)
    (h : pderiv i (pderiv j v) = 0) (α : σ →₀ ℕ) (hα : coeff α v ≠ 0) :
    α i = 0 ∨ α j = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hi, hj⟩ := hcon
  have hsplit : α = (α - Finsupp.single i 1 - Finsupp.single j 1) + Finsupp.single i 1 +
      Finsupp.single j 1 := by
    ext k
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.tsub_apply,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h1 h2 h2 <;> (try subst_vars) <;> first | omega | exact (hij rfl).elim
  obtain ⟨m, hm⟩ : ∃ m, α = m + Finsupp.single i 1 + Finsupp.single j 1 := ⟨_, hsplit⟩
  have hc := congrArg (coeff m) h
  rw [coeff_pderiv, coeff_pderiv, coeff_zero, ← hm] at hc
  rcases mul_eq_zero.1 hc with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact hα h''
    · exact Nat.cast_add_one_ne_zero _ h''
  · exact Nat.cast_add_one_ne_zero _ h'

variable {p q r s : ℕ}

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases c with j | j <;> simp [linePos]`.
-/
theorem side_lp (a : Ix p q) (c : Ix r s) :
    linePos ((a, c) : Ln p q r s) = true ↔ a.isLeft = c.isLeft := by
  rcases a with i | i <;> rcases c with j | j <;> simp [linePos]

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp [sameBlock]`.
-/
theorem side_sb {m n : ℕ} (a b : Ix m n) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  rcases a with i | i <;> rcases b with j | j <;> simp [sameBlock]

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp_all [posC, sameBlock]`.
-/
theorem posC_sb {m n : ℕ} (a b : Ix m n) (h : posC a b) : sameBlock a b := by
  rcases a with i | i <;> rcases b with j | j <;> simp_all [posC, sameBlock]

/- English proof (translation)
Introduce and unpack `rfl`. Apply the tactic sequence `rcases a with i | i <;> simp_all [posC]`.
-/
theorem posC_ne {m n : ℕ} (a b : Ix m n) (h : posC a b) : a ≠ b := by
  rintro rfl
  rcases a with i | i <;> simp_all [posC]

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp_all [posC, sameBlock]`.
-/
theorem posC_or {m n : ℕ} (a b : Ix m n) (h : sameBlock a b) (hne : a ≠ b) :
    posC a b ∨ posC b a := by
  rcases a with i | i <;> rcases b with j | j <;> simp_all [posC, sameBlock]

def gg (v : Pol p q r s) (a : Ix p q) (c d : Ix r s) : Pol p q r s :=
  if (¬ sameBlock c d) ∧ linePos ((a, d) : Ln p q r s) = true then
    pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) v) else 0

def SS (v : Pol p q r s) (a b : Ix p q) : ℂ :=
  ∑ c : Ix r s, ∑ d : Ix r s, fockInner (gg v a c d) (gg v b c d)

/- English proof (translation)
Distinguish the cases in `h : sameBlock c d`. Conclude with `Finset.sum_eq_zero fun a _ => by simp [gg, h]`. Rewrite using `[← hH c d h, lowOp, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : linePos ((a, d) : Ln p q r s) = true`.

Simplify using `[gg, h, hl]`. Simplify using `[gg, h, hl]`.
-/
theorem sum_gg (v : Pol p q r s)
    (hH : ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d v = 0) (c d : Ix r s) :
    ∑ a : Ix p q, gg v a c d = 0 := by
  by_cases h : sameBlock c d
  · exact Finset.sum_eq_zero fun a _ => by simp [gg, h]
  · rw [← hH c d h, lowOp, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hl : linePos ((a, d) : Ln p q r s) = true
    · simp [gg, h, hl]
    · simp [gg, h, hl]

/- English proof (translation)
Set `F : Ix p q → Ix p q → Ix r s → Ix r s → ℂ` to `fun a b c d => fockInner (gg v a c d) (gg v b c d)`. Establish `h0 : ∑ c : Ix r s, ∑ d : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q, F a b c d = 0`. Use `Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Establish `e : ∑ a : Ix p q, ∑ b : Ix p q, F a b c d = fockInner (∑ a : Ix p q, gg v a c d) (∑ b : Ix p q, gg v b c d)`. Rewrite using `[fockInner_sum_left]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[fockInner_sum_right]`. Rewrite using `[e, sum_gg v hH c d, fockInner_zero_left]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_SS (v : Pol p q r s)
    (hH : ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d v = 0) :
    ∑ a : Ix p q, ∑ b : Ix p q, SS v a b = 0 := by
  let F : Ix p q → Ix p q → Ix r s → Ix r s → ℂ :=
    fun a b c d => fockInner (gg v a c d) (gg v b c d)
  have h0 : ∑ c : Ix r s, ∑ d : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q, F a b c d = 0 := by
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    have e : ∑ a : Ix p q, ∑ b : Ix p q, F a b c d =
        fockInner (∑ a : Ix p q, gg v a c d) (∑ b : Ix p q, gg v b c d) := by
      rw [fockInner_sum_left]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [fockInner_sum_right]
    rw [e, sum_gg v hH c d, fockInner_zero_left]
  calc ∑ a : Ix p q, ∑ b : Ix p q, SS v a b
      = ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s, ∑ d : Ix r s, F a b c d := rfl
    _ = ∑ a : Ix p q, ∑ c : Ix r s, ∑ b : Ix p q, ∑ d : Ix r s, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q, ∑ d : Ix r s, F a b c d := Finset.sum_comm
    _ = ∑ c : Ix r s, ∑ a : Ix p q, ∑ d : Ix r s, ∑ b : Ix p q, F a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : Ix r s, ∑ d : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q, F a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = 0 := h0

/- English proof (translation)
Unfold `SS`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Conclude with `fockInner_swap _ _`.
-/
theorem SS_swap (v : Pol p q r s) (a b : Ix p q) : SS v a b = starRingEnd ℂ (SS v b a) := by
  unfold SS
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  exact fockInner_swap _ _

/- English proof (translation)
Unfold `SS`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_sum]`.
-/
theorem SS_self_re (v : Pol p q r s) (a : Ix p q) :
    (SS v a a).re = ∑ c : Ix r s, ∑ d : Ix r s, (fockInner (gg v a c d) (gg v a c d)).re := by
  unfold SS
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_sum]

/- English proof (translation)
Rewrite using `[SS_self_re]`. Conclude with `Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => fockInner_self_re_nonneg _`.
-/
theorem SS_self_nonneg (v : Pol p q r s) (a : Ix p q) : 0 ≤ (SS v a a).re := by
  rw [SS_self_re]
  exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => fockInner_self_re_nonneg _

/- English proof (translation)
Use `Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Unfold `gg`. Distinguish the cases in `h1 : (¬ sameBlock c d) ∧ linePos ((a, d) : Ln p q r s) = true`. Distinguish the cases in `h2 : (¬ sameBlock c d) ∧ linePos ((b, d) : Ln p q r s) = true`. It suffices to derive a contradiction.

Apply `h` to reduce the goal to its premises. Rewrite using `[side_sb]`. Rewrite using `[(side_lp a d).1 h1.2, (side_lp b d).1 h2.2]`. Rewrite using `[if_neg h2, fockInner_zero_right]`. Rewrite using `[if_neg h1, fockInner_zero_left]`.
-/
theorem SS_offblock (v : Pol p q r s) (a b : Ix p q) (h : ¬ sameBlock a b) : SS v a b = 0 := by
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  unfold gg
  by_cases h1 : (¬ sameBlock c d) ∧ linePos ((a, d) : Ln p q r s) = true
  · by_cases h2 : (¬ sameBlock c d) ∧ linePos ((b, d) : Ln p q r s) = true
    · exfalso
      apply h
      rw [side_sb]
      rw [(side_lp a d).1 h1.2, (side_lp b d).1 h2.2]
    · rw [if_neg h2, fockInner_zero_right]
  · rw [if_neg h1, fockInner_zero_left]

/- English proof (translation)
Unfold `negOp`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : linePos ((b, c) : Ln p q r s) = true`. Simplify using `[hl]`.

Simplify using `[hl]`.
-/
theorem negOp_apply (v : Pol p q r s) (b a : Ix p q) :
    negOp b a v = ∑ c : Ix r s, (if linePos ((b, c) : Ln p q r s) = true then 0
      else X ((b, c) : Ln p q r s) * pderiv ((a, c) : Ln p q r s) v) := by
  unfold negOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hl : linePos ((b, c) : Ln p q r s) = true
  · simp [hl]
  · simp [hl]

/- English proof (translation)
Unfold `posOp`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : linePos ((a, d) : Ln p q r s) = true`. Simplify using `[hl]`.

Simplify using `[hl]`.
-/
theorem posOp_apply (v : Pol p q r s) (a b : Ix p q) :
    posOp a b v = ∑ d : Ix r s, (if linePos ((a, d) : Ln p q r s) = true then
      X ((a, d) : Ln p q r s) * pderiv ((b, d) : Ln p q r s) v else 0) := by
  unfold posOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hl : linePos ((a, d) : Ln p q r s) = true
  · simp [hl]
  · simp [hl]

/- English proof (translation)
Establish `hs : a.isLeft = b.isLeft` using `(side_sb a b).1 hab`. Rewrite using `[negOp_apply, posOp_apply, fockInner_sum_left]`. Unfold `SS`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[fockInner_sum_right]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Unfold `gg`. Distinguish the cases in `hD : linePos ((a, d) : Ln p q r s) = true`. Establish `hD' : linePos ((b, d) : Ln p q r s) = true`. Rewrite `hD`, the goal using `[side_lp]`.

Rewrite using `[← hs]`. Conclude with `hD`. Distinguish the cases in `hcd : sameBlock c d`. Establish `hbc : linePos ((b, c) : Ln p q r s) = true`. Rewrite using `[side_lp, ← hs, (side_lp a d).1 hD]`.

Conclude with `((side_sb c d).1 hcd).symm`. Rewrite using `[if_neg (fun h => h.1 hcd), if_pos hbc, fockInner_zero_left, fockInner_zero_left]`. Establish `hbc : ¬ linePos ((b, c) : Ln p q r s) = true`. Introduce `h`. Apply `hcd` to reduce the goal to its premises.

Rewrite using `[side_sb, ← (side_lp b c).1 h, ← hs]`. Conclude with `(side_lp a d).1 hD`. Rewrite using `[if_pos ⟨hcd, hD⟩, if_pos ⟨hcd, hD'⟩, if_neg hbc, if_pos hD]`. Apply `key` to reduce the goal to its premises. Introduce `h`.

Apply `hcd` to reduce the goal to its premises. Establish `: c = d` using `(Prod.mk.inj h).2`. Substitute `this` using the available equality. Conclude with `(side_sb c c).2 rfl`. Rewrite using `[if_neg (fun h => hD h.2), if_neg hD, fockInner_zero_left, fockInner_zero_right]`.
-/
theorem SS_eq (v : Pol p q r s) (a b : Ix p q) (hab : sameBlock a b) :
    SS v a b = fockInner (negOp b a v) (posOp a b v) := by
  have hs : a.isLeft = b.isLeft := (side_sb a b).1 hab
  rw [negOp_apply, posOp_apply, fockInner_sum_left]
  unfold SS
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fockInner_sum_right]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold gg
  by_cases hD : linePos ((a, d) : Ln p q r s) = true
  · have hD' : linePos ((b, d) : Ln p q r s) = true := by
      rw [side_lp] at hD ⊢; rw [← hs]; exact hD
    by_cases hcd : sameBlock c d
    · have hbc : linePos ((b, c) : Ln p q r s) = true := by
        rw [side_lp, ← hs, (side_lp a d).1 hD]
        exact ((side_sb c d).1 hcd).symm
      rw [if_neg (fun h => h.1 hcd), if_pos hbc, fockInner_zero_left, fockInner_zero_left]
    · have hbc : ¬ linePos ((b, c) : Ln p q r s) = true := by
        intro h
        apply hcd
        rw [side_sb, ← (side_lp b c).1 h, ← hs]
        exact (side_lp a d).1 hD
      rw [if_pos ⟨hcd, hD⟩, if_pos ⟨hcd, hD'⟩, if_neg hbc, if_pos hD]
      apply key
      intro h
      apply hcd
      have : c = d := (Prod.mk.inj h).2
      subst this
      exact (side_sb c c).2 rfl
  · rw [if_neg (fun h => hD h.2), if_neg hD, fockInner_zero_left, fockInner_zero_right]

/- English proof (translation)
Establish `hker : fockAct1 p q r s (Eab a b) v = 0`. Establish `h2` using `hv.2`. Simplify using `only [hwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h2`. Conclude with `h2.2 a b h`. Rewrite `hker` using `[hK p q r s a b (posC_sb a b h), if_neg (posC_ne a b h), add_zero, LinearMap.sub_apply, sub_eq_zero]`.

Conclude with `hker`.
-/
theorem hw_eq (hK : OpsK) (μ : Ix p q → ℚ) (v : Pol p q r s)
    (hv : IsHW (fockAct1 p q r s) μ v) (a b : Ix p q) (h : posC a b) :
    posOp a b v = negOp b a v := by
  have hker : fockAct1 p q r s (Eab a b) v = 0 := by
    have h2 := hv.2
    simp only [hwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h2
    exact h2.2 a b h
  rw [hK p q r s a b (posC_sb a b h), if_neg (posC_ne a b h), add_zero, LinearMap.sub_apply,
    sub_eq_zero] at hker
  exact hker

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Conclude with `SS_self_nonneg v a`. Distinguish the cases in `hsb : sameBlock a b`. Break down `posC_or a b hsb hab with h | h` into its components or cases.

Rewrite using `[SS_eq v a b hsb, hw_eq hK μ v hv a b h]`. Conclude with `fockInner_self_re_nonneg _`. Rewrite using `[SS_swap, Complex.conj_re, SS_eq v b a ((side_sb b a).2 ((side_sb a b).1 hsb).symm), hw_eq hK μ v hv b a h]`. Conclude with `fockInner_self_re_nonneg _`. Rewrite using `[SS_offblock v a b hsb]`.

Simplify using the standard rewrite rules.
-/
theorem SS_nonneg (hK : OpsK) (μ : Ix p q → ℚ) (v : Pol p q r s)
    (hv : IsHW (fockAct1 p q r s) μ v) (a b : Ix p q) : 0 ≤ (SS v a b).re := by
  by_cases hab : a = b
  · subst hab; exact SS_self_nonneg v a
  by_cases hsb : sameBlock a b
  · rcases posC_or a b hsb hab with h | h
    · rw [SS_eq v a b hsb, hw_eq hK μ v hv a b h]
      exact fockInner_self_re_nonneg _
    · rw [SS_swap, Complex.conj_re, SS_eq v b a ((side_sb b a).2 ((side_sb a b).1 hsb).symm),
        hw_eq hK μ v hv b a h]
      exact fockInner_self_re_nonneg _
  · rw [SS_offblock v a b hsb]; simp

/- English proof (translation)
Establish `hH` using `(hL p q r s v).1 hh`. Establish `hsum` using `sum_SS v hH`. Establish `hre : ∑ a : Ix p q, ∑ b : Ix p q, (SS v a b).re = 0`. Use `congrArg Complex.re hsum` as an intermediate fact. Rewrite `this` using `[Complex.re_sum]`.

Simplify `this` using `[Complex.re_sum]`. Establish `hrow` using `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => SS_nonneg hK μ v hv a b)).1 hre a (Finset.mem_univ _)`. Establish `haa` using `(Finset.sum_eq_zero_iff_of_nonneg (fun b _ => SS_nonneg hK μ v hv a b)).1 hrow a (Finset.mem_univ _)`. Rewrite `haa` using `[SS_self_re]`. Establish `hc1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Finset.sum_nonneg fun d _ => fockInner_self_re_nonneg (gg v a c d))).1 haa c (Finset.mem_univ _)`.

Establish `hcd` using `(Finset.sum_eq_zero_iff_of_nonneg (fun d _ => fockInner_self_re_nonneg (gg v a c d))).1 hc1 d (Finset.mem_univ _)`. Establish `hg` using `eq_zero_of_fockInner_self_re _ hcd`. Establish `hnsb : ¬ sameBlock c d`. Introduce `h`. Rewrite `h` using `[side_sb]`.

Establish `h1` using `(side_lp a d).1 hd`. Establish `h2 : ¬ linePos ((a, c) : Ln p q r s) = true` using `by rw [hc]; simp`. Conclude with `h2 ((side_lp a c).2 (h1.trans h.symm))`. Unfold `gg at hg`. Rewrite `hg` using `[if_pos ⟨hnsb, hd⟩]`. Then use the resulting hypothesis.
-/
theorem core (hK : OpsK) (hL : HarmIff) (μ : Ix p q → ℚ) (v : Pol p q r s)
    (hv : IsHW (fockAct1 p q r s) μ v) (hh : Harm2 v) (a : Ix p q) (c d : Ix r s)
    (hc : linePos ((a, c) : Ln p q r s) = false) (hd : linePos ((a, d) : Ln p q r s) = true) :
    pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) v) = 0 := by
  have hH := (hL p q r s v).1 hh
  have hsum := sum_SS v hH
  have hre : ∑ a : Ix p q, ∑ b : Ix p q, (SS v a b).re = 0 := by
    have := congrArg Complex.re hsum
    rw [Complex.re_sum] at this
    simpa [Complex.re_sum] using this
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    Finset.sum_nonneg fun b _ => SS_nonneg hK μ v hv a b)).1 hre a (Finset.mem_univ _)
  have haa := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => SS_nonneg hK μ v hv a b)).1 hrow a
    (Finset.mem_univ _)
  rw [SS_self_re] at haa
  have hc1 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Finset.sum_nonneg fun d _ =>
    fockInner_self_re_nonneg (gg v a c d))).1 haa c (Finset.mem_univ _)
  have hcd := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ =>
    fockInner_self_re_nonneg (gg v a c d))).1 hc1 d (Finset.mem_univ _)
  have hg := eq_zero_of_fockInner_self_re _ hcd
  have hnsb : ¬ sameBlock c d := by
    intro h
    rw [side_sb] at h
    have h1 := (side_lp a d).1 hd
    have h2 : ¬ linePos ((a, c) : Ln p q r s) = true := by rw [hc]; simp
    exact h2 ((side_lp a c).2 (h1.trans h.symm))
  unfold gg at hg
  rwa [if_pos ⟨hnsb, hd⟩] at hg

/- English proof (translation)
Take `⟨α, hα⟩` from `MvPolynomial.exists_coeff_ne_zero h0`. Use `⟨α, hα, ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `hh : P.IsHomogeneous d` using `hP`. Assume the negation of the conclusion as `hne`. Conclude with `hα (hh.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum]))`.

Establish `h1` using `congrArg (MvPolynomial.coeff α) (hw a)`. Rewrite `h1` using `[LinearMap.sub_apply, MvPolynomial.coeff_sub, coeff_of_diag (T a) (fun β => ((f a β : ℚ) : ℂ)) (hT a), LinearMap.smul_apply, LinearMap.id_apply, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero, smul_eq_mul, ← sub_mul]`. Establish `h2` using `(mul_eq_zero.1 h1).resolve_right hα`. Conclude with `(sub_eq_zero.1 h2).symm` after adjusting the coercions.
-/
theorem exists_monomial_weight' {σ ι : Type*} [Fintype σ]
    (T : ι → Module.End ℂ (MvPolynomial σ ℂ)) (f : ι → (σ →₀ ℕ) → ℚ)
    (hT : ∀ a β, T a (MvPolynomial.monomial β 1) =
      ((f a β : ℚ) : ℂ) • MvPolynomial.monomial β 1)
    (μ : ι → ℚ) (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P ∈ homog σ d) (h0 : P ≠ 0)
    (hw : ∀ a, (T a - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ (MvPolynomial σ ℂ))) P = 0) :
    ∃ α : σ →₀ ℕ, MvPolynomial.coeff α P ≠ 0 ∧ ∑ i, α i = d ∧ ∀ a, μ a = f a α := by
  obtain ⟨α, hα⟩ := MvPolynomial.exists_coeff_ne_zero h0
  refine ⟨α, hα, ?_, fun a => ?_⟩
  · have hh : P.IsHomogeneous d := hP
    by_contra hne
    exact hα (hh.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum]))
  · have h1 := congrArg (MvPolynomial.coeff α) (hw a)
    rw [LinearMap.sub_apply, MvPolynomial.coeff_sub,
      coeff_of_diag (T a) (fun β => ((f a β : ℚ) : ℂ)) (hT a),
      LinearMap.smul_apply, LinearMap.id_apply, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero,
      smul_eq_mul, ← sub_mul] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_right hα
    exact_mod_cast (sub_eq_zero.1 h2).symm

/- English proof (translation)
The claim follows from `|A - B| = A + B := by rcases h with rfl | rfl · simp [abs_of_nonneg hB] · simp [abs_of_nonneg hA]`.
-/
theorem abs_sub_of (A B : ℚ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A = 0 ∨ B = 0) :
    |A - B| = A + B := by
  rcases h with rfl | rfl
  · simp [abs_of_nonneg hB]
  · simp [abs_of_nonneg hA]

/- English proof (translation)
The claim follows from `|shiftNu (cPair r s) (fun b => W1 b α) a| = ∑ c : Ix r s, (α (a, c) : ℚ) := by rcases a with i | i · rw [Fintype.sum_sum_type] have hx : shiftNu (cPair r s) (fun b => W1 b α) (Sum.inl i) = (∑ c : Fin r, (α (Sum.inl i, Sum.inl c) : ℚ)) - ∑ c : Fin s, (α (Sum.inl i, Sum.inr c) : ℚ) …`.
-/
theorem shift_eq (α : Ln p q r s →₀ ℕ)
    (hrow : ∀ (a : Ix p q) (c d : Ix r s), linePos ((a, c) : Ln p q r s) = false →
      linePos ((a, d) : Ln p q r s) = true → α (a, c) = 0 ∨ α (a, d) = 0) (a : Ix p q) :
    |shiftNu (cPair r s) (fun b => W1 b α) a| = ∑ c : Ix r s, (α (a, c) : ℚ) := by
  rcases a with i | i
  · rw [Fintype.sum_sum_type]
    have hx : shiftNu (cPair r s) (fun b => W1 b α) (Sum.inl i) =
        (∑ c : Fin r, (α (Sum.inl i, Sum.inl c) : ℚ)) -
          ∑ c : Fin s, (α (Sum.inl i, Sum.inr c) : ℚ) := by
      simp [shiftNu, W1, cPair, Fintype.sum_sum_type, lw, linePos, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring
    rw [hx]
    apply abs_sub_of _ _ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    by_cases hA : ∀ c : Fin r, α (Sum.inl i, Sum.inl c) = 0
    · left; exact Finset.sum_eq_zero fun c _ => by simp [hA c]
    · right
      push_neg at hA
      obtain ⟨c0, hc0⟩ := hA
      refine Finset.sum_eq_zero fun d _ => ?_
      have := (hrow (Sum.inl i) (Sum.inr d) (Sum.inl c0) rfl rfl).resolve_right hc0
      simp [this]
  · rw [Fintype.sum_sum_type, add_comm]
    have hx : shiftNu (cPair r s) (fun b => W1 b α) (Sum.inr i) =
        (∑ c : Fin s, (α (Sum.inr i, Sum.inr c) : ℚ)) -
          ∑ c : Fin r, (α (Sum.inr i, Sum.inl c) : ℚ) := by
      simp [shiftNu, W1, cPair, Fintype.sum_sum_type, lw, linePos, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring
    rw [hx]
    apply abs_sub_of _ _ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    by_cases hA : ∀ c : Fin s, α (Sum.inr i, Sum.inr c) = 0
    · left; exact Finset.sum_eq_zero fun c _ => by simp [hA c]
    · right
      push_neg at hA
      obtain ⟨c0, hc0⟩ := hA
      refine Finset.sum_eq_zero fun d _ => ?_
      have := (hrow (Sum.inr i) (Sum.inl d) (Sum.inr c0) rfl rfl).resolve_right hc0
      simp [this]

/- English proof (translation)
Introduce `p q r s μ e v hv hHW hH`. Take `⟨h0, hw⟩` from `wt_of_isHW _ μ v hHW`. Take `⟨α, hα, hdeg, hμ⟩` from `exists_monomial_weight' (fun a => fockAct1 p q r s (Eab a a)) (fun a β => W1 a β) (fun a β => fockAct1_monomial p q r s a β) μ e v hv h0 hw`. Establish `hrow : ∀ (a : Ix p q) (c d : Ix r s), linePos ((a, c) : Ln p q r s) = false → linePos ((a, d) : Ln p q r s) = true → α (a, c) = 0 ∨ α (a, d) = 0`. Introduce `a c d h1 h2`.

Use `coeff_zero_of_dd v _ _ ?_ (core hK hL μ v hHW hH a c d h1 h2) α hα` and prove the remaining obligations. Introduce `h`. Rewrite `h1` using `[h]`. Rewrite `h2` using `[h1]`. Conclude with `Bool.false_ne_true h2`.

Establish `hμ' : μ = fun b => W1 b α` using `funext hμ`. Substitute `hμ'` using the available equality. Unfold `degW`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hwHarmDeg_of (hK : OpsK) (hL : HarmIff) : HwHarmDeg := by
  intro p q r s μ e v hv hHW hH
  obtain ⟨h0, hw⟩ := wt_of_isHW _ μ v hHW
  obtain ⟨α, hα, hdeg, hμ⟩ := exists_monomial_weight' (fun a => fockAct1 p q r s (Eab a a))
    (fun a β => W1 a β) (fun a β => fockAct1_monomial p q r s a β) μ e v hv h0 hw
  have hrow : ∀ (a : Ix p q) (c d : Ix r s), linePos ((a, c) : Ln p q r s) = false →
      linePos ((a, d) : Ln p q r s) = true → α (a, c) = 0 ∨ α (a, d) = 0 := by
    intro a c d h1 h2
    refine coeff_zero_of_dd v _ _ ?_ (core hK hL μ v hHW hH a c d h1 h2) α hα
    intro h
    rw [h] at h1
    rw [h1] at h2
    exact Bool.false_ne_true h2
  have hμ' : μ = fun b => W1 b α := funext hμ
  subst hμ'
  unfold degW
  calc (e : ℚ) = ∑ l : Ln p q r s, (α l : ℚ) := by rw [← hdeg, Nat.cast_sum]
    _ = ∑ a : Ix p q, ∑ c : Ix r s, (α (a, c) : ℚ) :=
        Fintype.sum_prod_type (fun l : Ln p q r s => (α l : ℚ))
    _ = _ := Finset.sum_congr rfl fun a _ => (shift_eq α hrow a).symm

end PI.FockOneDegW.Core
