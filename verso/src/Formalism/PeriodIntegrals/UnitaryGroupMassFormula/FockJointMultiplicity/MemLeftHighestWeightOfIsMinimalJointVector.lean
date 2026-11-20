import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMP

open PI.FJM

section Gen

variable {σ : Type*}

/- English proof (translation)
Use `MvPolynomial.induction_on' P (fun m a => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `h1 : monomial m a = a • monomial m (1 : ℂ)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1, map_smul, hT, smul_smul]`. Simplify using `only [coeff_smul, coeff_monomial, smul_eq_mul]`.

Distinguish the cases in `h : m = e`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, coeff_add, coeff_add, hp, hq, mul_add]`.
-/
theorem coeff_diag (T : Module.End ℂ (MvPolynomial σ ℂ)) (w : (σ →₀ ℕ) → ℂ)
    (hT : ∀ m, T (monomial m 1) = w m • monomial m 1) (P : MvPolynomial σ ℂ) (e : σ →₀ ℕ) :
    coeff e (T P) = w e * coeff e P := by
  classical
  refine MvPolynomial.induction_on' P (fun m a => ?_) (fun p q hp hq => ?_)
  · have h1 : monomial m a = a • monomial m (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, hT, smul_smul]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul]
    by_cases h : m = e
    · subst h
      rw [if_pos rfl]
      ring
    · rw [if_neg h]
      ring
  · rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/- English proof (translation)
Establish `h1` using `coeff_diag T w hT P e`. Rewrite `h1` using `[hP]`. Simplify using `only [coeff_smul, smul_eq_mul] at h1`. Conclude with `(mul_right_cancel₀ (mem_support_iff.mp he) h1).symm`.
-/
theorem eig_of_mem_support (T : Module.End ℂ (MvPolynomial σ ℂ)) (w : (σ →₀ ℕ) → ℂ)
    (hT : ∀ m, T (monomial m 1) = w m • monomial m 1) (P : MvPolynomial σ ℂ) (c : ℂ) (hP : T P = c • P)
    (e : σ →₀ ℕ) (he : e ∈ P.support) : w e = c := by
  have h1 := coeff_diag T w hT P e
  rw [hP] at h1
  simp only [coeff_smul, smul_eq_mul] at h1
  exact (mul_right_cancel₀ (mem_support_iff.mp he) h1).symm

def NoVar (P : MvPolynomial σ ℂ) (v : σ) : Prop := ∀ e ∈ P.support, e v = 0

/- English proof (translation)
Rewrite using `[P.as_sum, map_sum]`. Use `Finset.sum_eq_zero fun e he => ?_` and prove the remaining obligations. Rewrite using `[pderiv_monomial]`. Simplify using `[h e he]`.
-/
theorem pderiv_eq_zero_of_noVar {P : MvPolynomial σ ℂ} {v : σ} (h : NoVar P v) : pderiv v P = 0 := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [pderiv_monomial]
  simp [h e he]

/- English proof (translation)
Introduce `f hf`. Rewrite `hf` using `[P.as_sum, map_sum]`. Take `⟨e, he, hfe⟩` from `Finset.mem_biUnion.mp (support_sum hf)`. Rewrite `hfe` using `[pderiv_monomial]`. Take `rfl` from `Finset.mem_singleton.mp (support_monomial_subset hfe)`.

Simplify using `[h e he]`.
-/
theorem noVar_pderiv {P : MvPolynomial σ ℂ} {v : σ} (h : NoVar P v) (u : σ) : NoVar (pderiv u P) v := by
  classical
  intro f hf
  rw [P.as_sum, map_sum] at hf
  obtain ⟨e, he, hfe⟩ := Finset.mem_biUnion.mp (support_sum hf)
  rw [pderiv_monomial] at hfe
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hfe)
  simp [h e he]

/- English proof (translation)
Introduce `e he`. Assume the negation of the conclusion as `hev`. Establish `hc : coeff (e - Finsupp.single v 1) (pderiv v P) = coeff e P * (e v : ℂ)` using `by conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Simplify using `only [pderiv_monomial, coeff_monomial]`.

Rewrite using `[Finset.sum_eq_single e]`. Rewrite using `[if_pos rfl]`. Introduce `b _ hbe`. Distinguish the cases in `hbv : b v = 0`. Simplify using `[hbv]`.

Rewrite using `[if_neg]`. Introduce `hb`. Apply `hbe` to reduce the goal to its premises. Establish `h1 : Finsupp.single v 1 ≤ b` using `Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hbv)`. Establish `h2 : Finsupp.single v 1 ≤ e` using `Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hev)`.

Rewrite using `[← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, hb]`. Introduce `h'`. Conclude with `absurd he h'`. Rewrite `hc` using `[h, coeff_zero]`. Conclude with `mul_ne_zero (mem_support_iff.mp he) (Nat.cast_ne_zero.mpr hev) hc.symm`.
-/
theorem noVar_of_pderiv_eq_zero {P : MvPolynomial σ ℂ} {v : σ} (h : pderiv v P = 0) : NoVar P v := by
  classical
  intro e he
  by_contra hev
  have hc : coeff (e - Finsupp.single v 1) (pderiv v P) = coeff e P * (e v : ℂ) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, coeff_sum]
    simp only [pderiv_monomial, coeff_monomial]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl]
    · intro b _ hbe
      by_cases hbv : b v = 0
      · simp [hbv]
      · rw [if_neg]
        intro hb
        apply hbe
        have h1 : Finsupp.single v 1 ≤ b := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hbv)
        have h2 : Finsupp.single v 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hev)
        rw [← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, hb]
    · intro h'
      exact absurd he h'
  rw [h, coeff_zero] at hc
  exact mul_ne_zero (mem_support_iff.mp he) (Nat.cast_ne_zero.mpr hev) hc.symm

/- English proof (translation)
Take `⟨e, he⟩` from `Finset.nonempty_iff_ne_empty.mpr (fun h => hP (support_eq_empty.mp h))`. Conclude with `⟨e, he⟩`.
-/
theorem exists_mem_support {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : ∃ e, e ∈ P.support := by
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr (fun h => hP (support_eq_empty.mp h))
  exact ⟨e, he⟩

variable {κ : Type*} [Fintype κ]

def gR (u v : κ → σ) (pos : κ → Bool) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ c, if pos c = true then X (u c) * pderiv (v c) P else -(X (v c) * pderiv (u c) P)

def sw (e : σ →₀ ℕ) (w : κ → σ) (pos : κ → Bool) : ℤ :=
  ∑ c, if pos c = true then (e (w c) : ℤ) else -(e (w c) : ℤ)

/- English proof (translation)
Unfold `gR`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (pos c) with h | h <;> simp [h]`.
-/
theorem gR_swap (u v : κ → σ) (pos : κ → Bool) (P : MvPolynomial σ ℂ) :
    gR v u (fun c => !pos c) P = -gR u v pos P := by
  unfold gR
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases Bool.eq_false_or_eq_true (pos c) with h | h <;> simp [h]

/- English proof (translation)
Establish `hno0` using `hno c0 hc0`. Establish `key : ∀ a b, pderiv (u c0) (X a * pderiv b P) = pderiv b P * pderiv (u c0) (X a)`. Introduce `a b`. Rewrite using `[Derivation.leibniz, pderiv_eq_zero_of_noVar (noVar_pderiv hno0 b), smul_zero, zero_add, smul_eq_mul]`. Establish `h0 : pderiv (u c0) (gR u v pos P) = 0` using `by rw [hR, map_zero]`.

Unfold `gR at h0`. Rewrite `h0` using `[map_sum, Finset.sum_eq_single c0]`. Rewrite `h0` using `[if_pos hc0, key, pderiv_X_self, mul_one]`. Conclude with `h0`. Introduce `c _ hc split_ifs with hpc`.

Rewrite using `[key, pderiv_X_of_ne (fun h => hc (hu h)), mul_zero]`. Rewrite using `[map_neg, key, pderiv_X_of_ne (huv c0 c).symm, mul_zero, neg_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c0) h`.
-/
theorem gR_pos_lemma (u v : κ → σ) (pos : κ → Bool) (hu : Function.Injective u) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hno : ∀ c, pos c = true → NoVar P (u c))
    (c0 : κ) (hc0 : pos c0 = true) : pderiv (v c0) P = 0 := by
  have hno0 := hno c0 hc0
  have key : ∀ a b, pderiv (u c0) (X a * pderiv b P) = pderiv b P * pderiv (u c0) (X a) := by
    intro a b
    rw [Derivation.leibniz, pderiv_eq_zero_of_noVar (noVar_pderiv hno0 b), smul_zero, zero_add, smul_eq_mul]
  have h0 : pderiv (u c0) (gR u v pos P) = 0 := by rw [hR, map_zero]
  unfold gR at h0
  rw [map_sum, Finset.sum_eq_single c0] at h0
  · rw [if_pos hc0, key, pderiv_X_self, mul_one] at h0
    exact h0
  · intro c _ hc
    split_ifs with hpc
    · rw [key, pderiv_X_of_ne (fun h => hc (hu h)), mul_zero]
    · rw [map_neg, key, pderiv_X_of_ne (huv c0 c).symm, mul_zero, neg_zero]
  · intro h
    exact absurd (Finset.mem_univ c0) h

/- English proof (translation)
Establish `hR' : gR v u (fun c => !pos c) P = 0` using `by rw [gR_swap, hR, neg_zero]`. Conclude with `gR_pos_lemma v u (fun c => !pos c) hv (fun c c' h => huv c' c h.symm) P hR' (fun c hc => hno c (by simpa using hc)) c0 (by simp [hc0])`.
-/
theorem gR_neg_lemma (u v : κ → σ) (pos : κ → Bool) (hv : Function.Injective v) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hno : ∀ c, pos c = false → NoVar P (v c))
    (c0 : κ) (hc0 : pos c0 = false) : pderiv (u c0) P = 0 := by
  have hR' : gR v u (fun c => !pos c) P = 0 := by rw [gR_swap, hR, neg_zero]
  exact gR_pos_lemma v u (fun c => !pos c) hv (fun c c' h => huv c' c h.symm) P hR'
    (fun c hc => hno c (by simpa using hc)) c0 (by simp [hc0])

/- English proof (translation)
Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `hnoU : ∀ c, pos c = true → NoVar P (u c)`. Introduce `c hc e he`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `(hpU e he c hne).2.mp hc`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnoV : ∀ c, pos c = true → NoVar P (v c)` using `fun c hc => noVar_of_pderiv_eq_zero (gR_pos_lemma u v pos hu huv P hR hnoU c hc)`. Take `⟨e, he⟩` from `exists_mem_support hP`. Establish `hsw : sw e v pos ≤ 0`.

Unfold `sw`. Apply `Finset.sum_nonpos` to reduce the goal to its premises. Introduce `c _`. Use `split_ifs with hc`. Rewrite using `[hnoV c hc e he]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `h2` using `hwV e he`. Establish `h3 : ((sw e v pos : ℤ) : ℚ) ≤ 0` using `by exact_mod_cast hsw`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem seg_pos_gen (u v : κ → σ) (pos : κ → Bool) (hu : Function.Injective u) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hP : P ≠ 0) (nuU nuV : ℚ)
    (hwV : ∀ e ∈ P.support, (sw e v pos : ℚ) = nuV)
    (hpU : ∀ e ∈ P.support, ∀ c, e (u c) ≠ 0 → nuU ≠ 0 ∧ (pos c = true ↔ 0 < nuU)) (hV : 0 < nuV) :
    0 < nuU := by
  by_contra hneg
  push_neg at hneg
  have hnoU : ∀ c, pos c = true → NoVar P (u c) := by
    intro c hc e he
    by_contra hne
    have h1 := (hpU e he c hne).2.mp hc
    linarith
  have hnoV : ∀ c, pos c = true → NoVar P (v c) := fun c hc =>
    noVar_of_pderiv_eq_zero (gR_pos_lemma u v pos hu huv P hR hnoU c hc)
  obtain ⟨e, he⟩ := exists_mem_support hP
  have hsw : sw e v pos ≤ 0 := by
    unfold sw
    apply Finset.sum_nonpos
    intro c _
    split_ifs with hc
    · rw [hnoV c hc e he]
      simp
    · simp
  have h2 := hwV e he
  have h3 : ((sw e v pos : ℤ) : ℚ) ≤ 0 := by exact_mod_cast hsw
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `hnoV : ∀ c, pos c = false → NoVar P (v c)`. Introduce `c hc e he`. Assume the negation of the conclusion as `hne`.

Take `⟨h1, h2⟩` from `hpV e he c hne`. Establish `h3 : ¬ 0 < nuV` using `fun h => by`. Establish `h4` using `h2.mpr h`. Simplify using `[hc] at h4`. Conclude with `h1 (le_antisymm (not_lt.mp h3) hneg)`.

Establish `hnoU : ∀ c, pos c = false → NoVar P (u c)` using `fun c hc => noVar_of_pderiv_eq_zero (gR_neg_lemma u v pos hv huv P hR hnoV c hc)`. Take `⟨e, he⟩` from `exists_mem_support hP`. Establish `hsw : 0 ≤ sw e u pos`. Unfold `sw`. Apply `Finset.sum_nonneg` to reduce the goal to its premises.

Introduce `c _`. Use `split_ifs with hc`. Simplify using the standard rewrite rules. Rewrite using `[hnoU c (by simpa using hc) e he]`. Simplify using the standard rewrite rules.

Establish `h2` using `hwU e he`. Establish `h3 : (0 : ℚ) ≤ ((sw e u pos : ℤ) : ℚ)` using `by exact_mod_cast hsw`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem seg_neg_gen (u v : κ → σ) (pos : κ → Bool) (hv : Function.Injective v) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hP : P ≠ 0) (nuU nuV : ℚ)
    (hwU : ∀ e ∈ P.support, (sw e u pos : ℚ) = nuU)
    (hpV : ∀ e ∈ P.support, ∀ c, e (v c) ≠ 0 → nuV ≠ 0 ∧ (pos c = true ↔ 0 < nuV)) (hU : nuU < 0) :
    nuV < 0 := by
  by_contra hneg
  push_neg at hneg
  have hnoV : ∀ c, pos c = false → NoVar P (v c) := by
    intro c hc e he
    by_contra hne
    obtain ⟨h1, h2⟩ := hpV e he c hne
    have h3 : ¬ 0 < nuV := fun h => by
      have h4 := h2.mpr h
      simp [hc] at h4
    exact h1 (le_antisymm (not_lt.mp h3) hneg)
  have hnoU : ∀ c, pos c = false → NoVar P (u c) := fun c hc =>
    noVar_of_pderiv_eq_zero (gR_neg_lemma u v pos hv huv P hR hnoV c hc)
  obtain ⟨e, he⟩ := exists_mem_support hP
  have hsw : 0 ≤ sw e u pos := by
    unfold sw
    apply Finset.sum_nonneg
    intro c _
    split_ifs with hc
    · simp
    · rw [hnoU c (by simpa using hc) e he]
      simp
  have h2 := hwU e he
  have h3 : (0 : ℚ) ≤ ((sw e u pos : ℤ) : ℚ) := by exact_mod_cast hsw
  linarith

end Gen

/- English proof (translation)
Establish `hrow : ∀ a, |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| ≤ ∑ c, (x a c : ℤ)`. Introduce `a`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Establish `heq : |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| = ∑ c, (x a c : ℤ)` using `(Finset.sum_eq_sum_iff_of_le (fun a _ => hrow a)).mp h a (Finset.mem_univ a)`.

Establish `hxpos : (0 : ℤ) < x a c` using `by exact_mod_cast Nat.pos_of_ne_zero hx`. Establish `hle : (x a c : ℤ) ≤ ∑ c, (x a c : ℤ)` using `Finset.single_le_sum (f := fun c => (x a c : ℤ)) (fun c _ => Nat.cast_nonneg _) (Finset.mem_univ c)`. Break down `le_or_gt 0 (∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) with hs | hs` into its components or cases. Rewrite `heq` using `[abs_of_nonneg hs]`. Establish `hz : ∑ c, ((x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) = 0`.

Rewrite using `[Finset.sum_sub_distrib, heq, sub_self]`. Establish `hnn : ∀ c ∈ Finset.univ, 0 ≤ (x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))`. Introduce `c _`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hc0 : (x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) = 0` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz c (Finset.mem_univ c)`.

Establish `hpc : pos a c = true`. Assume the negation of the conclusion as `hpc`. Rewrite `hc0` using `[if_neg hpc]`. Use linear arithmetic over natural numbers and integers. Use `⟨by omega, ?_⟩` and prove the remaining obligations.

Rewrite using `[hpc]`. Conclude with `⟨fun _ => by omega, fun _ => rfl⟩`. Rewrite `heq` using `[abs_of_neg hs]`. Establish `hz : ∑ c, ((x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) = 0`. Rewrite using `[Finset.sum_add_distrib]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnn : ∀ c ∈ Finset.univ, 0 ≤ (x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))`. Introduce `c _`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hc0 : (x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) = 0` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz c (Finset.mem_univ c)`.

Establish `hpc : pos a c = false`. Assume the negation of the conclusion as `hpc`. Rewrite `hc0` using `[if_pos (by simpa using hpc)]`. Use linear arithmetic over natural numbers and integers. Use `⟨hs.ne, ?_⟩` and prove the remaining obligations.

Rewrite using `[hpc]`. Prove the components needed by the constructor for the conclusion. Introduce `h'`. Conclude with `absurd h' (by decide)`. Introduce `h'`.

Conclude with `absurd h' (not_lt.mpr hs.le)`.
-/
theorem pure_gen {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → κ → ℕ) (pos : ι → κ → Bool)
    (h : ∑ a, |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| = ∑ a, ∑ c, (x a c : ℤ))
    (a : ι) (c : κ) (hx : x a c ≠ 0) :
    (∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) ≠ 0 ∧
      (pos a c = true ↔ 0 < ∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) := by
  have hrow : ∀ a, |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| ≤ ∑ c, (x a c : ℤ) := by
    intro a
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
    split_ifs <;> simp
  have heq : |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| = ∑ c, (x a c : ℤ) :=
    (Finset.sum_eq_sum_iff_of_le (fun a _ => hrow a)).mp h a (Finset.mem_univ a)
  have hxpos : (0 : ℤ) < x a c := by exact_mod_cast Nat.pos_of_ne_zero hx
  have hle : (x a c : ℤ) ≤ ∑ c, (x a c : ℤ) :=
    Finset.single_le_sum (f := fun c => (x a c : ℤ)) (fun c _ => Nat.cast_nonneg _) (Finset.mem_univ c)
  rcases le_or_gt 0 (∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) with hs | hs
  · rw [abs_of_nonneg hs] at heq
    have hz : ∑ c, ((x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) = 0 := by
      rw [Finset.sum_sub_distrib, heq, sub_self]
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) := by
      intro c _
      split_ifs <;> omega
    have hc0 : (x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz c (Finset.mem_univ c)
    have hpc : pos a c = true := by
      by_contra hpc
      rw [if_neg hpc] at hc0
      omega
    refine ⟨by omega, ?_⟩
    rw [hpc]
    exact ⟨fun _ => by omega, fun _ => rfl⟩
  · rw [abs_of_neg hs] at heq
    have hz : ∑ c, ((x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) = 0 := by
      rw [Finset.sum_add_distrib]
      linarith
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) := by
      intro c _
      split_ifs <;> omega
    have hc0 : (x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz c (Finset.mem_univ c)
    have hpc : pos a c = false := by
      by_contra hpc
      rw [if_pos (by simpa using hpc)] at hc0
      omega
    refine ⟨hs.ne, ?_⟩
    rw [hpc]
    constructor
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      exact absurd h' (not_lt.mpr hs.le)

/- English proof (translation)
Establish `h1 : P ∈ wtSub (fockAct1 p q r s) μ`. Unfold `hwSub at hP`. Conclude with `(Submodule.mem_inf.mp hP).1`. Establish `h2 : fockAct1 p q r s (Eab a a) P = (((μ a : ℚ) : ℂ)) • P`. Unfold `wtSub at h1`.

Establish `h3` using `(Submodule.mem_iInf _).mp h1 a`. Rewrite `h3` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Conclude with `h3`. Establish `h4 : ((((wt1 e a : ℤ) : ℚ) + sh1 p q r s a : ℚ) : ℂ) = (((μ a : ℚ)) : ℂ)` using `eig_of_mem_support (fockAct1 p q r s (Eab a a)) (fun m => ((((wt1 m a : ℤ) : ℚ) + sh1 p q r s a : ℚ) : ℂ)) (fun m => hW p q r s a m) P _ h2 e he`. Establish `h5 : ((wt1 e a : ℤ) : ℚ) + sh1 p q r s a = μ a` using `by exact_mod_cast h4`.

Break down `a with i | j` into its components or cases. Simplify using `only [nu1, shiftNu]`. Simplify using `only [sh1, Sum.elim_inl] at h5`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [nu1, shiftNu]`.

Simplify using `only [sh1, Sum.elim_inr] at h5`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem monomialLeftWeight_eq_weight_sub (hW : FormWt1) {p q r s : ℕ} {μ : Ix p q → ℚ} {P : Pol p q r s}
    (hP : P ∈ hwSub (fockAct1 p q r s) μ) (e : Ln p q r s →₀ ℕ) (he : e ∈ P.support) (a : Ix p q) :
    ((wt1 e a : ℤ) : ℚ) = nu1 p q r s μ a := by
  have h1 : P ∈ wtSub (fockAct1 p q r s) μ := by
    unfold hwSub at hP
    exact (Submodule.mem_inf.mp hP).1
  have h2 : fockAct1 p q r s (Eab a a) P = (((μ a : ℚ) : ℂ)) • P := by
    unfold wtSub at h1
    have h3 := (Submodule.mem_iInf _).mp h1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
    exact h3
  have h4 : ((((wt1 e a : ℤ) : ℚ) + sh1 p q r s a : ℚ) : ℂ) = (((μ a : ℚ)) : ℂ) :=
    eig_of_mem_support (fockAct1 p q r s (Eab a a))
      (fun m => ((((wt1 m a : ℤ) : ℚ) + sh1 p q r s a : ℚ) : ℂ)) (fun m => hW p q r s a m) P _ h2 e he
  have h5 : ((wt1 e a : ℤ) : ℚ) + sh1 p q r s a = μ a := by exact_mod_cast h4
  rcases a with i | j
  · simp only [nu1, shiftNu]
    simp only [sh1, Sum.elim_inl] at h5
    linarith
  · simp only [nu1, shiftNu]
    simp only [sh1, Sum.elim_inr] at h5
    linarith

/- English proof (translation)
Establish `h1 : P ∈ wtSub (fockAct2 p q r s) μ'`. Unfold `hwSub at hP`. Conclude with `(Submodule.mem_inf.mp hP).1`. Establish `h2 : fockAct2 p q r s (Eab c c) P = (((μ' c : ℚ) : ℂ)) • P`. Unfold `wtSub at h1`.

Establish `h3` using `(Submodule.mem_iInf _).mp h1 c`. Rewrite `h3` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Conclude with `h3`. Establish `h4 : ((((wt2 e c : ℤ) : ℚ) + sh2 p q r s c : ℚ) : ℂ) = (((μ' c : ℚ)) : ℂ)` using `eig_of_mem_support (fockAct2 p q r s (Eab c c)) (fun m => ((((wt2 m c : ℤ) : ℚ) + sh2 p q r s c : ℚ) : ℂ)) (fun m => hW p q r s c m) P _ h2 e he`. Establish `h5 : ((wt2 e c : ℤ) : ℚ) + sh2 p q r s c = μ' c` using `by exact_mod_cast h4`.

Break down `c with i | j` into its components or cases. Simplify using `only [nu2, shiftNu]`. Simplify using `only [sh2, Sum.elim_inl] at h5`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [nu2, shiftNu]`.

Simplify using `only [sh2, Sum.elim_inr] at h5`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem monomialRightWeight_eq_weight_sub (hW : FormWt2) {p q r s : ℕ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hP : P ∈ hwSub (fockAct2 p q r s) μ') (e : Ln p q r s →₀ ℕ) (he : e ∈ P.support) (c : Ix r s) :
    ((wt2 e c : ℤ) : ℚ) = nu2 p q r s μ' c := by
  have h1 : P ∈ wtSub (fockAct2 p q r s) μ' := by
    unfold hwSub at hP
    exact (Submodule.mem_inf.mp hP).1
  have h2 : fockAct2 p q r s (Eab c c) P = (((μ' c : ℚ) : ℂ)) • P := by
    unfold wtSub at h1
    have h3 := (Submodule.mem_iInf _).mp h1 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
    exact h3
  have h4 : ((((wt2 e c : ℤ) : ℚ) + sh2 p q r s c : ℚ) : ℂ) = (((μ' c : ℚ)) : ℂ) :=
    eig_of_mem_support (fockAct2 p q r s (Eab c c))
      (fun m => ((((wt2 m c : ℤ) : ℚ) + sh2 p q r s c : ℚ) : ℂ)) (fun m => hW p q r s c m) P _ h2 e he
  have h5 : ((wt2 e c : ℤ) : ℚ) + sh2 p q r s c = μ' c := by exact_mod_cast h4
  rcases c with i | j
  · simp only [nu2, shiftNu]
    simp only [sh2, Sum.elim_inl] at h5
    linarith
  · simp only [nu2, shiftNu]
    simp only [sh2, Sum.elim_inr] at h5
    linarith

/- English proof (translation)
Establish `hM'` using `hM`. Unfold `MinHyp at hM'`. Establish `h` using `hM'.1`. Unfold `JH at h`. Conclude with `(Submodule.mem_inf.mp (Submodule.mem_inf.mp h).1).1`.
-/
theorem mem_leftHighestWeight_of_isMinimalJointVector {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : P ∈ hwSub (fockAct1 p q r s) μ := by
  have hM' := hM
  unfold MinHyp at hM'
  have h := hM'.1
  unfold JH at h
  exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp h).1).1

/- English proof (translation)
Establish `hM'` using `hM`. Unfold `MinHyp at hM'`. Establish `h` using `hM'.1`. Unfold `JH at h`. Conclude with `(Submodule.mem_inf.mp (Submodule.mem_inf.mp h).1).2`.
-/
theorem mem_rightHighestWeight_of_isMinimalJointVector {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : P ∈ hwSub (fockAct2 p q r s) μ' := by
  have hM' := hM
  unfold MinHyp at hM'
  have h := hM'.1
  unfold JH at h
  exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp h).1).2

/- English proof (translation)
Introduce `p q r s μ μ' P hM e he l hl`. Establish `hP1` using `mem_leftHighestWeight_of_isMinimalJointVector hM`. Establish `hP2` using `mem_rightHighestWeight_of_isMinimalJointVector hM`. Establish `hM'` using `hM`. Unfold `MinHyp at hM'`.

Take `⟨-, -, d, hd1, hd2, hH⟩` from `hM'`. Establish `hdeg : ∑ l : Ln p q r s, e l = d`. Establish `h0` using `(mem_homogeneousSubmodule d P).mp hH (mem_support_iff.mp he)`. Use `first`. Consider the case `simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h0`.

Consider the case `simpa [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] using h0`. Establish `hsum : (∑ a : Ix p q, ∑ c : Ix r s, (e (a, c) : ℤ)) = d`. Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `hdeg` after adjusting the coercions. Establish `hrow : ∑ a, |∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then (e (a, c) : ℤ) else -(e (a, c) : ℤ))| = ∑ a : Ix p q, ∑ c : Ix r s, (e (a, c) : ℤ)`.

Establish `h1 : (∑ a, |((wt1 e a : ℤ) : ℚ)|) = (d : ℚ)`. Rewrite using `[hd1]`. Unfold `degW`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[monomialLeftWeight_eq_weight_sub hW1 hP1 e he a]`.

Establish `h3 : (∑ a, |wt1 e a|) = (d : ℤ)` using `by exact_mod_cast h1`. Rewrite using `[hsum]`. Conclude with `h3`. Establish `hcol : ∑ c, |∑ a : Ix p q, (if linePos ((a, c) : Ln p q r s) = true then (e (a, c) : ℤ) else -(e (a, c) : ℤ))| = ∑ c : Ix r s, ∑ a : Ix p q, (e (a, c) : ℤ)`. Establish `h1 : (∑ c, |((wt2 e c : ℤ) : ℚ)|) = (d : ℚ)`.

Rewrite using `[hd2]`. Unfold `degW`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[monomialRightWeight_eq_weight_sub hW2 hP2 e he c]`. Establish `h3 : (∑ c, |wt2 e c|) = (d : ℤ)` using `by exact_mod_cast h1`.

Rewrite using `[Finset.sum_comm, hsum]`. Conclude with `h3`. Take `⟨a, c⟩` from `l`. Take `⟨r1, r2⟩` from `pure_gen (fun a c => (e ((a, c) : Ln p q r s))) (fun a c => linePos ((a, c) : Ln p q r s)) hrow a c hl`. Take `⟨c1, c2⟩` from `pure_gen (fun c a => (e ((a, c) : Ln p q r s))) (fun c a => linePos ((a, c) : Ln p q r s)) hcol c a hl`.

Establish `r1' : wt1 e a ≠ 0` using `r1`. Establish `r2' : linePos ((a, c) : Ln p q r s) = true ↔ 0 < wt1 e a` using `r2`. Establish `c1' : wt2 e c ≠ 0` using `c1`. Establish `c2' : linePos ((a, c) : Ln p q r s) = true ↔ 0 < wt2 e c` using `c2`. Establish `hw1` using `monomialLeftWeight_eq_weight_sub hW1 hP1 e he a`.

Establish `hw2` using `monomialRightWeight_eq_weight_sub hW2 hP2 e he c`. Establish `k1 : nu1 p q r s μ a ≠ 0`. Rewrite using `[← hw1]`. Conclude with `r1'` after adjusting the coercions. Establish `k2 : nu2 p q r s μ' c ≠ 0`.

Rewrite using `[← hw2]`. Conclude with `c1'` after adjusting the coercions. Establish `k3 : linePos ((a, c) : Ln p q r s) = true ↔ 0 < nu1 p q r s μ a`. Rewrite using `[← hw1, r2']`. Conclude with `Int.cast_pos.symm`.

Establish `k4 : linePos ((a, c) : Ln p q r s) = true ↔ 0 < nu2 p q r s μ' c`. Rewrite using `[← hw2, c2']`. Conclude with `Int.cast_pos.symm`. Conclude with `⟨k1, k2, k3, k4⟩`.
-/
theorem pureJ_of (hW1 : FormWt1) (hW2 : FormWt2) : PureJ := by
  intro p q r s μ μ' P hM e he l hl
  have hP1 := mem_leftHighestWeight_of_isMinimalJointVector hM
  have hP2 := mem_rightHighestWeight_of_isMinimalJointVector hM
  have hM' := hM
  unfold MinHyp at hM'
  obtain ⟨-, -, d, hd1, hd2, hH⟩ := hM'
  have hdeg : ∑ l : Ln p q r s, e l = d := by
    have h0 := (mem_homogeneousSubmodule d P).mp hH (mem_support_iff.mp he)
    first
      | simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h0
      | simpa [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] using h0
  have hsum : (∑ a : Ix p q, ∑ c : Ix r s, (e (a, c) : ℤ)) = d := by
    rw [← Fintype.sum_prod_type']
    exact_mod_cast hdeg
  have hrow : ∑ a, |∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then (e (a, c) : ℤ) else -(e (a, c) : ℤ))|
      = ∑ a : Ix p q, ∑ c : Ix r s, (e (a, c) : ℤ) := by
    have h1 : (∑ a, |((wt1 e a : ℤ) : ℚ)|) = (d : ℚ) := by
      rw [hd1]
      unfold degW
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [monomialLeftWeight_eq_weight_sub hW1 hP1 e he a]
    have h3 : (∑ a, |wt1 e a|) = (d : ℤ) := by exact_mod_cast h1
    rw [hsum]
    exact h3
  have hcol : ∑ c, |∑ a : Ix p q, (if linePos ((a, c) : Ln p q r s) = true then (e (a, c) : ℤ) else -(e (a, c) : ℤ))|
      = ∑ c : Ix r s, ∑ a : Ix p q, (e (a, c) : ℤ) := by
    have h1 : (∑ c, |((wt2 e c : ℤ) : ℚ)|) = (d : ℚ) := by
      rw [hd2]
      unfold degW
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [monomialRightWeight_eq_weight_sub hW2 hP2 e he c]
    have h3 : (∑ c, |wt2 e c|) = (d : ℤ) := by exact_mod_cast h1
    rw [Finset.sum_comm, hsum]
    exact h3
  obtain ⟨a, c⟩ := l
  obtain ⟨r1, r2⟩ := pure_gen (fun a c => (e ((a, c) : Ln p q r s))) (fun a c => linePos ((a, c) : Ln p q r s))
    hrow a c hl
  obtain ⟨c1, c2⟩ := pure_gen (fun c a => (e ((a, c) : Ln p q r s))) (fun c a => linePos ((a, c) : Ln p q r s))
    hcol c a hl
  have r1' : wt1 e a ≠ 0 := r1
  have r2' : linePos ((a, c) : Ln p q r s) = true ↔ 0 < wt1 e a := r2
  have c1' : wt2 e c ≠ 0 := c1
  have c2' : linePos ((a, c) : Ln p q r s) = true ↔ 0 < wt2 e c := c2
  have hw1 := monomialLeftWeight_eq_weight_sub hW1 hP1 e he a
  have hw2 := monomialRightWeight_eq_weight_sub hW2 hP2 e he c
  have k1 : nu1 p q r s μ a ≠ 0 := by
    rw [← hw1]
    exact_mod_cast r1'
  have k2 : nu2 p q r s μ' c ≠ 0 := by
    rw [← hw2]
    exact_mod_cast c1'
  have k3 : linePos ((a, c) : Ln p q r s) = true ↔ 0 < nu1 p q r s μ a := by
    rw [← hw1, r2']
    exact Int.cast_pos.symm
  have k4 : linePos ((a, c) : Ln p q r s) = true ↔ 0 < nu2 p q r s μ' c := by
    rw [← hw2, c2']
    exact Int.cast_pos.symm
  exact ⟨k1, k2, k3, k4⟩

/- English proof (translation)
Unfold `rai1 gR`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `show raiB (a, c) (lowB (b, c) P) = _`. Use `beta_reduce`.

Unfold `raiB lowB`. Rewrite using `[hsame c]`. Distinguish the cases in `h : linePos ((a, c) : Ln p q r s) = true`. Simplify using `only [if_pos h]`. Simplify using the standard rewrite rules.

Establish `hne : ((b, c) : Ln p q r s) ≠ (a, c)` using `fun e => hab (Prod.ext_iff.mp e).1.symm`. Simplify using `only [if_neg h]`. Simplify using `[Derivation.leibniz, pderiv_X_of_ne hne, hne]`.
-/
theorem leftRootOperator_eq_signedPolarization {p q r s : ℕ} (a b : Ix p q) (hab : a ≠ b)
    (hsame : ∀ c : Ix r s, linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) (P : Pol p q r s) :
    rai1 (r := r) (s := s) a b P = gR (fun c : Ix r s => ((a, c) : Ln p q r s)) (fun c => (b, c))
      (fun c => linePos ((a, c) : Ln p q r s)) P := by
  unfold rai1 gR
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  show raiB (a, c) (lowB (b, c) P) = _
  beta_reduce
  unfold raiB lowB
  rw [hsame c]
  by_cases h : linePos ((a, c) : Ln p q r s) = true
  · simp only [if_pos h]
    simp
  · have hne : ((b, c) : Ln p q r s) ≠ (a, c) := fun e => hab (Prod.ext_iff.mp e).1.symm
    simp only [if_neg h]
    simp [Derivation.leibniz, pderiv_X_of_ne hne, hne]

/- English proof (translation)
Unfold `rai2 gR`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show raiB (a, c) (lowB (a, d) P) = _`. Use `beta_reduce`.

Unfold `raiB lowB`. Rewrite using `[hsame a]`. Distinguish the cases in `h : linePos ((a, c) : Ln p q r s) = true`. Simplify using `only [if_pos h]`. Simplify using the standard rewrite rules.

Establish `hne : ((a, d) : Ln p q r s) ≠ (a, c)` using `fun e => hcd (Prod.ext_iff.mp e).2.symm`. Simplify using `only [if_neg h]`. Simplify using `[Derivation.leibniz, pderiv_X_of_ne hne, hne]`.
-/
theorem rightRootOperator_eq_signedPolarization {p q r s : ℕ} (c d : Ix r s) (hcd : c ≠ d)
    (hsame : ∀ a : Ix p q, linePos ((a, d) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) (P : Pol p q r s) :
    rai2 (p := p) (q := q) c d P = gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d))
      (fun a => linePos ((a, c) : Ln p q r s)) P := by
  unfold rai2 gR
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  show raiB (a, c) (lowB (a, d) P) = _
  beta_reduce
  unfold raiB lowB
  rw [hsame a]
  by_cases h : linePos ((a, c) : Ln p q r s) = true
  · simp only [if_pos h]
    simp
  · have hne : ((a, d) : Ln p q r s) ≠ (a, c) := fun e => hcd (Prod.ext_iff.mp e).2.symm
    simp only [if_neg h]
    simp [Derivation.leibniz, pderiv_X_of_ne hne, hne]

/- English proof (translation)
Unfold `hwSub at hv`. Establish `h` using `(Submodule.mem_inf.mp hv).2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at h`. Conclude with `h a b hab`.
-/
theorem ker_of_hw {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub act μ) (a b : Ix p q) (hab : posC a b) : act (Eab a b) v = 0 := by
  unfold hwSub at hv
  have h := (Submodule.mem_inf.mp hv).2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h
  exact h a b hab

/- English proof (translation)
Introduce `hab`. Substitute `hab` using the available equality. Apply the tactic sequence `rcases a with i | i <;> exact absurd h (by simp [posC])`.
-/
theorem ne_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : a ≠ b := by
  intro hab
  subst hab
  rcases a with i | i <;> exact absurd h (by simp [posC])

/- English proof (translation)
Establish `hP1` using `mem_leftHighestWeight_of_isMinimalJointVector hM`. Establish `hne` using `ne_of_posC hab`. Establish `hR : gR (fun c : Ix r s => ((a, c) : Ln p q r s)) (fun c => (b, c)) (fun c => linePos ((a, c) : Ln p q r s)) P = 0`. Rewrite using `[← leftRootOperator_eq_signedPolarization a b hne hsame P, ← hR1 p q r s a b hne]`. Conclude with `ker_of_hw hP1 a b hab`.

Establish `hu : Function.Injective (fun c : Ix r s => ((a, c) : Ln p q r s))` using `fun c c' h => (Prod.ext_iff.mp h).2`. Establish `hv : Function.Injective (fun c : Ix r s => ((b, c) : Ln p q r s))` using `fun c c' h => (Prod.ext_iff.mp h).2`. Establish `huv : ∀ c c' : Ix r s, ((a, c) : Ln p q r s) ≠ (b, c')` using `fun c c' h => hne (Prod.ext_iff.mp h).1`. Establish `hM'` using `hM`. Unfold `MinHyp at hM'`.

Establish `hPJ` using `pureJ_of hW1 hW2 p q r s μ μ' P hM`. Establish `hswA : ∀ e ∈ P.support, (sw e (fun c : Ix r s => ((a, c) : Ln p q r s)) (fun c => linePos ((a, c) : Ln p q r s)) : ℚ) = nu1 p q r s μ a`. Introduce `e he`. Rewrite using `[← monomialLeftWeight_eq_weight_sub hW1 hP1 e he a]`. Both sides reduce to the same expression.

Establish `hswB : ∀ e ∈ P.support, (sw e (fun c : Ix r s => ((b, c) : Ln p q r s)) (fun c => linePos ((a, c) : Ln p q r s)) : ℚ) = nu1 p q r s μ b`. Introduce `e he`. Rewrite using `[← monomialLeftWeight_eq_weight_sub hW1 hP1 e he b]`. Use `congr 1`. Unfold `sw wt1`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hsame c]`. Use `⟨fun hb => seg_pos_gen _ _ _ hu huv P hR hM'.2.1 _ _ hswB ?_ hb, fun ha => seg_neg_gen _ _ _ hv huv P hR hM'.2.1 _ _ hswA ?_ ha⟩` and prove the remaining obligations. Introduce `e he c hc`. Take `⟨h1, -, h3, -⟩` from `hPJ e he (a, c) hc`.

Conclude with `⟨h1, h3⟩`. Introduce `e he c hc`. Take `⟨h1, -, h3, -⟩` from `hPJ e he (b, c) hc`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `show linePos ((a, c) : Ln p q r s) = true ↔ _`.

Rewrite using `[← hsame c]`. Conclude with `h3`.
-/
theorem seg1 (hW1 : FormWt1) (hW2 : FormWt2) (hR1 : FormRaise1) {p q r s : ℕ} {μ : Ix p q → ℚ}
    {μ' : Ix r s → ℚ} {P : Pol p q r s} (hM : MinHyp p q r s μ μ' P) (a b : Ix p q) (hab : posC a b)
    (hsame : ∀ c : Ix r s, linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) :
    (0 < nu1 p q r s μ b → 0 < nu1 p q r s μ a) ∧ (nu1 p q r s μ a < 0 → nu1 p q r s μ b < 0) := by
  have hP1 := mem_leftHighestWeight_of_isMinimalJointVector hM
  have hne := ne_of_posC hab
  have hR : gR (fun c : Ix r s => ((a, c) : Ln p q r s)) (fun c => (b, c))
      (fun c => linePos ((a, c) : Ln p q r s)) P = 0 := by
    rw [← leftRootOperator_eq_signedPolarization a b hne hsame P, ← hR1 p q r s a b hne]
    exact ker_of_hw hP1 a b hab
  have hu : Function.Injective (fun c : Ix r s => ((a, c) : Ln p q r s)) := fun c c' h => (Prod.ext_iff.mp h).2
  have hv : Function.Injective (fun c : Ix r s => ((b, c) : Ln p q r s)) := fun c c' h => (Prod.ext_iff.mp h).2
  have huv : ∀ c c' : Ix r s, ((a, c) : Ln p q r s) ≠ (b, c') := fun c c' h => hne (Prod.ext_iff.mp h).1
  have hM' := hM
  unfold MinHyp at hM'
  have hPJ := pureJ_of hW1 hW2 p q r s μ μ' P hM
  have hswA : ∀ e ∈ P.support, (sw e (fun c : Ix r s => ((a, c) : Ln p q r s))
      (fun c => linePos ((a, c) : Ln p q r s)) : ℚ) = nu1 p q r s μ a := by
    intro e he
    rw [← monomialLeftWeight_eq_weight_sub hW1 hP1 e he a]
    rfl
  have hswB : ∀ e ∈ P.support, (sw e (fun c : Ix r s => ((b, c) : Ln p q r s))
      (fun c => linePos ((a, c) : Ln p q r s)) : ℚ) = nu1 p q r s μ b := by
    intro e he
    rw [← monomialLeftWeight_eq_weight_sub hW1 hP1 e he b]
    congr 1
    unfold sw wt1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsame c]
  refine ⟨fun hb => seg_pos_gen _ _ _ hu huv P hR hM'.2.1 _ _ hswB ?_ hb,
    fun ha => seg_neg_gen _ _ _ hv huv P hR hM'.2.1 _ _ hswA ?_ ha⟩
  · intro e he c hc
    obtain ⟨h1, -, h3, -⟩ := hPJ e he (a, c) hc
    exact ⟨h1, h3⟩
  · intro e he c hc
    obtain ⟨h1, -, h3, -⟩ := hPJ e he (b, c) hc
    refine ⟨h1, ?_⟩
    show linePos ((a, c) : Ln p q r s) = true ↔ _
    rw [← hsame c]
    exact h3

/- English proof (translation)
Establish `hP2` using `mem_rightHighestWeight_of_isMinimalJointVector hM`. Establish `hne` using `ne_of_posC hcd`. Establish `hR : gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d)) (fun a => linePos ((a, c) : Ln p q r s)) P = 0`. Rewrite using `[← rightRootOperator_eq_signedPolarization c d hne hsame P, ← hR2 p q r s c d hne]`. Conclude with `ker_of_hw hP2 c d hcd`.

Establish `hu : Function.Injective (fun a : Ix p q => ((a, c) : Ln p q r s))` using `fun a a' h => (Prod.ext_iff.mp h).1`. Establish `hv : Function.Injective (fun a : Ix p q => ((a, d) : Ln p q r s))` using `fun a a' h => (Prod.ext_iff.mp h).1`. Establish `huv : ∀ a a' : Ix p q, ((a, c) : Ln p q r s) ≠ (a', d)` using `fun a a' h => hne (Prod.ext_iff.mp h).2`. Establish `hM'` using `hM`. Unfold `MinHyp at hM'`.

Establish `hPJ` using `pureJ_of hW1 hW2 p q r s μ μ' P hM`. Establish `hswA : ∀ e ∈ P.support, (sw e (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => linePos ((a, c) : Ln p q r s)) : ℚ) = nu2 p q r s μ' c`. Introduce `e he`. Rewrite using `[← monomialRightWeight_eq_weight_sub hW2 hP2 e he c]`. Both sides reduce to the same expression.

Establish `hswB : ∀ e ∈ P.support, (sw e (fun a : Ix p q => ((a, d) : Ln p q r s)) (fun a => linePos ((a, c) : Ln p q r s)) : ℚ) = nu2 p q r s μ' d`. Introduce `e he`. Rewrite using `[← monomialRightWeight_eq_weight_sub hW2 hP2 e he d]`. Use `congr 1`. Unfold `sw wt2`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hsame a]`. Use `⟨fun hd => seg_pos_gen _ _ _ hu huv P hR hM'.2.1 _ _ hswB ?_ hd, fun hc => seg_neg_gen _ _ _ hv huv P hR hM'.2.1 _ _ hswA ?_ hc⟩` and prove the remaining obligations. Introduce `e he a ha`. Take `⟨-, h2, -, h4⟩` from `hPJ e he (a, c) ha`.

Conclude with `⟨h2, h4⟩`. Introduce `e he a ha`. Take `⟨-, h2, -, h4⟩` from `hPJ e he (a, d) ha`. Use `⟨h2, ?_⟩` and prove the remaining obligations. Use `show linePos ((a, c) : Ln p q r s) = true ↔ _`.

Rewrite using `[← hsame a]`. Conclude with `h4`.
-/
theorem seg2 (hW1 : FormWt1) (hW2 : FormWt2) (hR2 : FormRaise2) {p q r s : ℕ} {μ : Ix p q → ℚ}
    {μ' : Ix r s → ℚ} {P : Pol p q r s} (hM : MinHyp p q r s μ μ' P) (c d : Ix r s) (hcd : posC c d)
    (hsame : ∀ a : Ix p q, linePos ((a, d) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) :
    (0 < nu2 p q r s μ' d → 0 < nu2 p q r s μ' c) ∧ (nu2 p q r s μ' c < 0 → nu2 p q r s μ' d < 0) := by
  have hP2 := mem_rightHighestWeight_of_isMinimalJointVector hM
  have hne := ne_of_posC hcd
  have hR : gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d))
      (fun a => linePos ((a, c) : Ln p q r s)) P = 0 := by
    rw [← rightRootOperator_eq_signedPolarization c d hne hsame P, ← hR2 p q r s c d hne]
    exact ker_of_hw hP2 c d hcd
  have hu : Function.Injective (fun a : Ix p q => ((a, c) : Ln p q r s)) := fun a a' h => (Prod.ext_iff.mp h).1
  have hv : Function.Injective (fun a : Ix p q => ((a, d) : Ln p q r s)) := fun a a' h => (Prod.ext_iff.mp h).1
  have huv : ∀ a a' : Ix p q, ((a, c) : Ln p q r s) ≠ (a', d) := fun a a' h => hne (Prod.ext_iff.mp h).2
  have hM' := hM
  unfold MinHyp at hM'
  have hPJ := pureJ_of hW1 hW2 p q r s μ μ' P hM
  have hswA : ∀ e ∈ P.support, (sw e (fun a : Ix p q => ((a, c) : Ln p q r s))
      (fun a => linePos ((a, c) : Ln p q r s)) : ℚ) = nu2 p q r s μ' c := by
    intro e he
    rw [← monomialRightWeight_eq_weight_sub hW2 hP2 e he c]
    rfl
  have hswB : ∀ e ∈ P.support, (sw e (fun a : Ix p q => ((a, d) : Ln p q r s))
      (fun a => linePos ((a, c) : Ln p q r s)) : ℚ) = nu2 p q r s μ' d := by
    intro e he
    rw [← monomialRightWeight_eq_weight_sub hW2 hP2 e he d]
    congr 1
    unfold sw wt2
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsame a]
  refine ⟨fun hd => seg_pos_gen _ _ _ hu huv P hR hM'.2.1 _ _ hswB ?_ hd,
    fun hc => seg_neg_gen _ _ _ hv huv P hR hM'.2.1 _ _ hswA ?_ hc⟩
  · intro e he a ha
    obtain ⟨-, h2, -, h4⟩ := hPJ e he (a, c) ha
    exact ⟨h2, h4⟩
  · intro e he a ha
    obtain ⟨-, h2, -, h4⟩ := hPJ e he (a, d) ha
    refine ⟨h2, ?_⟩
    show linePos ((a, c) : Ln p q r s) = true ↔ _
    rw [← hsame a]
    exact h4

/- English proof (translation)
Introduce `p q r s μ μ' P hM`. Use `⟨fun i i' h => (seg1 hW1 hW2 hR1 hM (.inl i) (.inl i') h (fun c => ?_)).1, fun i i' h => (seg1 hW1 hW2 hR1 hM (.inl i) (.inl i') h (fun c => ?_)).2, fun j j' h => (seg1 hW1 hW2 hR1 hM (.inr j) (.inr j') h (fun c => ?_)).1, fun j j' h => (seg1 hW1 hW2 hR1 hM (.inr j) (.inr j') h ( …` and prove the remaining obligations. Apply the tactic sequence `all_goals first`. Consider the case `(rcases c with _ | _ <;> rfl)`. Consider the case `(rcases a with _ | _ <;> rfl)`.
-/
theorem segJ_of (hW1 : FormWt1) (hW2 : FormWt2) (hR1 : FormRaise1) (hR2 : FormRaise2) : SegJ := by
  intro p q r s μ μ' P hM
  refine ⟨fun i i' h => (seg1 hW1 hW2 hR1 hM (.inl i) (.inl i') h (fun c => ?_)).1,
    fun i i' h => (seg1 hW1 hW2 hR1 hM (.inl i) (.inl i') h (fun c => ?_)).2,
    fun j j' h => (seg1 hW1 hW2 hR1 hM (.inr j) (.inr j') h (fun c => ?_)).1,
    fun j j' h => (seg1 hW1 hW2 hR1 hM (.inr j) (.inr j') h (fun c => ?_)).2,
    fun k k' h => (seg2 hW1 hW2 hR2 hM (.inl k) (.inl k') h (fun a => ?_)).1,
    fun k k' h => (seg2 hW1 hW2 hR2 hM (.inl k) (.inl k') h (fun a => ?_)).2,
    fun l l' h => (seg2 hW1 hW2 hR2 hM (.inr l) (.inr l') h (fun a => ?_)).1,
    fun l l' h => (seg2 hW1 hW2 hR2 hM (.inr l) (.inr l') h (fun a => ?_)).2⟩
  all_goals first
    | (rcases c with _ | _ <;> rfl)
    | (rcases a with _ | _ <;> rfl)

end PI.FJMP
