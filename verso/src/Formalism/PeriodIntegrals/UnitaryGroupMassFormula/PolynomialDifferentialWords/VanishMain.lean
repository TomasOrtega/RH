import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.VanishExp

open MvPolynomial

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

/- English proof (translation)
Rewrite using `[eval_eq]`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Take `⟨i, hmi, hpi⟩` from `h m hm`. Rewrite using `[Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hmi) (by rw [hpi]; exact zero_pow hmi), mul_zero]`.
-/
lemma eval_eq_zero_of_support (g : Pol K k) (p : Fin k ⊕ Fin k → K)
    (h : ∀ m ∈ g.support, ∃ i, m i ≠ 0 ∧ p i = 0) : eval p g = 0 := by
  rw [eval_eq]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨i, hmi, hpi⟩ := h m hm
  rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hmi) (by rw [hpi]; exact zero_pow hmi), mul_zero]

/- English proof (translation)
Establish `hg' : g ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d` using `hg`. Establish `hx` using `(Submodule.mem_inf.1 hg').1`. Rewrite `hx` using `[mem_weightedHomogeneousSubmodule]`. Establish `h1` using `hx (MvPolynomial.mem_support_iff.1 hm)`. Simplify `h1` using `[Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type]`.
-/
lemma xdeg_of_bihom {d : ℕ} {g : Pol K k} (hg : g ∈ Bihom K k d) {m : Fin k ⊕ Fin k →₀ ℕ}
    (hm : m ∈ g.support) : ∑ a, m (Sum.inl a) = d := by
  have hg' : g ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hg
  have hx := (Submodule.mem_inf.1 hg').1
  rw [mem_weightedHomogeneousSubmodule] at hx
  have h1 := hx (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type] using h1

/- English proof (translation)
Apply `eval_eq_zero_of_support` to reduce the goal to its premises. Introduce `m hm`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hzero : ∀ b, b ≠ i0 → m (Sum.inl b) = 0`.

Introduce `b hb`. Assume the negation of the conclusion as `h0`. Conclude with `hne _ h0 (hx b hb)`. Establish `hr : m (Sum.inr i0) = 0`. Assume the negation of the conclusion as `h0`.

Conclude with `hne _ h0 hxi`. Establish `hsum` using `xdeg_of_bihom hg hm`. Rewrite `hsum` using `[Finset.sum_eq_single i0 (fun b _ hb => hzero b hb) (fun h => absurd (Finset.mem_univ i0) h)]`. Establish `h2` using `hw m hm i0`. Use linear arithmetic over natural numbers and integers.
-/
lemma eval_base {d c : ℕ} (hcd : c < d) (i0 : Fin k) {g : Pol K k} (hg : g ∈ Bihom K k d)
    (hw : WtLe K k c g) (p : Fin k ⊕ Fin k → K) (hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0)
    (hxi : p (Sum.inr i0) = 0) : eval p g = 0 := by
  apply eval_eq_zero_of_support
  intro m hm
  by_contra hne
  push_neg at hne
  have hzero : ∀ b, b ≠ i0 → m (Sum.inl b) = 0 := by
    intro b hb
    by_contra h0
    exact hne _ h0 (hx b hb)
  have hr : m (Sum.inr i0) = 0 := by
    by_contra h0
    exact hne _ h0 hxi
  have hsum := xdeg_of_bihom hg hm
  rw [Finset.sum_eq_single i0 (fun b _ hb => hzero b hb)
    (fun h => absurd (Finset.mem_univ i0) h)] at hsum
  have h2 := hw m hm i0
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hg`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hst _ ih a b`.
-/
lemma iter_mem (W : Submodule K (Pol K k)) (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W)
    (a b : Fin k) {g : Pol K k} (hg : g ∈ W) (n : ℕ) : (Rop K k a b)^[n] g ∈ W := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hst _ ih a b

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on`. Use `next =>`. Introduce `p hp0 hS hq g hg`. Establish `hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0`. Introduce `b hb`.

Assume the negation of the conclusion as `h`. Conclude with `absurd (hS b hb h) (by simp)`. Establish `hxi : p (Sum.inr i0) = 0`. Rewrite `hq` using `[Finset.sum_eq_single i0 (fun b _ hb => by rw [hx b hb, zero_mul]) (fun h => absurd (Finset.mem_univ i0) h)]`. Conclude with `(mul_eq_zero.1 hq).resolve_left hp0`.

Conclude with `eval_base hcd i0 (hW hg) (hwt g hg) p hx hxi`. Use `next b S hbS ih =>`. Introduce `p hp0 hS hq g hg`. Distinguish the cases in `hpb : p (Sum.inl b) = 0`. Use `ih p hp0 ?_ hq g hg` and prove the remaining obligations.

Introduce `b' hb' hne`. Break down `Finset.mem_insert.1 (hS b' hb' hne) with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `absurd hpb hne`. Conclude with `h`.

Distinguish the cases in `hbi : b = i0`. Use `ih p hp0 ?_ hq g hg` and prove the remaining obligations. Introduce `b' hb' hne`. Break down `Finset.mem_insert.1 (hS b' hb' hne) with h | h` into its components or cases. Conclude with `absurd (h.trans hbi) hb'`.

Conclude with `h`. Establish `hib : i0 ≠ b` using `Ne.symm hbi`. Establish `hshl : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k), shiftPt i0 b t y (Sum.inl j) = y (Sum.inl j) + t * (if j = b then y (Sum.inl i0) else 0)`. Introduce `t y j`. Apply the tactic sequence `by_cases h : j = b <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring`.

Establish `hshr : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k), shiftPt i0 b t y (Sum.inr j) = y (Sum.inr j) - t * (if j = i0 then y (Sum.inr b) else 0)`. Introduce `t y j`. Apply the tactic sequence `by_cases h : j = i0 <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring`. Take `⟨s, hs⟩ : ∃ s : K, s = -(p (Sum.inl b) / p (Sum.inl i0))` from `⟨_, rfl⟩`. Establish `hq0 : shiftPt i0 b s p (Sum.inl i0) = p (Sum.inl i0)`.

Rewrite using `[hshl, if_neg hib, mul_zero, add_zero]`. Establish `hqb : shiftPt i0 b s p (Sum.inl b) = 0`. Rewrite using `[hshl, if_pos rfl, hs, neg_mul, div_mul_cancel₀ _ hp0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hqj : ∀ j, j ≠ b → shiftPt i0 b s p (Sum.inl j) = p (Sum.inl j)`.

Introduce `j hj`. Rewrite using `[hshl, if_neg hj, mul_zero, add_zero]`. Establish `hquad : ∑ i, shiftPt i0 b s p (Sum.inl i) * shiftPt i0 b s p (Sum.inr i) = 0`. Simplify using `only [hshl, hshr, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hbi, hib, if_false, hq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `ihq : ∀ g ∈ W, eval (shiftPt i0 b s p) g = 0`. Use `ih _ (by rw [hq0]; exact hp0) ?_ hquad` and prove the remaining obligations. Introduce `b' hb' hne`. Distinguish the cases in `hbb : b' = b`. Substitute `hbb` using the available equality.

Conclude with `absurd hqb hne`. Rewrite `hne` using `[hqj b' hbb]`. Break down `Finset.mem_insert.1 (hS b' hb' hne) with h | h` into its components or cases. Conclude with `absurd h hbb`. Conclude with `h`.

Establish `hback : shiftPt i0 b (-s) (shiftPt i0 b s p) = p`. Use function extensionality and compare the values at `v`. Break down `v with j | j` into its components or cases. Apply the tactic sequence `by_cases h : j = b <;> simp [hshl, h, hib] <;> ring`. Apply the tactic sequence `by_cases h : j = i0 <;> simp [hshr, h, hbi] <;> ring`.

Establish `hE` using `expFormula i0 b hib (-s) g`. Unfold `ExpFormula at hE`. Take `⟨N, _, hsum⟩` from `hE`. Rewrite using `[← hback, hsum N le_rfl]`. Use `Finset.sum_eq_zero fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[ihq _ (iter_mem W hst i0 b hg n), mul_zero]`.
-/
lemma vanish_at {d c : ℕ} (W : Submodule K (Pol K k)) (hW : W ≤ Bihom K k d)
    (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) (hwt : ∀ f ∈ W, WtLe K k c f) (hcd : c < d)
    (i0 : Fin k) (S : Finset (Fin k)) :
    ∀ p : Fin k ⊕ Fin k → K, p (Sum.inl i0) ≠ 0 → (∀ b, b ≠ i0 → p (Sum.inl b) ≠ 0 → b ∈ S) →
      ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → ∀ g ∈ W, eval p g = 0 := by
  classical
  induction S using Finset.induction_on
  next =>
    intro p hp0 hS hq g hg
    have hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0 := by
      intro b hb
      by_contra h
      exact absurd (hS b hb h) (by simp)
    have hxi : p (Sum.inr i0) = 0 := by
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hx b hb, zero_mul])
        (fun h => absurd (Finset.mem_univ i0) h)] at hq
      exact (mul_eq_zero.1 hq).resolve_left hp0
    exact eval_base hcd i0 (hW hg) (hwt g hg) p hx hxi
  next b S hbS ih =>
    intro p hp0 hS hq g hg
    by_cases hpb : p (Sum.inl b) = 0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · subst h
        exact absurd hpb hne
      · exact h
    by_cases hbi : b = i0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · exact absurd (h.trans hbi) hb'
      · exact h
    have hib : i0 ≠ b := Ne.symm hbi
    have hshl : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inl j) = y (Sum.inl j) + t * (if j = b then y (Sum.inl i0) else 0) := by
      intro t y j
      by_cases h : j = b <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    have hshr : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inr j) = y (Sum.inr j) - t * (if j = i0 then y (Sum.inr b) else 0) := by
      intro t y j
      by_cases h : j = i0 <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    obtain ⟨s, hs⟩ : ∃ s : K, s = -(p (Sum.inl b) / p (Sum.inl i0)) := ⟨_, rfl⟩
    have hq0 : shiftPt i0 b s p (Sum.inl i0) = p (Sum.inl i0) := by
      rw [hshl, if_neg hib, mul_zero, add_zero]
    have hqb : shiftPt i0 b s p (Sum.inl b) = 0 := by
      rw [hshl, if_pos rfl, hs, neg_mul, div_mul_cancel₀ _ hp0]
      ring
    have hqj : ∀ j, j ≠ b → shiftPt i0 b s p (Sum.inl j) = p (Sum.inl j) := by
      intro j hj
      rw [hshl, if_neg hj, mul_zero, add_zero]
    have hquad : ∑ i, shiftPt i0 b s p (Sum.inl i) * shiftPt i0 b s p (Sum.inr i) = 0 := by
      simp only [hshl, hshr, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hbi, hib, if_false, hq]
      ring
    have ihq : ∀ g ∈ W, eval (shiftPt i0 b s p) g = 0 := by
      refine ih _ (by rw [hq0]; exact hp0) ?_ hquad
      intro b' hb' hne
      by_cases hbb : b' = b
      · subst hbb
        exact absurd hqb hne
      · rw [hqj b' hbb] at hne
        rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
        · exact absurd h hbb
        · exact h
    have hback : shiftPt i0 b (-s) (shiftPt i0 b s p) = p := by
      funext v
      rcases v with j | j
      · by_cases h : j = b <;> simp [hshl, h, hib] <;> ring
      · by_cases h : j = i0 <;> simp [hshr, h, hbi] <;> ring
    have hE := expFormula i0 b hib (-s) g
    unfold ExpFormula at hE
    obtain ⟨N, _, hsum⟩ := hE
    rw [← hback, hsum N le_rfl]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [ihq _ (iter_mem W hst i0 b hg n), mul_zero]

/- English proof (translation)
Introduce `K _ _ k d c W hW hst hwt hcd f hf p hp`. Distinguish the cases in `h : ∃ i0, p (Sum.inl i0) ≠ 0`. Take `⟨i0, hi0⟩` from `h`. Conclude with `vanish_at W hW hst hwt hcd i0 Finset.univ p hi0 (fun b _ _ => Finset.mem_univ b) hp f hf`. Use `push_neg at h`.

Apply `eval_eq_zero_of_support` to reduce the goal to its premises. Introduce `m hm`. Establish `hsum` using `xdeg_of_bihom (hW hf) hm`. Establish `hex : ∃ a, m (Sum.inl a) ≠ 0`. Assume the negation of the conclusion as `h0`.

Use `push_neg at h0`. Simplify using `[h0] at hsum`. Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `hex`. Conclude with `⟨Sum.inl a, ha, h a⟩`.
-/
theorem vanishingOnQuadric : Vanish := by
  intro K _ _ k d c W hW hst hwt hcd f hf p hp
  by_cases h : ∃ i0, p (Sum.inl i0) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    exact vanish_at W hW hst hwt hcd i0 Finset.univ p hi0 (fun b _ _ => Finset.mem_univ b) hp f hf
  · push_neg at h
    apply eval_eq_zero_of_support
    intro m hm
    have hsum := xdeg_of_bihom (hW hf) hm
    have hex : ∃ a, m (Sum.inl a) ≠ 0 := by
      by_contra h0
      push_neg at h0
      simp [h0] at hsum
      omega
    obtain ⟨a, ha⟩ := hex
    exact ⟨Sum.inl a, ha, h a⟩

end PI.OpWords
