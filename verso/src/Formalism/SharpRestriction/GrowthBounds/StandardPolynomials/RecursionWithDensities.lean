import Formalism.SharpRestriction.GrowthBounds.PolBridge

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.PolBridge

section YC

variable {K : Type} [Field K] [CharZero K] {N r : ℕ} [NeZero r]

/- English proof (translation)
Unfold `glAct`. Simplify using `only [LinearMap.sum_apply]`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l ∈ S`.

Distinguish the cases in `hv : Lt.vec l = true`. Simplify using `only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [if_neg hl, LinearMap.zero_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem glAct_mul' (Lt : Letters (Fin N)) (S : Set (Fin N)) (c d : Fin r) (f h : MvPolynomial (Fin N × Fin r) K) :
    glAct K Lt S c d (f * h) = glAct K Lt S c d f * h + f * glAct K Lt S c d h := by
  classical
  unfold glAct
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ S
  · by_cases hv : Lt.vec l = true
    · simp only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul]
      ring
    · simp only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
      ring
  · simp only [if_neg hl, LinearMap.zero_apply]
    ring

open Classical in
/- English proof (translation)
Unfold `glAct`. Simplify using `only [LinearMap.sum_apply]`. Rewrite using `[Finset.sum_eq_single a]`. Distinguish the cases in `hl : a ∈ S`. Distinguish the cases in `hv : Lt.vec a = true`.

Simplify using `only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pderiv_X]`. Distinguish the cases in `he : e = d`. Substitute `he` using the available equality. Simplify using the standard rewrite rules. Establish `: (a, d) ≠ (a, e)` using `fun h => he (Prod.mk.inj h).2.symm`.

Simplify using `[he, Pi.single_apply, Ne.symm this]`. Simplify using `only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pderiv_X]`. Distinguish the cases in `he : e = c`. Substitute `he` using the available equality. Simplify using the standard rewrite rules.

Establish `: (a, c) ≠ (a, e)` using `fun h => he (Prod.mk.inj h).2.symm`. Simplify using `[he, Pi.single_apply, Ne.symm this]`. Simplify using `only [if_neg hl, LinearMap.zero_apply]`. Introduce `l _ hla`. Establish `h1 : ∀ b : Fin r, pderiv (l, b) (X (a, e) : MvPolynomial (Fin N × Fin r) K) = 0`.

Introduce `b`. Rewrite using `[pderiv_X, Pi.single_apply, if_neg]`. Introduce `h`. Conclude with `hla (Prod.mk.inj h).1.symm`. Distinguish the cases in `hl : l ∈ S`.

Distinguish the cases in `hv : Lt.vec l = true`. Simplify using `only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, h1, mul_zero]`. Simplify using `only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, h1, mul_zero, neg_zero]`. Simplify using `only [if_neg hl, LinearMap.zero_apply]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem glAct_X' (Lt : Letters (Fin N)) (S : Set (Fin N)) (c d : Fin r) (a : Fin N) (e : Fin r) :
    glAct K Lt S c d (X (a, e)) =
      if a ∈ S then (if Lt.vec a = true then (if e = d then X (a, c) else 0) else (if e = c then -X (a, d) else 0))
      else 0 := by
  classical
  unfold glAct
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_eq_single a]
  · by_cases hl : a ∈ S
    · by_cases hv : Lt.vec a = true
      · simp only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pderiv_X]
        by_cases he : e = d
        · subst he; simp
        · have : (a, d) ≠ (a, e) := fun h => he (Prod.mk.inj h).2.symm
          simp [he, Pi.single_apply, Ne.symm this]
      · simp only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          Derivation.coeFn_coe, pderiv_X]
        by_cases he : e = c
        · subst he; simp
        · have : (a, c) ≠ (a, e) := fun h => he (Prod.mk.inj h).2.symm
          simp [he, Pi.single_apply, Ne.symm this]
    · simp only [if_neg hl, LinearMap.zero_apply]
  · intro l _ hla
    have h1 : ∀ b : Fin r, pderiv (l, b) (X (a, e) : MvPolynomial (Fin N × Fin r) K) = 0 := by
      intro b
      rw [pderiv_X, Pi.single_apply, if_neg]
      intro h
      exact hla (Prod.mk.inj h).1.symm
    by_cases hl : l ∈ S
    · by_cases hv : Lt.vec l = true
      · simp only [if_pos hl, if_pos hv, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, h1, mul_zero]
      · simp only [if_pos hl, if_neg hv, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          Derivation.coeFn_coe, h1, mul_zero, neg_zero]
    · simp only [if_neg hl, LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `chWt`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [Finsupp.add_apply] <;> ring`.
-/
theorem chWt_add (LL : ChainLetters N) (j : ℕ) (c : Fin r) (m m' : Fin N × Fin r →₀ ℕ) :
    chWt LL j c (m + m') = chWt LL j c m + chWt LL j c m' := by
  unfold chWt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Finsupp.add_apply] <;> ring

/- English proof (translation)
Unfold `chWt`. Rewrite using `[Finset.sum_eq_single a]`. Distinguish the cases in `he : e = 0`. Substitute `he` using the available equality. Simplify using the standard rewrite rules.

Establish `: (a, e) ≠ (a, (0 : Fin r))` using `fun h => he (Prod.mk.inj h).2`. Simplify using `[he, Finsupp.single_apply, this]`. Introduce `i _ hia`. Establish `: (a, e) ≠ (i, (0 : Fin r))` using `fun h => hia (Prod.mk.inj h).1.symm`. Simplify using `[Finsupp.single_apply, this]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem chWt_single (LL : ChainLetters N) (j : ℕ) (a : Fin N) (e : Fin r) :
    chWt LL j (0 : Fin r) (Finsupp.single (a, e) 1) =
      if (a : ℕ) < j then (if LL.vec a = true then (if e = 0 then 1 else 0) else (if e = 0 then -1 else 0)) else 0 := by
  classical
  unfold chWt
  rw [Finset.sum_eq_single a]
  · by_cases he : e = 0
    · subst he; simp
    · have : (a, e) ≠ (a, (0 : Fin r)) := fun h => he (Prod.mk.inj h).2
      simp [he, Finsupp.single_apply, this]
  · intro i _ hia
    have : (a, e) ≠ (i, (0 : Fin r)) := fun h => hia (Prod.mk.inj h).1.symm
    simp [Finsupp.single_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
The claim follows from `le_sSup (show V ∈ {S | S ≤ _ ∧ chStable K LL j S} from ⟨h1, h2⟩)`.
-/
theorem ycond_of_stable (LL : ChainLetters N) (j : ℕ) (M : WithTop ℤ) (V : Submodule K (MvPolynomial (Fin N × Fin r) K))
    (h1 : V ≤ MvPolynomial.restrictSupport K {m | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ M}) (h2 : chStable K LL j V) :
    V ≤ YCond K (r := r) LL j M :=
  le_sSup (show V ∈ {S | S ≤ _ ∧ chStable K LL j S} from ⟨h1, h2⟩)

/- English proof (translation)
Use `ycond_of_stable LL j M' _ ?_ (ycond_stable LL j M)` and prove the remaining obligations. Use `(ycond_le LL j M).trans ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx`, the goal using `[MvPolynomial.mem_restrictSupport_iff]`. Conclude with `fun m hm => le_trans (hx hm) h`.
-/
theorem ycond_mono (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ} (h : M ≤ M') :
    YCond K (r := r) LL j M ≤ YCond K (r := r) LL j M' := by
  refine ycond_of_stable LL j M' _ ?_ (ycond_stable LL j M)
  refine (ycond_le LL j M).trans ?_
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

/- English proof (translation)
Establish `key : YCond K (r` using `r) LL j M * YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j (M + M') := by`. Use `ycond_of_stable LL j _ _ ?_ ?_` and prove the remaining obligations. Use `Submodule.mul_le.2 fun f hf h hh => ?_` and prove the remaining obligations. Establish `h1` using `ycond_le LL j M hf`. Establish `h2` using `ycond_le LL j M' hh`.

Rewrite `h1`, `h2`, the goal using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.1 (support_mul f h (Finset.mem_coe.1 hm))`. Establish `a1 : ((chWt LL j 0 a : ℤ) : WithTop ℤ) ≤ M` using `h1 (Finset.mem_coe.2 ha)`. Establish `a2 : ((chWt LL j 0 b : ℤ) : WithTop ℤ) ≤ M'` using `h2 (Finset.mem_coe.2 hb)`.

Use `show ((chWt LL j 0 (a + b) : ℤ) : WithTop ℤ) ≤ M + M'`. Rewrite using `[chWt_add, WithTop.coe_add]`. Conclude with `add_le_add a1 a2`. Introduce `c d x hx`. Use `Submodule.mul_induction_on hx (fun f hf h hh => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations.

Rewrite using `[glAct_mul']`. Conclude with `Submodule.add_mem _ (Submodule.mul_mem_mul (ycond_stable LL j M c d f hf) hh) (Submodule.mul_mem_mul hf (ycond_stable LL j M' c d h hh))`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Conclude with `key (Submodule.mul_mem_mul hf hh)`.
-/
theorem ycond_mul (LL : ChainLetters N) (j : ℕ) (M M' : WithTop ℤ) {f h : MvPolynomial (Fin N × Fin r) K}
    (hf : f ∈ YCond K (r := r) LL j M) (hh : h ∈ YCond K (r := r) LL j M') :
    f * h ∈ YCond K (r := r) LL j (M + M') := by
  classical
  have key : YCond K (r := r) LL j M * YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j (M + M') := by
    refine ycond_of_stable LL j _ _ ?_ ?_
    · refine Submodule.mul_le.2 fun f hf h hh => ?_
      have h1 := ycond_le LL j M hf
      have h2 := ycond_le LL j M' hh
      rw [MvPolynomial.mem_restrictSupport_iff] at h1 h2 ⊢
      intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f h (Finset.mem_coe.1 hm))
      have a1 : ((chWt LL j 0 a : ℤ) : WithTop ℤ) ≤ M := h1 (Finset.mem_coe.2 ha)
      have a2 : ((chWt LL j 0 b : ℤ) : WithTop ℤ) ≤ M' := h2 (Finset.mem_coe.2 hb)
      show ((chWt LL j 0 (a + b) : ℤ) : WithTop ℤ) ≤ M + M'
      rw [chWt_add, WithTop.coe_add]
      exact add_le_add a1 a2
    · intro c d x hx
      refine Submodule.mul_induction_on hx (fun f hf h hh => ?_) (fun x y hx hy => ?_)
      · rw [glAct_mul']
        exact Submodule.add_mem _ (Submodule.mul_mem_mul (ycond_stable LL j M c d f hf) hh)
          (Submodule.mul_mem_mul hf (ycond_stable LL j M' c d h hh))
      · rw [map_add]
        exact Submodule.add_mem _ hx hy
  exact key (Submodule.mul_mem_mul hf hh)

/- English proof (translation)
Establish `key : Submodule.span K {(1 : MvPolynomial (Fin N × Fin r) K)} ≤ YCond K (r` using `r) LL j ((0 : ℤ) : WithTop ℤ) := by`. Use `ycond_of_stable LL j _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ rfl`. Use `show (1 : MvPolynomial (Fin N × Fin r) K) ∈ MvPolynomial.restrictSupport K _`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hm' : m = 0`. Use `MvPolynomial.mem_support_iff.1 (Finset.mem_coe.1 hm)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.coeff_one]`.

Assume the negation of the conclusion as `h`. Conclude with `this (if_neg (Ne.symm h))`. Substitute `hm'` using the available equality. Use `show ((chWt LL j 0 (0 : Fin N × Fin r →₀ ℕ) : ℤ) : WithTop ℤ) ≤ _`. Simplify using `[chWt]`.

Introduce `c d x hx`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Establish `h1 : glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (1 : MvPolynomial (Fin N × Fin r) K) = 0`. Use `glAct_mul' (K := K) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d 1 1` as an intermediate fact. Simplify using `only [mul_one, one_mul] at this`.

Conclude with `left_eq_add.1 this |>.symm ▸ rfl`. Rewrite using `[map_smul, h1, smul_zero]`. Conclude with `Submodule.zero_mem _`. Conclude with `key (Submodule.subset_span rfl)`.
-/
theorem ycond_one (LL : ChainLetters N) (j : ℕ) : (1 : MvPolynomial (Fin N × Fin r) K) ∈ YCond K (r := r) LL j (0 : ℤ) := by
  classical
  have key : Submodule.span K {(1 : MvPolynomial (Fin N × Fin r) K)} ≤ YCond K (r := r) LL j ((0 : ℤ) : WithTop ℤ) := by
    refine ycond_of_stable LL j _ _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ rfl
      show (1 : MvPolynomial (Fin N × Fin r) K) ∈ MvPolynomial.restrictSupport K _
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      have hm' : m = 0 := by
        have := MvPolynomial.mem_support_iff.1 (Finset.mem_coe.1 hm)
        rw [MvPolynomial.coeff_one] at this
        by_contra h
        exact this (if_neg (Ne.symm h))
      subst hm'
      show ((chWt LL j 0 (0 : Fin N × Fin r →₀ ℕ) : ℤ) : WithTop ℤ) ≤ _
      simp [chWt]
    · intro c d x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have h1 : glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (1 : MvPolynomial (Fin N × Fin r) K) = 0 := by
        have := glAct_mul' (K := K) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d 1 1
        simp only [mul_one, one_mul] at this
        exact left_eq_add.1 this |>.symm ▸ rfl
      rw [map_smul, h1, smul_zero]
      exact Submodule.zero_mem _
  exact key (Submodule.subset_span rfl)

def vWt (LL : ChainLetters N) (j : ℕ) (a : Fin N) : ℕ := if LL.vec a = true ∧ (a : ℕ) < j then 1 else 0

/- English proof (translation)
Establish `key : Submodule.span K (Set.range fun e' : Fin r => (X (a, e') : MvPolynomial (Fin N × Fin r) K)) ≤ YCond K (r` using `r) LL j ((vWt LL j a : ℤ) : WithTop ℤ) := by`. Use `ycond_of_stable LL j _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨e', rfl⟩`. Use `show (X (a, e') : MvPolynomial (Fin N × Fin r) K) ∈ MvPolynomial.restrictSupport K _`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hm' : m = Finsupp.single (a, e') 1`. Use `Finset.mem_coe.1 hm` as an intermediate fact. Rewrite `this` using `[MvPolynomial.support_X]`.

Conclude with `Finset.mem_singleton.1 this`. Substitute `hm'` using the available equality. Use `show ((chWt LL j 0 (Finsupp.single (a, e') 1) : ℤ) : WithTop ℤ) ≤ _`. Rewrite using `[chWt_single, WithTop.coe_le_coe]`. Unfold `vWt`.

Apply the tactic sequence `split_ifs <;> simp_all`. Introduce `c d x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨e', rfl⟩` from `hx`.

Use `show glAct K _ _ c d (X (a, e')) ∈ _`. Rewrite using `[glAct_X']`. Use `split_ifs`. Conclude with `Submodule.subset_span ⟨c, rfl⟩`. Conclude with `Submodule.zero_mem _`.

Conclude with `Submodule.neg_mem _ (Submodule.subset_span ⟨d, rfl⟩)`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul t x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Conclude with `key (Submodule.subset_span ⟨e, rfl⟩)`.
-/
theorem ycond_X (LL : ChainLetters N) (j : ℕ) (a : Fin N) (e : Fin r) :
    (X (a, e) : MvPolynomial (Fin N × Fin r) K) ∈ YCond K (r := r) LL j ((vWt LL j a : ℤ) : WithTop ℤ) := by
  classical
  have key : Submodule.span K (Set.range fun e' : Fin r => (X (a, e') : MvPolynomial (Fin N × Fin r) K)) ≤
      YCond K (r := r) LL j ((vWt LL j a : ℤ) : WithTop ℤ) := by
    refine ycond_of_stable LL j _ _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨e', rfl⟩
      show (X (a, e') : MvPolynomial (Fin N × Fin r) K) ∈ MvPolynomial.restrictSupport K _
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      have hm' : m = Finsupp.single (a, e') 1 := by
        have := Finset.mem_coe.1 hm
        rw [MvPolynomial.support_X] at this
        exact Finset.mem_singleton.1 this
      subst hm'
      show ((chWt LL j 0 (Finsupp.single (a, e') 1) : ℤ) : WithTop ℤ) ≤ _
      rw [chWt_single, WithTop.coe_le_coe]
      unfold vWt
      split_ifs <;> simp_all
    · intro c d x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨e', rfl⟩ := hx
        show glAct K _ _ c d (X (a, e')) ∈ _
        rw [glAct_X']
        split_ifs
        · exact Submodule.subset_span ⟨c, rfl⟩
        · exact Submodule.zero_mem _
        · exact Submodule.neg_mem _ (Submodule.subset_span ⟨d, rfl⟩)
        · exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul t x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key (Submodule.subset_span ⟨e, rfl⟩)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using ycond_one (K := K) LL j`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Use `ycond_mul LL j _ _ ih hf` as an intermediate fact.

Rewrite `this` using `[← WithTop.coe_add]`. Establish `e : (n : ℤ) * z + z = ((n + 1 : ℕ) : ℤ) * z` using `by push_cast; ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem ycond_pow (LL : ChainLetters N) (j : ℕ) (z : ℤ) {f : MvPolynomial (Fin N × Fin r) K}
    (hf : f ∈ YCond K (r := r) LL j (z : WithTop ℤ)) (n : ℕ) :
    f ^ n ∈ YCond K (r := r) LL j (((n : ℤ) * z : ℤ) : WithTop ℤ) := by
  induction n with
  | zero => simpa using ycond_one (K := K) LL j
  | succ n ih =>
    rw [pow_succ]
    have := ycond_mul LL j _ _ ih hf
    rw [← WithTop.coe_add] at this
    have e : (n : ℤ) * z + z = ((n + 1 : ℕ) : ℤ) * z := by push_cast; ring
    rwa [e] at this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ycond_one (K := K) LL j`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, WithTop.coe_add]`. Conclude with `ycond_mul LL j _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
theorem ycond_prod (LL : ChainLetters N) (j : ℕ) {ι : Type} (s : Finset ι) (z : ι → ℤ)
    (f : ι → MvPolynomial (Fin N × Fin r) K) (hf : ∀ i ∈ s, f i ∈ YCond K (r := r) LL j (z i : WithTop ℤ)) :
    ∏ i ∈ s, f i ∈ YCond K (r := r) LL j ((∑ i ∈ s, z i : ℤ) : WithTop ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ycond_one (K := K) LL j
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, WithTop.coe_add]
    exact ycond_mul LL j _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

def tcPairP (K : Type) [CommRing K] {N r : ℕ} (a a' : Fin N) : MvPolynomial (Fin N × Fin r) K := ∑ c, X (a, c) * X (a', c)

def pWt (j : ℕ) (a a' : Fin N) : ℕ := if (a : ℕ) < j ∧ ¬ (a' : ℕ) < j then 1 else 0

/- English proof (translation)
Distinguish the cases in `hboth : (a : ℕ) < j ∧ (a' : ℕ) < j`. Establish `hp : pWt j a a' = 0` using `by unfold pWt; rw [if_neg]; tauto`. Rewrite using `[hp]`. Establish `key : Submodule.span K {tcPairP K (r` using `r) a a'} ≤ YCond K (r := r) LL j (((0 : ℕ) : ℤ) : WithTop ℤ) := by`. Use `ycond_of_stable LL j _ _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ rfl`. Use `show tcPairP K (r := r) a a' ∈ MvPolynomial.restrictSupport K _`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`.

Introduce `m hm`. Take `⟨x, hx, y, hy, rfl⟩` from `Finset.mem_add.1 (support_mul _ _ (Finset.mem_coe.1 hm))`. Rewrite `hx`, `hy` using `[MvPolynomial.support_X]`. Rewrite using `[Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy]`. Use `show ((chWt LL j 0 _ : ℤ) : WithTop ℤ) ≤ _`.

Establish `hv' : ¬ LL.vec a' = true` using `by rw [ha']; exact Bool.false_ne_true`. Rewrite using `[chWt_add, chWt_single, chWt_single, if_pos hboth.1, if_pos hboth.2, if_pos ha, if_neg hv']`. Apply the tactic sequence `by_cases hc : c = 0 <;> simp [hc]`. Introduce `c d x hx`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hx`.

Establish `h0 : glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (tcPairP K (r` using `r) a a') = 0 := by`. Unfold `tcPairP`. Rewrite using `[map_sum]`. Simplify using `only [glAct_mul', glAct_X']`. Establish `m1 : a ∈ {i : Fin N | (i : ℕ) < j}` using `hboth.1`.

Establish `m2 : a' ∈ {i : Fin N | (i : ℕ) < j}` using `hboth.2`. Simplify using `only [if_pos m1, if_pos m2, if_pos ha, ha', Bool.false_eq_true, if_false]`. Rewrite using `[Finset.sum_add_distrib]`. Simplify using `only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_smul, h0, smul_zero]`. Conclude with `Submodule.zero_mem _`. Conclude with `key (Submodule.subset_span rfl)`. Establish `hle : ((vWt LL j a : ℤ) : WithTop ℤ) + ((vWt LL j a' : ℤ) : WithTop ℤ) ≤ ((pWt j a a' : ℤ) : WithTop ℤ)`. Rewrite using `[← WithTop.coe_add, WithTop.coe_le_coe]`.

Unfold `vWt pWt`. Simplify using `only [ha, ha', true_and, Bool.false_eq_true, false_and, if_false]`. Apply the tactic sequence `split_ifs <;> simp_all`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Conclude with `ycond_mono LL j hle (ycond_mul LL j _ _ (ycond_X LL j a c) (ycond_X LL j a' c))`.
-/
theorem ycond_pair (LL : ChainLetters N) (j : ℕ) (a a' : Fin N) (ha : LL.vec a = true) (ha' : LL.vec a' = false) :
    tcPairP K (r := r) a a' ∈ YCond K (r := r) LL j ((pWt j a a' : ℤ) : WithTop ℤ) := by
  classical
  by_cases hboth : (a : ℕ) < j ∧ (a' : ℕ) < j
  · have hp : pWt j a a' = 0 := by unfold pWt; rw [if_neg]; tauto
    rw [hp]
    have key : Submodule.span K {tcPairP K (r := r) a a'} ≤ YCond K (r := r) LL j (((0 : ℕ) : ℤ) : WithTop ℤ) := by
      refine ycond_of_stable LL j _ _ ?_ ?_
      · rw [Submodule.span_le]
        rintro _ rfl
        show tcPairP K (r := r) a a' ∈ MvPolynomial.restrictSupport K _
        refine Submodule.sum_mem _ fun c _ => ?_
        rw [MvPolynomial.mem_restrictSupport_iff]
        intro m hm
        obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul _ _ (Finset.mem_coe.1 hm))
        rw [MvPolynomial.support_X] at hx hy
        rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy]
        show ((chWt LL j 0 _ : ℤ) : WithTop ℤ) ≤ _
        have hv' : ¬ LL.vec a' = true := by rw [ha']; exact Bool.false_ne_true
        rw [chWt_add, chWt_single, chWt_single, if_pos hboth.1, if_pos hboth.2, if_pos ha, if_neg hv']
        by_cases hc : c = 0 <;> simp [hc]
      · intro c d x hx
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
        have h0 : glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (tcPairP K (r := r) a a') = 0 := by
          unfold tcPairP
          rw [map_sum]
          simp only [glAct_mul', glAct_X']
          have m1 : a ∈ {i : Fin N | (i : ℕ) < j} := hboth.1
          have m2 : a' ∈ {i : Fin N | (i : ℕ) < j} := hboth.2
          simp only [if_pos m1, if_pos m2, if_pos ha, ha', Bool.false_eq_true, if_false]
          rw [Finset.sum_add_distrib]
          simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [map_smul, h0, smul_zero]
        exact Submodule.zero_mem _
    exact key (Submodule.subset_span rfl)
  · have hle : ((vWt LL j a : ℤ) : WithTop ℤ) + ((vWt LL j a' : ℤ) : WithTop ℤ) ≤ ((pWt j a a' : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      unfold vWt pWt
      simp only [ha, ha', true_and, Bool.false_eq_true, false_and, if_false]
      split_ifs <;> simp_all
    refine Submodule.sum_mem _ fun c _ => ?_
    exact ycond_mono LL j hle (ycond_mul LL j _ _ (ycond_X LL j a c) (ycond_X LL j a' c))

/- English proof (translation)
Establish `e : (monomial ε (1 : K) : MvPolynomial (Fin N × Fin r) K) = ∏ v : Fin N × Fin r, X v ^ ε v`. Rewrite using `[MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Rewrite using `[e]`. Conclude with `ycond_prod LL j Finset.univ _ _ fun v _ => ycond_pow LL j _ (ycond_X LL j v.1 v.2) (ε v)`.
-/
theorem ycond_monomial (LL : ChainLetters N) (j : ℕ) (ε : Fin N × Fin r →₀ ℕ) :
    (monomial ε (1 : K) : MvPolynomial (Fin N × Fin r) K) ∈
      YCond K (r := r) LL j ((∑ v : Fin N × Fin r, (ε v : ℤ) * (vWt LL j v.1 : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  have e : (monomial ε (1 : K) : MvPolynomial (Fin N × Fin r) K) = ∏ v : Fin N × Fin r, X v ^ ε v := by
    rw [MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [e]
  exact ycond_prod LL j Finset.univ _ _ fun v _ => ycond_pow LL j _ (ycond_X LL j v.1 v.2) (ε v)

end YC

end Formalism.MainNotions.ColumnSystems.Pf
