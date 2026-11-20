import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Comm

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Establish `hcomm : ∀ (u v : Fin N × Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]), pderiv u (pderiv v y) = pderiv v (pderiv u y)`. Introduce `u v y`. Use `MvPolynomial.induction_on' y (fun s b => ?_) (fun q q' hq hq' => ?_)` and prove the remaining obligations. Simplify using `only [pderiv_monomial]`. Distinguish the cases in `huv : u = v`.

Substitute `huv` using the available equality. Both sides reduce to the same expression. Establish `h1 : (s - Finsupp.single v 1 : Fin N × Fin r →₀ ℕ) u = s u`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm huv), Nat.sub_zero]`. Establish `h2 : (s - Finsupp.single u 1 : Fin N × Fin r →₀ ℕ) v = s v`.

Rewrite using `[Finsupp.tsub_apply, Finsupp.single_apply, if_neg huv, Nat.sub_zero]`. Rewrite using `[h1, h2, tsub_right_comm, mul_assoc, mul_assoc, mul_comm ((s u : ℚ_[p]))]`. Simplify using `only [map_add, hq, hq']`. Establish `hg : ∀ y, M.glAct p LL J c' d' y = ∑ i : Fin N, (if (i : ℕ) < J then (if LL.vec i then X (i, c') * pderiv (i, d') y else -(X (i, d') * pderiv (i, c') y)) else 0)`. Introduce `y`.

Simplify using `only [M.glAct, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Establish `key : ∀ i : Fin N, pderiv (a, c) (if (i : ℕ) < J then (if LL.vec i then X (i, c') * pderiv (i, d') x else -(X (i, d') * pderiv (i, c') x)) else 0) = (if (i : ℕ) < J then (if LL.vec i then X (i, c') * pderiv (i, d') (pderiv (a, c) x) else -(X (i, d') * pderiv (i, c') (pderiv (a, c …`. Introduce `i`.

Distinguish the cases in `hi : (i : ℕ) < J`. Distinguish the cases in `hv : LL.vec i`. Simplify using `only [hi, hv, if_true, pderiv_mul, pderiv_X, Pi.single_apply]`. Rewrite using `[hcomm (a, c) (i, d') x]`. Distinguish the cases in `hai : a = i`.

Substitute `hai` using the available equality. Distinguish the cases in `hcc : c = c'`. Substitute `hcc` using the available equality. Simplify using the standard rewrite rules. Apply the tactic sequence `try abel`.

Simplify using `[hcc, Ne.symm hcc]`. Establish `hne : (i, c') ≠ (a, c)` using `fun h' => hai (congrArg Prod.fst h').symm`. Simplify using `[hai, hne]`. Simplify using `only [hi, hv, if_true, Bool.false_eq_true, if_false, map_neg, pderiv_mul, pderiv_X, Pi.single_apply]`. Rewrite using `[hcomm (a, c) (i, c') x]`.

Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality. Distinguish the cases in `hcd : c = d'`. Substitute `hcd` using the available equality. Simplify using the standard rewrite rules.

Apply the tactic sequence `try abel`. Simplify using `[hcd, Ne.symm hcd]`. Establish `hne : (i, d') ≠ (a, c)` using `fun h' => hai (congrArg Prod.fst h').symm`. Simplify using `[hai, hne]`. Simplify using `[hi]`.

Rewrite using `[hg, hg, map_sum, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_glAct (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c' d' : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    pderiv (a, c) (M.glAct p LL J c' d' x) = M.glAct p LL J c' d' (pderiv (a, c) x) +
      (if (a : ℕ) < J then
        (if LL.vec a then (if c = c' then pderiv (a, d') x else 0) else (if c = d' then -pderiv (a, c') x else 0))
       else 0) := by
  classical
  have hcomm : ∀ (u v : Fin N × Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      pderiv u (pderiv v y) = pderiv v (pderiv u y) := by
    intro u v y
    refine MvPolynomial.induction_on' y (fun s b => ?_) (fun q q' hq hq' => ?_)
    · simp only [pderiv_monomial]
      by_cases huv : u = v
      · subst huv
        rfl
      · have h1 : (s - Finsupp.single v 1 : Fin N × Fin r →₀ ℕ) u = s u := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm huv), Nat.sub_zero]
        have h2 : (s - Finsupp.single u 1 : Fin N × Fin r →₀ ℕ) v = s v := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg huv, Nat.sub_zero]
        rw [h1, h2, tsub_right_comm, mul_assoc, mul_assoc, mul_comm ((s u : ℚ_[p]))]
    · simp only [map_add, hq, hq']
  have hg : ∀ y, M.glAct p LL J c' d' y = ∑ i : Fin N, (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') y else -(X (i, d') * pderiv (i, c') y)) else 0) := by
    intro y
    simp only [M.glAct, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have key : ∀ i : Fin N, pderiv (a, c) (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') x else -(X (i, d') * pderiv (i, c') x)) else 0) =
      (if (i : ℕ) < J then (if LL.vec i then X (i, c') * pderiv (i, d') (pderiv (a, c) x)
        else -(X (i, d') * pderiv (i, c') (pderiv (a, c) x))) else 0) +
      (if a = i then (if (i : ℕ) < J then (if LL.vec i then (if c = c' then pderiv (i, d') x else 0)
        else (if c = d' then -pderiv (i, c') x else 0)) else 0) else 0) := by
    intro i
    by_cases hi : (i : ℕ) < J
    · by_cases hv : LL.vec i
      · simp only [hi, hv, if_true, pderiv_mul, pderiv_X, Pi.single_apply]
        rw [hcomm (a, c) (i, d') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcc : c = c'
          · subst hcc
            simp
            try abel
          · simp [hcc, Ne.symm hcc]
        · have hne : (i, c') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
      · simp only [hi, hv, if_true, Bool.false_eq_true, if_false, map_neg, pderiv_mul, pderiv_X,
          Pi.single_apply]
        rw [hcomm (a, c) (i, c') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcd : c = d'
          · subst hcd
            simp
            try abel
          · simp [hcd, Ne.symm hcd]
        · have hne : (i, d') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
    · simp [hi]
  rw [hg, hg, map_sum, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq]
  simp

/- English proof (translation)
Introduce `x hx`. Establish `hx'` using `(mem_restrictSupport_iff ℚ_[p]).mp hx`. Rewrite using `[x.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[pderiv_monomial]`.

Distinguish the cases in `hmv : m v = 0`. Simplify using `[hmv]`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m' hm'`. Establish `h1` using `support_monomial_subset hm'`.

Rewrite `h1` using `[Finset.mem_singleton]`. Rewrite using `[h1]`. Conclude with `h m (hx' hm) (Nat.one_le_iff_ne_zero.mpr hmv)`.
-/
theorem pderiv_keep {σ : Type} (v : σ) (Q Q' : Set (σ →₀ ℕ))
    (h : ∀ m ∈ Q, 1 ≤ m v → m - Finsupp.single v 1 ∈ Q') :
    ∀ x ∈ restrictSupport ℚ_[p] Q, pderiv v x ∈ restrictSupport ℚ_[p] Q' := by
  intro x hx
  have hx' := (mem_restrictSupport_iff ℚ_[p]).mp hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmv : m v = 0
  · simp [hmv]
  · rw [mem_restrictSupport_iff]
    intro m' hm'
    have h1 := support_monomial_subset hm'
    rw [Finset.mem_singleton] at h1
    rw [h1]
    exact h m (hx' hm) (Nat.one_le_iff_ne_zero.mpr hmv)

/- English proof (translation)
Establish `key : ∀ i, (((m - Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ)) (i, c0) : ℤ) = (m (i, c0) : ℤ) - (if i = a ∧ c = c0 then 1 else 0)`. Introduce `i`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_apply]`. Distinguish the cases in `hh : i = a ∧ c = c0`. Take `⟨rfl, rfl⟩` from `hh`.

Rewrite using `[if_pos rfl, if_pos ⟨rfl, rfl⟩, Nat.cast_sub h]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg, if_neg hh]`. Simplify using the standard rewrite rules. Introduce `h'`.

Apply `hh` to reduce the goal to its premises. Simplify using `only [Prod.mk.injEq] at h'`. Conclude with `⟨h'.1.symm, h'.2⟩`. Unfold `M.wt`. Simplify using `only [key]`.

Rewrite using `[show (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then (1 : ℤ) else -1) else 0) = ∑ i : Fin N, (if (i : ℕ) < J then (if LL.vec i then (if i = a ∧ c = c0 then (1 : ℤ) else 0) else -(if i = a ∧ c = c0 then 1 else 0)) else 0) from ?_]`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[Finset.sum_eq_single a]`.

Apply the tactic sequence `by_cases h1 : (a : ℕ) < J <;> by_cases h2 : c = c0 <;> by_cases h3 : LL.vec a <;> simp [h1, h2, h3]`. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
theorem wt_sub_single (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c0 : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (h : 1 ≤ m (a, c)) :
    M.wt LL J c0 (m - Finsupp.single (a, c) 1) =
      M.wt LL J c0 m - (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then 1 else -1) else 0) := by
  have key : ∀ i, (((m - Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ)) (i, c0) : ℤ) =
      (m (i, c0) : ℤ) - (if i = a ∧ c = c0 then 1 else 0) := by
    intro i
    rw [Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hh : i = a ∧ c = c0
    · obtain ⟨rfl, rfl⟩ := hh
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, Nat.cast_sub h]
      simp
    · rw [if_neg, if_neg hh]
      · simp
      · intro h'
        apply hh
        simp only [Prod.mk.injEq] at h'
        exact ⟨h'.1.symm, h'.2⟩
  unfold M.wt
  simp only [key]
  rw [show (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then (1 : ℤ) else -1) else 0) =
      ∑ i : Fin N, (if (i : ℕ) < J then (if LL.vec i then (if i = a ∧ c = c0 then (1 : ℤ) else 0)
        else -(if i = a ∧ c = c0 then 1 else 0)) else 0) from ?_]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  · rw [Finset.sum_eq_single a]
    · by_cases h1 : (a : ℕ) < J <;> by_cases h2 : c = c0 <;> by_cases h3 : LL.vec a <;> simp [h1, h2, h3]
    · intro b _ hb
      simp [hb]
    · simp

variable [NeZero r]

/- English proof (translation)
Take `⟨v, d⟩` from `LL`. Take `⟨v', d'⟩` from `LL'`. Simplify using `only at h`. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem ycond_vec (LL LL' : M.Letters N) (h : LL.vec = LL'.vec) (J : ℕ) (Mt : WithTop ℤ) :
    M.YCond p (r := r) LL J Mt = M.YCond p (r := r) LL' J Mt := by
  obtain ⟨v, d⟩ := LL
  obtain ⟨v', d'⟩ := LL'
  simp only at h
  subst h
  rfl

/- English proof (translation)
Take `⟨S', hS'⟩ : ∃ S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]), S' = Submodule.span ℚ_[p] {z | ∃ (c'' : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]), y ∈ M.YCond p (r` from `r) LL J Mt ∧ z = pderiv (a, c'') y} := ⟨_, rfl⟩`. Establish `hgen : ∀ (c'' : Fin r) y, y ∈ M.YCond p (r` using `r) LL J Mt → pderiv (a, c'') y ∈ S' := by`. Introduce `c'' y hy`. Rewrite using `[hS']`. Conclude with `Submodule.subset_span ⟨c'', y, hy, rfl⟩`.

Establish `hsupp : S' ≤ MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt}`. Rewrite using `[hS', Submodule.span_le]`. Introduce and unpack `_ ⟨c'', y, hy, rfl⟩`. Use `pderiv_keep (a, c'') _ _ ?_ y (Formalism.CountingSumsFrames.ycond_le_supp LL J Mt hy)` and prove the remaining obligations. Introduce `m hm h1`.

Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Rewrite using `[wt_sub_single LL J a c'' 0 m h1]`. Use `le_trans (WithTop.coe_le_coe.mpr ?_) hm` and prove the remaining obligations. Distinguish the cases in `ha : (a : ℕ) < J`. Establish `hv` using `hva ha`.

Apply the tactic sequence `by_cases hc : c'' = 0 <;> simp [ha, hv, hc]`. Simplify using `[ha]`. Establish `hstab : M.GlStable p LL J S'`. Introduce `c d z hz`. Rewrite `hz` using `[hS']`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨c'', y, hy, rfl⟩` from `hz`. Establish `e` using `pderiv_glAct LL J a c'' c d y`. Establish `hy' : M.glAct p LL J c d y ∈ M.YCond p (r` using `r) LL J Mt := Formalism.CountingSumsFrames.ycond_glStable LL J Mt c d y hy`.

Establish `hext : (if (a : ℕ) < J then (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0) else (if c'' = d then -pderiv (a, c) y else 0)) else 0) ∈ S'` using `by split_ifs`. Conclude with `hgen d y hy`. Conclude with `S'.zero_mem`. Conclude with `S'.neg_mem (hgen c y hy)`. Conclude with `S'.zero_mem`.

Conclude with `S'.zero_mem`. Rewrite using `[show M.glAct p LL J c d (pderiv (a, c'') y) = pderiv (a, c'') (M.glAct p LL J c d y) - (if (a : ℕ) < J then (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0) else (if c'' = d then -pderiv (a, c) y else 0)) else 0) by rw [e]; abel]`. Conclude with `S'.sub_mem (hgen c'' _ hy') hext`. Consider the case `zero => simp`. Consider the case `add z z' _ _ hz hz'`.

Rewrite using `[map_add]`. Conclude with `S'.add_mem hz hz'`. Consider the case `smul t z _ hz`. Rewrite using `[map_smul]`. Conclude with `S'.smul_mem t hz`.

Establish `hle : S' ≤ M.YCond p (r` using `r) LL J Mt := by`. Unfold `M.YCond`. Conclude with `le_sSup ⟨hsupp, hstab⟩`. Conclude with `hle (hgen c x hx)`.
-/
theorem pderiv_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (a : Fin N) (hva : (a : ℕ) < J → LL.vec a = true)
    (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    pderiv (a, c) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  obtain ⟨S', hS'⟩ : ∃ S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]),
      S' = Submodule.span ℚ_[p] {z | ∃ (c'' : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
        y ∈ M.YCond p (r := r) LL J Mt ∧ z = pderiv (a, c'') y} := ⟨_, rfl⟩
  have hgen : ∀ (c'' : Fin r) y, y ∈ M.YCond p (r := r) LL J Mt → pderiv (a, c'') y ∈ S' := by
    intro c'' y hy
    rw [hS']
    exact Submodule.subset_span ⟨c'', y, hy, rfl⟩
  have hsupp : S' ≤ MvPolynomial.restrictSupport ℚ_[p]
      {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [hS', Submodule.span_le]
    rintro _ ⟨c'', y, hy, rfl⟩
    refine pderiv_keep (a, c'') _ _ ?_ y (Formalism.CountingSumsFrames.ycond_le_supp LL J Mt hy)
    intro m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [wt_sub_single LL J a c'' 0 m h1]
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    by_cases ha : (a : ℕ) < J
    · have hv := hva ha
      by_cases hc : c'' = 0 <;> simp [ha, hv, hc]
    · simp [ha]
  have hstab : M.GlStable p LL J S' := by
    intro c d z hz
    rw [hS'] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c'', y, hy, rfl⟩ := hz
      have e := pderiv_glAct LL J a c'' c d y
      have hy' : M.glAct p LL J c d y ∈ M.YCond p (r := r) LL J Mt :=
        Formalism.CountingSumsFrames.ycond_glStable LL J Mt c d y hy
      have hext : (if (a : ℕ) < J then
          (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) ∈ S' := by
        split_ifs
        · exact hgen d y hy
        · exact S'.zero_mem
        · exact S'.neg_mem (hgen c y hy)
        · exact S'.zero_mem
        · exact S'.zero_mem
      rw [show M.glAct p LL J c d (pderiv (a, c'') y) = pderiv (a, c'') (M.glAct p LL J c d y) -
        (if (a : ℕ) < J then (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) by rw [e]; abel]
      exact S'.sub_mem (hgen c'' _ hy') hext
    | zero => simp
    | add z z' _ _ hz hz' =>
      rw [map_add]
      exact S'.add_mem hz hz'
    | smul t z _ hz =>
      rw [map_smul]
      exact S'.smul_mem t hz
  have hle : S' ≤ M.YCond p (r := r) LL J Mt := by
    unfold M.YCond
    exact le_sSup ⟨hsupp, hstab⟩
  exact hle (hgen c x hx)

/- English proof (translation)
Establish `ht : ∀ y : MvPolynomial (Fin N × Fin r) ℚ_[p], tieF (fun c => (W, c)) (fun c => (E, c)) y = ∑ c0 : Fin r, pderiv (W, c0) (pderiv (E, c0) y)`. Introduce `y`. Simplify using `[tieF, LinearMap.sum_apply]`. Use `Formalism.CountingSumsFrames.ycond_keep LL J Mt (tieF (fun c => (W, c)) (fun c => (E, c))) ?_ ?_ x hx` and prove the remaining obligations. Introduce `c d y`.

Establish `step : ∀ c0, pderiv (W, c0) (pderiv (E, c0) (M.glAct p LL J c d y)) = M.glAct p LL J c d (pderiv (W, c0) (pderiv (E, c0) y)) + (if c0 = c then pderiv (W, d) (pderiv (E, c0) y) else 0) + (if c0 = d then -pderiv (W, c0) (pderiv (E, c) y) else 0)`. Introduce `c0`. Rewrite using `[pderiv_glAct LL J E c0 c d y, map_add, pderiv_glAct LL J W c0 c d (pderiv (E, c0) y)]`. Simplify using `only [hE, hW, hvW, hvE, if_true, Bool.false_eq_true, if_false]`. Apply the tactic sequence `split_ifs <;> simp [map_neg]`.

Rewrite using `[ht, ht, map_sum, Finset.sum_congr rfl (fun c0 _ => step c0), Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']`. Simplify using `only [Finset.mem_univ, if_true, add_assoc, add_neg_cancel, add_zero]`. Introduce `z hz`. Rewrite using `[ht]`. Use `Submodule.sum_mem _ fun c0 _ => ?_` and prove the remaining obligations.

Establish `hQ1 : pderiv (E, c0) z ∈ MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | (((M.wt LL J 0 m - (if c0 = 0 then 1 else 0) : ℤ)) : WithTop ℤ) ≤ Mt}`. Use `pderiv_keep (E, c0) {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} _ ?_ z hz` and prove the remaining obligations. Introduce `m hm h1`. Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Rewrite using `[wt_sub_single LL J E c0 0 m h1]`.

Apply the tactic sequence `by_cases hc : c0 = 0 <;> simpa [hE, hvE, hc] using hm`. Use `pderiv_keep (W, c0) _ {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} ?_ _ hQ1` and prove the remaining obligations. Introduce `m hm h1`. Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Rewrite using `[wt_sub_single LL J W c0 0 m h1]`.

Apply the tactic sequence `by_cases hc : c0 = 0 <;> simpa [hW, hvW, hc] using hm`.
-/
theorem tieF_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (W E : Fin N) (hW : (W : ℕ) < J) (hE : (E : ℕ) < J)
    (hvW : LL.vec W = true) (hvE : LL.vec E = false)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    tieF (fun c => (W, c)) (fun c => (E, c)) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  have ht : ∀ y : MvPolynomial (Fin N × Fin r) ℚ_[p], tieF (fun c => (W, c)) (fun c => (E, c)) y =
      ∑ c0 : Fin r, pderiv (W, c0) (pderiv (E, c0) y) := by
    intro y
    simp [tieF, LinearMap.sum_apply]
  refine Formalism.CountingSumsFrames.ycond_keep LL J Mt (tieF (fun c => (W, c)) (fun c => (E, c))) ?_ ?_ x hx
  · intro c d y
    have step : ∀ c0, pderiv (W, c0) (pderiv (E, c0) (M.glAct p LL J c d y)) =
        M.glAct p LL J c d (pderiv (W, c0) (pderiv (E, c0) y)) +
        (if c0 = c then pderiv (W, d) (pderiv (E, c0) y) else 0) +
        (if c0 = d then -pderiv (W, c0) (pderiv (E, c) y) else 0) := by
      intro c0
      rw [pderiv_glAct LL J E c0 c d y, map_add, pderiv_glAct LL J W c0 c d (pderiv (E, c0) y)]
      simp only [hE, hW, hvW, hvE, if_true, Bool.false_eq_true, if_false]
      split_ifs <;> simp [map_neg]
    rw [ht, ht, map_sum, Finset.sum_congr rfl (fun c0 _ => step c0), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, add_assoc, add_neg_cancel, add_zero]
  · intro z hz
    rw [ht]
    refine Submodule.sum_mem _ fun c0 _ => ?_
    have hQ1 : pderiv (E, c0) z ∈ MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ |
        (((M.wt LL J 0 m - (if c0 = 0 then 1 else 0) : ℤ)) : WithTop ℤ) ≤ Mt} := by
      refine pderiv_keep (E, c0) {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} _ ?_ z hz
      intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J E c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hE, hvE, hc] using hm
    refine pderiv_keep (W, c0) _ {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} ?_ _ hQ1
    · intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J W c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hW, hvW, hc] using hm

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
