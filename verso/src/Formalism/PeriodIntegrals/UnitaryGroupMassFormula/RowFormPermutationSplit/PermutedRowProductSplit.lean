import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Development
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmRowForm

def pF {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n)
    (x : Fin t → ℂ) (σ τ : Equiv.Perm (Fin t)) (k : Fin t) : A :=
  Tm E (x k) (a (σ k)) (b (τ k))

def pε {A : Type*} [Ring A] {t : ℕ} (σ τ : Equiv.Perm (Fin t)) : A :=
  (((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : A)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dblAlt_eq {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (x : Fin t → ℂ) :
    doubleRowFormSum E a b x = ∑ σ : Equiv.Perm (Fin t), ∑ τ : Equiv.Perm (Fin t),
      pε σ τ * (List.ofFn (pF E a b x σ τ)).prod := rfl

/- English proof (translation)
Establish `cen : ∀ (u : ℂ) (p q : Fin n) (z : A), (if p = q then algebraMap ℂ A u else 0) * z = z * (if p = q then algebraMap ℂ A u else 0)`. Introduce `u p q z`. Use `split_ifs`. Conclude with `Algebra.commutes u z`. Simplify using the standard rewrite rules.

Unfold `Tm`. Establish `h1` using `cen x a b (E c d)`. Establish `h2` using `cen y c d (E a b)`. Establish `h3` using `cen x a b (if c = d then algebraMap ℂ A y else 0)`. Generalize the expression as in `(if a = b then algebraMap ℂ A x else 0) = c1 at h1 h3 ⊢`.

Generalize the expression as in `(if c = d then algebraMap ℂ A y else 0) = c2 at h2 h3 ⊢`. Simplify using `only [add_mul, mul_add]`. Rewrite using `[h1, h2, h3]`. Normalize the expressions using the abelian group laws.
-/
theorem perm_Tm_comm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x y : ℂ)
    (a b c d : Fin n) :
    Tm E x a b * Tm E y c d - Tm E y c d * Tm E x a b = E a b * E c d - E c d * E a b := by
  have cen : ∀ (u : ℂ) (p q : Fin n) (z : A),
      (if p = q then algebraMap ℂ A u else 0) * z = z * (if p = q then algebraMap ℂ A u else 0) := by
    intro u p q z
    split_ifs
    · exact Algebra.commutes u z
    · simp
  unfold Tm
  have h1 := cen x a b (E c d)
  have h2 := cen y c d (E a b)
  have h3 := cen x a b (if c = d then algebraMap ℂ A y else 0)
  generalize (if a = b then algebraMap ℂ A x else 0) = c1 at h1 h3 ⊢
  generalize (if c = d then algebraMap ℂ A y else 0) = c2 at h2 h3 ⊢
  simp only [add_mul, mul_add]
  rw [h1, h2, h3]
  abel

/- English proof (translation)
Apply `Equiv.swap_apply_of_ne_of_ne` to reduce the goal to its premises. Introduce `h`. Apply `h1` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Introduce `h`. Apply `h2` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem perm_fix {m : ℕ} (i : Fin m) (k : Fin (m + 1)) (h1 : (k : ℕ) ≠ i) (h2 : (k : ℕ) ≠ (i : ℕ) + 1) :
    Equiv.swap i.castSucc i.succ k = k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    apply h1
    rw [h]
    simp
  · intro h
    apply h2
    rw [h]
    simp

/- English proof (translation)
Apply the tactic sequence `have h0 : (i : ℕ) < (List.ofFn F).length := by simp <;> omega`. Apply the tactic sequence `have h1 : (i : ℕ) + 1 < (List.ofFn F).length := by simp <;> omega`. Use `conv_lhs => rw [← List.take_append_drop (i : ℕ) (List.ofFn F)]`. Rewrite using `[List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]`. Simplify using `only [List.prod_append, List.prod_cons, List.getElem_ofFn, mul_assoc]`.

Both sides reduce to the same expression.
-/
private lemma sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul {A : Type*} [Ring A] {m : ℕ} (F : Fin (m + 1) → A) (i : Fin m) :
    (List.ofFn F).prod = ((List.ofFn F).take (i : ℕ)).prod * (F i.castSucc * F i.succ) *
      ((List.ofFn F).drop ((i : ℕ) + 2)).prod := by
  have h0 : (i : ℕ) < (List.ofFn F).length := by simp <;> omega
  have h1 : (i : ℕ) + 1 < (List.ofFn F).length := by simp <;> omega
  conv_lhs => rw [← List.take_append_drop (i : ℕ) (List.ofFn F)]
  rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]
  simp only [List.prod_append, List.prod_cons, List.getElem_ofFn, mul_assoc]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `List.ext_getElem (by simp)` to reduce the goal to its premises. Introduce `j hj1 hj2`. Simplify using `only [List.getElem_take, List.getElem_ofFn]`. Apply the tactic sequence `apply h <;> simp at hj1 ⊢ <;> omega`.

Apply `List.ext_getElem (by simp)` to reduce the goal to its premises. Introduce `j hj1 hj2`. Simplify using `only [List.getElem_drop, List.getElem_ofFn]`. Apply the tactic sequence `apply h <;> simp <;> omega`.
-/
private lemma ofFn_take_drop_eq_of_eq_off_pair {A : Type*} {m : ℕ} (F G : Fin (m + 1) → A) (i : Fin m)
    (h : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 → F k = G k) :
    (List.ofFn F).take (i : ℕ) = (List.ofFn G).take (i : ℕ) ∧
      (List.ofFn F).drop ((i : ℕ) + 2) = (List.ofFn G).drop ((i : ℕ) + 2) := by
  constructor
  · apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h <;> simp at hj1 ⊢ <;> omega
  · apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp only [List.getElem_drop, List.getElem_ofFn]
    apply h <;> simp <;> omega

/- English proof (translation)
Rewrite using `[sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul F i, sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (F ∘ Equiv.swap i.castSucc i.succ) i]`. Take `⟨ht, hd⟩` from `ofFn_take_drop_eq_of_eq_off_pair (F ∘ Equiv.swap i.castSucc i.succ) F i (fun k h1 h2 => by simp [perm_fix i k h1 h2])`. Rewrite using `[ht, hd]`. Simplify using `only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Use `noncomm_ring`.
-/
theorem perm_split_swap {A : Type*} [Ring A] {m : ℕ} (F : Fin (m + 1) → A) (i : Fin m) :
    (List.ofFn F).prod - (List.ofFn (F ∘ Equiv.swap i.castSucc i.succ)).prod =
      ((List.ofFn F).take (i : ℕ)).prod * (F i.castSucc * F i.succ - F i.succ * F i.castSucc) *
        ((List.ofFn F).drop ((i : ℕ) + 2)).prod := by
  rw [sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul F i, sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (F ∘ Equiv.swap i.castSucc i.succ) i]
  obtain ⟨ht, hd⟩ := ofFn_take_drop_eq_of_eq_off_pair (F ∘ Equiv.swap i.castSucc i.succ) F i
    (fun k h1 h2 => by simp [perm_fix i k h1 h2])
  rw [ht, hd]
  simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  noncomm_ring

def pL {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n)
    (x : Fin (m + 1) → ℂ) (i : Fin m) (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  ((List.ofFn (pF E a b x σ τ)).take (i : ℕ)).prod

def pR {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n)
    (x : Fin (m + 1) → ℂ) (i : Fin m) (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  ((List.ofFn (pF E a b x σ τ)).drop ((i : ℕ) + 2)).prod

def permutedRowProductSplitSum {A : Type*} [Ring A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n) (i : Fin m)
    (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  if b (τ i.castSucc) = a (σ i.succ) then E (a (σ i.castSucc)) (b (τ i.succ)) else 0

def permutedRowProductSplit {A : Type*} [Ring A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n) (i : Fin m)
    (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  if b (τ i.succ) = a (σ i.castSucc) then E (a (σ i.succ)) (b (τ i.castSucc)) else 0

/- English proof (translation)
Use `set s := Equiv.swap i.castSucc i.succ with hs`. Establish `hu : ((Equiv.Perm.sign s : ℤ) * (Equiv.Perm.sign s : ℤ)) = 1`. Rewrite using `[← Units.val_mul, Int.units_mul_self, Units.val_one]`. Establish `hε : ∀ σ τ : Equiv.Perm (Fin (m + 1)), (pε (σ * s) (τ * s) : A) = pε σ τ`. Introduce `σ τ`.

Unfold `pε`. Use `congr 1`. Rewrite using `[Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Units.val_mul, Units.val_mul]`. Take the linear combination `((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ)) * hu`. Establish `hagree : ∀ σ τ : Equiv.Perm (Fin (m + 1)), ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 → pF E a b x (σ * s) (τ * s) k = pF E a b x σ τ k`.

Introduce `σ τ k h1 h2`. Simplify using `only [pF, Equiv.Perm.mul_apply, hs, perm_fix i k h1 h2]`. Establish `hL : ∀ σ τ, pL E a b x i (σ * s) (τ * s) = pL E a b x i σ τ`. Introduce `σ τ`. Unfold `pL`.

Rewrite using `[(ofFn_take_drop_eq_of_eq_off_pair _ _ i (hagree σ τ)).1]`. Establish `hR : ∀ σ τ, pR E a b x i (σ * s) (τ * s) = pR E a b x i σ τ`. Introduce `σ τ`. Unfold `pR`. Rewrite using `[(ofFn_take_drop_eq_of_eq_off_pair _ _ i (hagree σ τ)).2]`.

Establish `hX : ∀ σ τ, permutedRowProductSplitSum E a b i (σ * s) (τ * s) = permutedRowProductSplit E a b i σ τ`. Introduce `σ τ`. Simplify using `only [permutedRowProductSplitSum, permutedRowProductSplit, Equiv.Perm.mul_apply, hs, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Establish `h1 : doubleRowFormSum E a b (x ∘ s) = ∑ σ, ∑ τ, pε σ τ * (List.ofFn (pF E a b x σ τ ∘ s)).prod`. Rewrite using `[dblAlt_eq, ← Equiv.sum_comp (Equiv.mulRight s)]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight s)]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[hε]`.

Both sides reduce to the same expression. Establish `h2 : ∀ σ τ, (List.ofFn (pF E a b x σ τ)).prod - (List.ofFn (pF E a b x σ τ ∘ s)).prod = pL E a b x i σ τ * (permutedRowProductSplitSum E a b i σ τ - permutedRowProductSplit E a b i σ τ) * pR E a b x i σ τ`. Introduce `σ τ`. Rewrite using `[hs, perm_split_swap]`. Unfold `pL pR`.

Use `congr 2`. Simplify using `only [pF]`. Rewrite using `[perm_Tm_comm, hE]`. Both sides reduce to the same expression. Establish `h3 : ∑ σ, ∑ τ, pε σ τ * (pL E a b x i σ τ * permutedRowProductSplitSum E a b i σ τ * pR E a b x i σ τ) = ∑ σ, ∑ τ, pε σ τ * (pL E a b x i σ τ * permutedRowProductSplit E a b i σ τ * pR E a b x i σ τ)`.

Rewrite using `[← Equiv.sum_comp (Equiv.mulRight s)]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight s)]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight]`.

Rewrite using `[hε, hL, hR, hX]`. Rewrite using `[h1, dblAlt_eq]`. Use `symm`. Rewrite using `[← sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, h2]`.

Use `noncomm_ring`. Use `_ = 0 := by`. Simplify using `only [Finset.sum_sub_distrib]`. Rewrite using `[h3, sub_self]`.
-/
theorem perm_swap {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (x : Fin (m + 1) → ℂ) (i : Fin m) :
    doubleRowFormSum E a b (x ∘ Equiv.swap i.castSucc i.succ) = doubleRowFormSum E a b x := by
  set s := Equiv.swap i.castSucc i.succ with hs
  have hu : ((Equiv.Perm.sign s : ℤ) * (Equiv.Perm.sign s : ℤ)) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hε : ∀ σ τ : Equiv.Perm (Fin (m + 1)), (pε (σ * s) (τ * s) : A) = pε σ τ := by
    intro σ τ
    unfold pε
    congr 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Units.val_mul, Units.val_mul]
    linear_combination ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ)) * hu
  have hagree : ∀ σ τ : Equiv.Perm (Fin (m + 1)), ∀ k : Fin (m + 1), (k : ℕ) ≠ i →
      (k : ℕ) ≠ (i : ℕ) + 1 → pF E a b x (σ * s) (τ * s) k = pF E a b x σ τ k := by
    intro σ τ k h1 h2
    simp only [pF, Equiv.Perm.mul_apply, hs, perm_fix i k h1 h2]
  have hL : ∀ σ τ, pL E a b x i (σ * s) (τ * s) = pL E a b x i σ τ := by
    intro σ τ
    unfold pL
    rw [(ofFn_take_drop_eq_of_eq_off_pair _ _ i (hagree σ τ)).1]
  have hR : ∀ σ τ, pR E a b x i (σ * s) (τ * s) = pR E a b x i σ τ := by
    intro σ τ
    unfold pR
    rw [(ofFn_take_drop_eq_of_eq_off_pair _ _ i (hagree σ τ)).2]
  have hX : ∀ σ τ, permutedRowProductSplitSum E a b i (σ * s) (τ * s) = permutedRowProductSplit E a b i σ τ := by
    intro σ τ
    simp only [permutedRowProductSplitSum, permutedRowProductSplit, Equiv.Perm.mul_apply, hs, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have h1 : doubleRowFormSum E a b (x ∘ s) =
      ∑ σ, ∑ τ, pε σ τ * (List.ofFn (pF E a b x σ τ ∘ s)).prod := by
    rw [dblAlt_eq, ← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hε]
    rfl
  have h2 : ∀ σ τ, (List.ofFn (pF E a b x σ τ)).prod - (List.ofFn (pF E a b x σ τ ∘ s)).prod =
      pL E a b x i σ τ * (permutedRowProductSplitSum E a b i σ τ - permutedRowProductSplit E a b i σ τ) * pR E a b x i σ τ := by
    intro σ τ
    rw [hs, perm_split_swap]
    unfold pL pR
    congr 2
    simp only [pF]
    rw [perm_Tm_comm, hE]
    rfl
  have h3 : ∑ σ, ∑ τ, pε σ τ * (pL E a b x i σ τ * permutedRowProductSplitSum E a b i σ τ * pR E a b x i σ τ) =
      ∑ σ, ∑ τ, pε σ τ * (pL E a b x i σ τ * permutedRowProductSplit E a b i σ τ * pR E a b x i σ τ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hε, hL, hR, hX]
  rw [h1, dblAlt_eq]
  symm
  rw [← sub_eq_zero]
  calc (∑ σ, ∑ τ, pε σ τ * (List.ofFn (pF E a b x σ τ)).prod) -
        ∑ σ, ∑ τ, pε σ τ * (List.ofFn (pF E a b x σ τ ∘ s)).prod
      = ∑ σ, ∑ τ, (pε σ τ * (pL E a b x i σ τ * permutedRowProductSplitSum E a b i σ τ * pR E a b x i σ τ) -
          pε σ τ * (pL E a b x i σ τ * permutedRowProductSplit E a b i σ τ * pR E a b x i σ τ)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← mul_sub, h2]
        noncomm_ring
    _ = 0 := by
        simp only [Finset.sum_sub_distrib]
        rw [h3, sub_self]

/- English proof (translation)
Introduce `A _ _ n t E hE a b x π`. Break down `t with _ | m` into its components or cases. Establish `hx : x ∘ π = x` using `funext fun k => k.elim0`. Rewrite using `[hx]`. Establish `hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)`.

Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ]`. Conclude with `Submonoid.mem_top π`. Use `revert x`. Proceed by induction on `hπ using Submonoid.closure_induction with`. Consider the case `mem π h`.

Take `⟨i, rfl⟩` from `h`. Introduce `x`. Conclude with `perm_swap E hE a b x i`. Consider the case `one`. Introduce `x`.

Both sides reduce to the same expression. Consider the case `mul π1 π2 _ _ ih1 ih2`. Introduce `x`. Establish `hc : x ∘ ⇑(π1 * π2) = (x ∘ ⇑π1) ∘ ⇑π2` using `rfl`. Rewrite using `[hc, ih2, ih1]`.
-/
theorem double_row_permutation : DblPerm := by
  intro A _ _ n t E hE a b x π
  rcases t with _ | m
  · have hx : x ∘ π = x := funext fun k => k.elim0
    rw [hx]
  · have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top π
    revert x
    induction hπ using Submonoid.closure_induction with
    | mem π h =>
      obtain ⟨i, rfl⟩ := h
      intro x
      exact perm_swap E hE a b x i
    | one =>
      intro x
      rfl
    | mul π1 π2 _ _ ih1 ih2 =>
      intro x
      have hc : x ∘ ⇑(π1 * π2) = (x ∘ ⇑π1) ∘ ⇑π2 := rfl
      rw [hc, ih2, ih1]

end PI.UnitaryGroupMassFormula.QmRowForm
