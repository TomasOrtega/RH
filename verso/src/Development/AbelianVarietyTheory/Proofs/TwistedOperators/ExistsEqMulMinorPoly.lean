import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

/- English proof (translation)
Establish `key : ∀ k, ∑ i ∈ Finset.Ico (a : ℕ) (a + k), (α i - α (i + 1)) + α (a + k) = α a`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[← add_assoc, Finset.sum_Ico_succ_top (by omega)]`. Use `hα (Nat.le_succ (a + k))` as an intermediate fact. Simplify using `only [Nat.succ_eq_add_one] at this`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `key (n - a)`.

Rewrite `h1` using `[show (a : ℕ) + (n - a) = n by have := a.2; omega, h0, add_zero]`. Rewrite using `[← h1]`. Use `Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ici, Fin.le_def]`.

Conclude with `Finset.mem_Ico.2 ⟨hi, i.2⟩`. Introduce `i _ j _ h`. Conclude with `Fin.ext h`. Introduce `b hb`. Rewrite `hb` using `[Finset.mem_Ico]`.

Conclude with `⟨⟨b, hb.2⟩, Finset.mem_Ici.2 (Fin.le_def.2 hb.1), rfl⟩`. Introduce `_ _`. Both sides reduce to the same expression.
-/
theorem sum_Ici_sub_succ {n : ℕ} (α : ℕ → ℕ) (hα : Antitone α) (h0 : α n = 0) (a : Fin n) :
    ∑ i ∈ Finset.Ici a, (α (i : ℕ) - α ((i : ℕ) + 1)) = α a := by
  have key : ∀ k, ∑ i ∈ Finset.Ico (a : ℕ) (a + k), (α i - α (i + 1)) + α (a + k) = α a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have := hα (Nat.le_succ (a + k))
      simp only [Nat.succ_eq_add_one] at this
      omega
  have h1 := key (n - a)
  rw [show (a : ℕ) + (n - a) = n by have := a.2; omega, h0, add_zero] at h1
  rw [← h1]
  refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Ici, Fin.le_def] at hi
    exact Finset.mem_Ico.2 ⟨hi, i.2⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_Ico] at hb
    exact ⟨⟨b, hb.2⟩, Finset.mem_Ici.2 (Fin.le_def.2 hb.1), rfl⟩
  · intro _ _
    rfl

/- English proof (translation)
Distinguish the cases in `hP0 : P = 0`. Conclude with `⟨0, by simp, by simp [hP0]⟩`. Take `⟨hru, hcu, hrw, hcw⟩` from `hP`. Establish `hrow : ∀ a : Fin p, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = α a` using `fun a m hm => by`. Conclude with `(rowOp_eq_smul_iff z a P _).1 (hrw a) m hm` after adjusting the coercions.

Establish `hcol : ∀ k : Fin r, ∀ m ∈ P.support, ∑ a, m (z (a, k)) = α k` using `fun k m hm => by`. Conclude with `(colOp_eq_smul_iff z k P _).1 (hcw k) m hm` after adjusting the coercions. Set `e : Fin (min p r) → Fin p` to `Fin.castLE (min_le_left p r)`. Set `f : Fin (min p r) → Fin r` to `Fin.castLE (min_le_right p r)`. Establish `hei : Function.Injective e` using `Fin.castLE_injective _`.

Establish `hfi : Function.Injective f` using `Fin.castLE_injective _`. Establish `hve : ∀ a k, a ∉ Set.range e → z (a, k) ∉ P.vars`. Introduce `a k ha hv`. Take `⟨m, hm, hv⟩` from `(mem_vars_iff_mem_support _).1 hv`. Establish `h1` using `hrow a m hm`.

Rewrite `h1` using `[h0 a (not_lt.1 fun h' => ha ⟨⟨a, h'⟩, rfl⟩), Finset.sum_eq_zero_iff]`. Conclude with `Finsupp.mem_support_iff.1 hv (h1 k (Finset.mem_univ _))`. Establish `hvf : ∀ a k, k ∉ Set.range f → z (a, k) ∉ P.vars`. Introduce `a k hk hv`. Take `⟨m, hm, hv⟩` from `(mem_vars_iff_mem_support _).1 hv`.

Establish `h1` using `hcol k m hm`. Rewrite `h1` using `[h0 k (not_lt.1 fun h' => hk ⟨⟨k, h'⟩, rfl⟩), Finset.sum_eq_zero_iff]`. Conclude with `Finsupp.mem_support_iff.1 hv (h1 a (Finset.mem_univ _))`. Take `⟨Q, hQ, hPQ⟩` from `eq_mul_prod_minors (fun w : Fin (min p r) × Fin (min p r) => z (e w.1, f w.2)) (hz.comp (hei.prodMap hfi)) P (fun i => α i - α (i + 1)) (fun a m hm => by`. Rewrite using `[sum_Ici_sub_succ α hα (h0 _ le_rfl)]`.

Use `Eq.trans ?_ (hrow (e a) m hm)` and prove the remaining obligations. Use `Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl` and prove the remaining obligations. Assume the negation of the conclusion as `h1`. Conclude with `hvf _ k hk ((mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h1⟩))`. Use the proof step `(fun i j hij => by`.

Establish `h₁` using `(rowOp_apply _ _ _ _).symm.trans (hru (e i) (e j) hij)`. Use `((rowAdd_invariant_iff (fun k => z (e i, f k)) (fun k => z (e j, f k)) (fun k l h => hfi (by simpa using hz h)) (fun k l h => hij.ne (hei (congrArg Prod.fst (hz h)))) P).out 2 1).1 (Eq.trans ?_ h₁)` and prove the remaining obligations. Use `Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl` and prove the remaining obligations. Rewrite using `[pderiv_eq_zero_of_notMem_vars (hvf _ k hk), mul_zero])`. Use the proof step `(fun i j hij => by`.

Establish `h₁` using `(colOp_apply _ _ _ _).symm.trans (hcu (f i) (f j) hij)`. Use `((rowAdd_invariant_iff (fun k => z (e k, f i)) (fun k => z (e k, f j)) (fun k l h => hei (by simpa using hz h)) (fun k l h => hij.ne (hfi (congrArg Prod.snd (hz h)))) P).out 2 1).1 (Eq.trans ?_ h₁)` and prove the remaining obligations. Use `Fintype.sum_of_injective e hei _ _ (fun k hk => ?_) fun _ => rfl` and prove the remaining obligations. Rewrite using `[pderiv_eq_zero_of_notMem_vars (hve k _ hk), mul_zero])`. Establish `hPQ' : P = Q * minorPoly z α` using `hPQ`.

Use `⟨Q, ?_, hPQ'⟩` and prove the remaining obligations. Establish `hsub : ∀ s ∈ Q.vars, s ∈ P.vars`. Introduce `s hs`. Rewrite `hs`, the goal using `[mem_vars_iff_degreeOf_ne_zero]`. Rewrite `hP0`, the goal using `[hPQ']`.

Rewrite using `[degreeOf_mul_eq (left_ne_zero_of_mul hP0) (right_ne_zero_of_mul hP0)]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨a, k⟩ hw`. Distinguish the cases in `ha : a ∈ Set.range e`. Distinguish the cases in `hk : k ∈ Set.range f`.

Take `⟨a, rfl⟩` from `ha`. Take `⟨k, rfl⟩` from `hk`. Conclude with `hQ (a, k) hw`. Conclude with `hvf a k hk (hsub _ hw)`. Conclude with `hve a k ha (hsub _ hw)`.
-/
theorem exists_eq_mul_minorPoly (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (α : ℕ → ℕ) (hα : Antitone α) (h0 : ∀ i, min p r ≤ i → α i = 0)
    (P : MvPolynomial σ ℂ) (hP : BlockHW z α P) :
    ∃ Q : MvPolynomial σ ℂ, (∀ w, z w ∉ Q.vars) ∧ P = Q * minorPoly z α := by
  by_cases hP0 : P = 0
  · exact ⟨0, by simp, by simp [hP0]⟩
  obtain ⟨hru, hcu, hrw, hcw⟩ := hP
  have hrow : ∀ a : Fin p, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = α a := fun a m hm => by
    exact_mod_cast (rowOp_eq_smul_iff z a P _).1 (hrw a) m hm
  have hcol : ∀ k : Fin r, ∀ m ∈ P.support, ∑ a, m (z (a, k)) = α k := fun k m hm => by
    exact_mod_cast (colOp_eq_smul_iff z k P _).1 (hcw k) m hm
  let e : Fin (min p r) → Fin p := Fin.castLE (min_le_left p r)
  let f : Fin (min p r) → Fin r := Fin.castLE (min_le_right p r)
  have hei : Function.Injective e := Fin.castLE_injective _
  have hfi : Function.Injective f := Fin.castLE_injective _
  have hve : ∀ a k, a ∉ Set.range e → z (a, k) ∉ P.vars := by
    intro a k ha hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hrow a m hm
    rw [h0 a (not_lt.1 fun h' => ha ⟨⟨a, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 k (Finset.mem_univ _))
  have hvf : ∀ a k, k ∉ Set.range f → z (a, k) ∉ P.vars := by
    intro a k hk hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hcol k m hm
    rw [h0 k (not_lt.1 fun h' => hk ⟨⟨k, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 a (Finset.mem_univ _))
  obtain ⟨Q, hQ, hPQ⟩ := eq_mul_prod_minors (fun w : Fin (min p r) × Fin (min p r) =>
      z (e w.1, f w.2)) (hz.comp (hei.prodMap hfi)) P (fun i => α i - α (i + 1))
    (fun a m hm => by
      rw [sum_Ici_sub_succ α hα (h0 _ le_rfl)]
      refine Eq.trans ?_ (hrow (e a) m hm)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      by_contra h1
      exact hvf _ k hk ((mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h1⟩))
    (fun i j hij => by
      have h₁ := (rowOp_apply _ _ _ _).symm.trans (hru (e i) (e j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e i, f k)) (fun k => z (e j, f k))
        (fun k l h => hfi (by simpa using hz h))
        (fun k l h => hij.ne (hei (congrArg Prod.fst (hz h)))) P).out 2 1).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hvf _ k hk), mul_zero])
    (fun i j hij => by
      have h₁ := (colOp_apply _ _ _ _).symm.trans (hcu (f i) (f j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e k, f i)) (fun k => z (e k, f j))
        (fun k l h => hei (by simpa using hz h))
        (fun k l h => hij.ne (hfi (congrArg Prod.snd (hz h)))) P).out 2 1).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective e hei _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hve k _ hk), mul_zero])
  have hPQ' : P = Q * minorPoly z α := hPQ
  refine ⟨Q, ?_, hPQ'⟩
  have hsub : ∀ s ∈ Q.vars, s ∈ P.vars := by
    intro s hs
    rw [mem_vars_iff_degreeOf_ne_zero] at hs ⊢
    rw [hPQ'] at hP0 ⊢
    rw [degreeOf_mul_eq (left_ne_zero_of_mul hP0) (right_ne_zero_of_mul hP0)]
    omega
  rintro ⟨a, k⟩ hw
  by_cases ha : a ∈ Set.range e
  · by_cases hk : k ∈ Set.range f
    · obtain ⟨a, rfl⟩ := ha
      obtain ⟨k, rfl⟩ := hk
      exact hQ (a, k) hw
    · exact hvf a k hk (hsub _ hw)
  · exact hve a k ha (hsub _ hw)

end GlobalTheory.JointHarm
