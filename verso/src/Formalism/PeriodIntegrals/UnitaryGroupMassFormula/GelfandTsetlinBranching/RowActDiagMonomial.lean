import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFEqSumOfSubsetB

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def wnB (n N : ℕ) : Fin N × Fin N → (Fin n → ℕ) :=
  fun v => if hv : v.1.1 < n then Pi.single (⟨v.1.1, hv⟩ : Fin n) 1 else 0

def prowB (n N : ℕ) (a : Fin N) : ℕ := if a.1 < n then n - a.1 else 0

def psiB (n N : ℕ) : Fin N × Fin N → ℕ := fun v => prowB n N v.1

def PsiB (n : ℕ) : (Fin n → ℕ) →+ ℕ where
  toFun m := ∑ j, (n - j.1) * m j
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem PsiB_apply (n : ℕ) (m : Fin n → ℕ) : PsiB n m = ∑ j, (n - j.1) * m j := rfl

/- English proof (translation)
Unfold `wnB psiB prowB`. Use `split_ifs with hv`. Rewrite using `[PsiB_apply]`. Simplify using `[Pi.single_apply]`. Simplify using the standard rewrite rules.
-/
theorem PsiB_wnB (n N : ℕ) (v : Fin N × Fin N) : PsiB n (wnB n N v) = psiB n N v := by
  unfold wnB psiB prowB
  split_ifs with hv
  · rw [PsiB_apply]
    simp [Pi.single_apply]
  · simp

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, PsiB_wnB]`.
-/
theorem weight_psiB (n N : ℕ) (e : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (psiB n N) e = PsiB n (Finsupp.weight (wnB n N) e) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_nsmul, PsiB_wnB]

def chiB {n : ℕ} (t : Fin n → ℂ) (m : Fin n → ℕ) : ℂ := ∏ j, t j ^ m j

/- English proof (translation)
Simplify using `[chiB, pow_add, Finset.prod_mul_distrib]`.
-/
theorem chiB_add {n : ℕ} (t : Fin n → ℂ) (a b : Fin n → ℕ) : chiB t (a + b) = chiB t a * chiB t b := by
  simp [chiB, pow_add, Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `only [chiB, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]`.
-/
theorem chiB_smul {n : ℕ} (t : Fin n → ℂ) (k : ℕ) (a : Fin n → ℕ) : chiB t (k • a) = chiB t a ^ k := by
  simp only [chiB, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]

/- English proof (translation)
Simplify using `[chiB]`.
-/
theorem chiB_zero {n : ℕ} (t : Fin n → ℂ) : chiB t 0 = 1 := by simp [chiB]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum]`. Proceed by induction on `e.support using Finset.cons_induction with`. Consider the case `empty => simp [chiB_zero]`. Consider the case `cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, chiB_add, chiB_smul, ih]`.
-/
theorem chiB_weight {n : ℕ} {σ : Type*} (t : Fin n → ℂ) (w : σ → (Fin n → ℕ)) (e : σ →₀ ℕ) :
    chiB t (Finsupp.weight w e) = ∏ v ∈ e.support, chiB t (w v) ^ e v := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  induction e.support using Finset.cons_induction with
  | empty => simp [chiB_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, chiB_add, chiB_smul, ih]

def dB (n N : ℕ) (t : Fin n → ℂ) : Fin N → ℂ := fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1

/- English proof (translation)
Unfold `wnB dB`. Use `split_ifs with hv`. Unfold `chiB`. Rewrite using `[Finset.prod_eq_single (⟨v.1.1, hv⟩ : Fin n)]`. Simplify using the standard rewrite rules.

Introduce `j _ hj`. Simplify using `[Pi.single_apply, hj]`. Simplify using the standard rewrite rules. Simplify using `[chiB]`.
-/
theorem chiB_wnB {n N : ℕ} (t : Fin n → ℂ) (v : Fin N × Fin N) : chiB t (wnB n N v) = dB n N t v.1 := by
  unfold wnB dB
  split_ifs with hv
  · unfold chiB
    rw [Finset.prod_eq_single (⟨v.1.1, hv⟩ : Fin n)]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  · simp [chiB]

/- English proof (translation)
Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.diagonal_apply]`. Rewrite using `[Finset.sum_eq_single v.1]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
theorem rowAct_diag_X {N : ℕ} (d : Fin N → ℂ) (v : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal d) (X v) = C (d v.1) * X v := by
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/- English proof (translation)
Establish `hC : Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `N) (Matrix.diagonal (dB n N t)) (C c) = C c := by`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct]`. Rewrite using `[chiB_weight, monomial_eq, map_mul, hC, Finsupp.prod, map_prod]`. Simplify using `only [map_pow, rowAct_diag_X, mul_pow, Finset.prod_mul_distrib, chiB_wnB]`. Rewrite using `[smul_eq_C_mul, map_prod]`.

Simplify using `only [C_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowAct_diag_monomial {n N : ℕ} (t : Fin n → ℂ) (e : Fin N × Fin N →₀ ℕ) (c : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (monomial e c) =
      chiB t (Finsupp.weight (wnB n N) e) • monomial e c := by
  have hC : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (C c) = C c := by
    simp [Formalism.GradedWeylDivisibility.rowAct]
  rw [chiB_weight, monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow, rowAct_diag_X, mul_pow, Finset.prod_mul_distrib, chiB_wnB]
  rw [smul_eq_C_mul, map_prod]
  simp only [C_pow]
  ring

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Rewrite using `[rowAct_diag_monomial, hg (mem_support_iff.mp he)]`.
-/
theorem rowAct_diag_homog {n N : ℕ} (t : Fin n → ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ)
    (hg : IsWeightedHomogeneous (wnB n N) g m) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) g = chiB t m • g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [rowAct_diag_monomial, hg (mem_support_iff.mp he)]

/- English proof (translation)
Use extensionality with `e`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_weightedHomogeneousComponent]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Conclude with `h (hF e (mem_support_iff.mpr (Ne.symm hne)))`.
-/
theorem comp_sum_B {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ)
    (F : Finset M) (hF : ∀ e ∈ f.support, Finsupp.weight w e ∈ F) :
    ∑ m ∈ F, weightedHomogeneousComponent w m f = f := by
  ext e
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hF e (mem_support_iff.mpr (Ne.symm hne)))

/- English proof (translation)
Use extensionality with `e`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_zero]`. Use `split_ifs with h`. Assume the negation of the conclusion as `hne`. Conclude with `hm e (mem_support_iff.mpr hne) h`.

Both sides reduce to the same expression.
-/
theorem comp_zero_B {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ) (m : M)
    (hm : ∀ e ∈ f.support, Finsupp.weight w e ≠ m) : weightedHomogeneousComponent w m f = 0 := by
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hne
    exact hm e (mem_support_iff.mpr hne) h
  · rfl

/- English proof (translation)
Introduce `F`. Proceed by induction on `F using Finset.strongInduction with`. Consider the case `H F ih`. Introduce `y hy hs i0 hi0`. Distinguish the cases in `hall : ∀ i ∈ F, i = i0`.

Establish `hF : F = {i0}`. Use extensionality with `i`. Simplify using `only [Finset.mem_singleton]`. Conclude with `⟨hall i, fun e => e ▸ hi0⟩`. Rewrite `hs` using `[hF, Finset.sum_singleton]`.

Conclude with `hs`. Use `push_neg at hall`. Take `⟨i1, hi1, hne⟩` from `hall`. Take `⟨t, ht⟩` from `hsep i1 i0 hne`. Set `y' : ι → V` to `fun i => (p i t - p i1 t) • y i`.

Establish `hy'1 : y' i1 = 0` using `by simp [y']`. Establish `hsum : ∑ i ∈ F.erase i1, y' i = C t (∑ i ∈ F, y i) - p i1 t • ∑ i ∈ F, y i`. Rewrite using `[Finset.sum_erase _ hy'1, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [y']`.

Rewrite using `[hy i hi t, sub_smul]`. Establish `hmem : ∑ i ∈ F.erase i1, y' i ∈ P`. Rewrite using `[hsum]`. Conclude with `P.sub_mem (hP t _ hs) (P.smul_mem _ hs)`. Establish `key` using `ih (F.erase i1) (Finset.erase_ssubset hi1) y' (fun i hi u => by`.

Simplify using `only [y']`. Rewrite using `[map_smul, hy i (Finset.mem_of_mem_erase hi) u, smul_comm]) hmem`. Use `i0 (Finset.mem_erase.mpr ⟨fun e => hne e.symm, hi0⟩)`. Establish `hd : p i0 t - p i1 t ≠ 0` using `sub_ne_zero.mpr (Ne.symm ht)`. Establish `e0 : y i0 = (p i0 t - p i1 t)⁻¹ • y' i0`.

Simplify using `only [y']`. Rewrite using `[smul_smul, inv_mul_cancel₀ hd, one_smul]`. Rewrite using `[e0]`. Conclude with `P.smul_mem _ key`.
-/
theorem sep_mem_B {ι T V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : T → Module.End ℂ V) (p : ι → T → ℂ) (P : Submodule ℂ V) (hP : ∀ t, ∀ x ∈ P, C t x ∈ P)
    (hsep : ∀ i j, i ≠ j → ∃ t, p i t ≠ p j t) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ t, C t (y i) = p i t • y i) → ∑ i ∈ F, y i ∈ P →
      ∀ i ∈ F, y i ∈ P := by
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro y hy hs i0 hi0
    by_cases hall : ∀ i ∈ F, i = i0
    · have hF : F = {i0} := by
        ext i
        simp only [Finset.mem_singleton]
        exact ⟨hall i, fun e => e ▸ hi0⟩
      rw [hF, Finset.sum_singleton] at hs
      exact hs
    push_neg at hall
    obtain ⟨i1, hi1, hne⟩ := hall
    obtain ⟨t, ht⟩ := hsep i1 i0 hne
    let y' : ι → V := fun i => (p i t - p i1 t) • y i
    have hy'1 : y' i1 = 0 := by simp [y']
    have hsum : ∑ i ∈ F.erase i1, y' i = C t (∑ i ∈ F, y i) - p i1 t • ∑ i ∈ F, y i := by
      rw [Finset.sum_erase _ hy'1, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [y']
      rw [hy i hi t, sub_smul]
    have hmem : ∑ i ∈ F.erase i1, y' i ∈ P := by
      rw [hsum]
      exact P.sub_mem (hP t _ hs) (P.smul_mem _ hs)
    have key := ih (F.erase i1) (Finset.erase_ssubset hi1) y'
      (fun i hi u => by
        simp only [y']
        rw [map_smul, hy i (Finset.mem_of_mem_erase hi) u, smul_comm]) hmem
      i0 (Finset.mem_erase.mpr ⟨fun e => hne e.symm, hi0⟩)
    have hd : p i0 t - p i1 t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have e0 : y i0 = (p i0 t - p i1 t)⁻¹ • y' i0 := by
      simp only [y']
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [e0]
    exact P.smul_mem _ key

/- English proof (translation)
Substitute `h` using the available equality. Apply the tactic sequence `induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>`. Simplify using `[embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]`.
-/
theorem embGL_apply_B {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) (a b : Fin N) :
    ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a b =
      if ha : a.1 < n then (if hb : b.1 < n then (g : Matrix (Fin n) (Fin n) ℂ) ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
      else (if b.1 < n then 0 else 1) := by
  subst h
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

/- English proof (translation)
Use extensionality with `a b`. Establish `ha2` using `a.2`. Establish `hb2` using `b.2`. Rewrite using `[embGL_apply_B, Matrix.diagonal_apply]`. Apply the tactic sequence `by_cases ha : a.1 < n <;> by_cases hb : b.1 < n`.

Rewrite using `[dif_pos ha, dif_pos hb] show (Matrix.diagonal fun a => (t a : ℂ)) ⟨a.1, ha⟩ ⟨b.1, hb⟩ = _`. Rewrite using `[Matrix.diagonal_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[dB, ha]`.

Establish `hne : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩` using `fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))`. Simplify using `[hab, hne]`. Establish `hab : a ≠ b` using `fun e => hb (e ▸ ha)`. Rewrite using `[dif_pos ha, dif_neg hb, if_neg hab]`. Establish `hab : a ≠ b` using `fun e => ha (e ▸ hb)`.

Rewrite using `[dif_neg ha, if_pos hb, if_neg hab]`. Establish `hab : a = b` using `Fin.ext (by omega)`. Substitute `hab` using the available equality. Rewrite using `[dif_neg ha, if_neg hb, if_pos rfl]`. Simplify using `[dB, ha]`.
-/
theorem embGL_diag_B {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    ((embGL ℂ n N h (diagGL ℂ n t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (dB n N (fun j => (t j : ℂ))) := by
  ext a b
  have ha2 := a.2
  have hb2 := b.2
  rw [embGL_apply_B, Matrix.diagonal_apply]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · rw [dif_pos ha, dif_pos hb]
    show (Matrix.diagonal fun a => (t a : ℂ)) ⟨a.1, ha⟩ ⟨b.1, hb⟩ = _
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp [dB, ha]
    · have hne : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩ := fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))
      simp [hab, hne]
  · have hab : a ≠ b := fun e => hb (e ▸ ha)
    rw [dif_pos ha, dif_neg hb, if_neg hab]
  · have hab : a ≠ b := fun e => ha (e ▸ hb)
    rw [dif_neg ha, if_pos hb, if_neg hab]
  · have hab : a = b := Fin.ext (by omega)
    subst hab
    rw [dif_neg ha, if_neg hb, if_pos rfl]
    simp [dB, ha]

/- English proof (translation)
Establish `h1` using `hW (diagGL ℂ n t) f hf`. Unfold `sqAct at h1`. Rewrite `h1` using `[embGL_diag_B, Matrix.diagonal_transpose]`. Establish `hu : detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift ≠ 0` using `Units.ne_zero _`. Use `W.smul_mem (detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift)⁻¹ h1` as an intermediate fact.

Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hu, one_smul]`. Then use the resulting hypothesis.
-/
theorem torus_mem_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (t : Fin n → ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ))) f ∈ W := by
  have h1 := hW (diagGL ℂ n t) f hf
  unfold sqAct at h1
  rw [embGL_diag_B, Matrix.diagonal_transpose] at h1
  have hu : detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift ≠ 0 := Units.ne_zero _
  have := W.smul_mem (detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this

/- English proof (translation)
Set `F` to `f.support.image (Finsupp.weight (wnB n N))`. Distinguish the cases in `hm : m ∈ F`. Use `sep_mem_B (T := Fin n → ℂˣ) (fun t => (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ)))).toLinearMap) (fun m t => chiB (fun j => (t j : ℂ)) m) W (fun t x hx => torus_mem_B h lam W hW t x hx) ?_ F (fun m => weightedHomogeneousCompone …` and prove the remaining obligations. Introduce `i j hij`. Take `⟨k, hk⟩ : ∃ k, i k ≠ j k` from `Function.ne_iff.mp hij`.

Set `τ : Fin n → ℂˣ` to `fun l => if l = k then Units.mk0 (2 : ℂ) two_ne_zero else 1`. Establish `key : ∀ a : Fin n → ℕ, chiB (fun l => ((τ l : ℂˣ) : ℂ)) a = (2 : ℂ) ^ a k`. Introduce `a`. Unfold `chiB`. Rewrite using `[Finset.prod_eq_single k]`.

Simplify using `[τ]`. Introduce `l _ hl`. Simplify using `[τ, hl]`. Simplify using the standard rewrite rules. Use `⟨τ, ?_⟩` and prove the remaining obligations.

Use `show chiB (fun l => ((τ l : ℂˣ) : ℂ)) i ≠ chiB (fun l => ((τ l : ℂˣ) : ℂ)) j`. Rewrite using `[key, key]`. Introduce `he`. Apply `hk` to reduce the goal to its premises. Establish `h2 : ((2 ^ i k : ℕ) : ℂ) = ((2 ^ j k : ℕ) : ℂ)` using `by push_cast; exact he`.

Conclude with `Nat.pow_right_injective le_rfl (Nat.cast_injective h2)`. Introduce `i _ t`. Conclude with `rowAct_diag_homog _ _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)`. Rewrite using `[comp_sum_B]`. Conclude with `hf`.

Introduce `e he`. Conclude with `Finset.mem_image_of_mem _ he`. Rewrite using `[comp_zero_B]`. Conclude with `W.zero_mem`. Introduce `e he hw`.

Conclude with `hm (hw ▸ Finset.mem_image_of_mem _ he)`.
-/
theorem graded_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) (m : Fin n → ℕ) :
    weightedHomogeneousComponent (wnB n N) m f ∈ W := by
  classical
  let F := f.support.image (Finsupp.weight (wnB n N))
  by_cases hm : m ∈ F
  · refine sep_mem_B (T := Fin n → ℂˣ)
      (fun t => (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ)))).toLinearMap)
      (fun m t => chiB (fun j => (t j : ℂ)) m) W (fun t x hx => torus_mem_B h lam W hW t x hx) ?_ F
      (fun m => weightedHomogeneousComponent (wnB n N) m f) ?_ ?_ m hm
    · intro i j hij
      obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := Function.ne_iff.mp hij
      let τ : Fin n → ℂˣ := fun l => if l = k then Units.mk0 (2 : ℂ) two_ne_zero else 1
      have key : ∀ a : Fin n → ℕ, chiB (fun l => ((τ l : ℂˣ) : ℂ)) a = (2 : ℂ) ^ a k := by
        intro a
        unfold chiB
        rw [Finset.prod_eq_single k]
        · simp [τ]
        · intro l _ hl
          simp [τ, hl]
        · simp
      refine ⟨τ, ?_⟩
      show chiB (fun l => ((τ l : ℂˣ) : ℂ)) i ≠ chiB (fun l => ((τ l : ℂˣ) : ℂ)) j
      rw [key, key]
      intro he
      apply hk
      have h2 : ((2 ^ i k : ℕ) : ℂ) = ((2 ^ j k : ℕ) : ℂ) := by push_cast; exact he
      exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2)
    · intro i _ t
      exact rowAct_diag_homog _ _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [comp_sum_B]
      · exact hf
      · intro e he
        exact Finset.mem_image_of_mem _ he
  · rw [comp_zero_B]
    · exact W.zero_mem
    · intro e he hw
      exact hm (hw ▸ Finset.mem_image_of_mem _ he)

end PI.WGB
