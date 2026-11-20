import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ClosedEqNablaC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL

noncomputable section

namespace PI.WHw

/- English proof (translation)
Simplify using `only [rowGen, MvPolynomial.aeval_X, lgraded_wa]`. Use `split_ifs with h`. Establish `hv : ((a, v.2) : Fin r × Fin n) = v` using `Prod.ext h.symm rfl`. Rewrite using `[hv]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules.
-/
theorem bC_rowGen_X {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen ℂ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  simp only [rowGen, MvPolynomial.aeval_X, lgraded_wa]
  split_ifs with h
  · have hv : ((a, v.2) : Fin r × Fin n) = v := Prod.ext h.symm rfl
    rw [hv]
    ring
  · simp

/- English proof (translation)
Use `first`. Consider the case `simp [rowGen, MvPolynomial.aeval_C]`. Consider the case `rfl`.
-/
theorem bC_rowGen_C {r n : ℕ} (a : Fin r) (c : ℂ) :
    rowGen ℂ a a (C c : MvPolynomial (Fin r × Fin n) ℂ) = Polynomial.C (C c) := by
  first
    | simp [rowGen, MvPolynomial.aeval_C]
    | rfl

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction`. Use `next =>`. Rewrite using `[MvPolynomial.monomial_zero', bC_rowGen_C]`. Simplify using the standard rewrite rules. Use `next v e m _ _ ih =>`.

Rewrite using `[MvPolynomial.monomial_single_add, map_mul, map_pow, bC_rowGen_X, ih]`. Establish `hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v e + m) = e * lgraded_wa a v + Finsupp.weight (lgraded_wa a) m`. Simplify using `[map_add, Finsupp.weight_apply, Finsupp.sum_single_index]`. Rewrite using `[hw]`. Simplify using `only [map_mul, map_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bC_rowGen_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowGen ℂ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  induction m using Finsupp.induction
  next =>
    rw [MvPolynomial.monomial_zero', bC_rowGen_C]
    simp
  next v e m _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, bC_rowGen_X, ih]
    have hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v e + m) =
        e * lgraded_wa a v + Finsupp.weight (lgraded_wa a) m := by
      simp [map_add, Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [hw]
    simp only [map_mul, map_pow]
    ring

/- English proof (translation)
Unfold `rowDiv`. Rewrite using `[bC_rowGen_monomial, Polynomial.coeff_C_mul, add_comm (1 : Polynomial _) Polynomial.X, Polynomial.coeff_X_add_one_pow, Nat.choose_one_right]`. Use `first`. Consider the case `rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]`. Consider the case `simp [nsmul_eq_mul, mul_comm]`.

Consider the case `(rw [MvPolynomial.smul_eq_C_mul, mul_comm]; simp)`.
-/
theorem bC_euler_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowDiv ℂ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℂ) • monomial m c := by
  unfold rowDiv
  rw [bC_rowGen_monomial, Polynomial.coeff_C_mul, add_comm (1 : Polynomial _) Polynomial.X,
    Polynomial.coeff_X_add_one_pow, Nat.choose_one_right]
  first
    | rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]
    | simp [nsmul_eq_mul, mul_comm]
    | (rw [MvPolynomial.smul_eq_C_mul, mul_comm]; simp)

/- English proof (translation)
Establish `hadd : ∀ p q : MvPolynomial (Fin r × Fin n) ℂ, rowDiv ℂ a a 1 (p + q) = rowDiv ℂ a a 1 p + rowDiv ℂ a a 1 q`. Introduce `p q`. Simplify using `[rowDiv, map_add]`. Proceed by induction on `f using MvPolynomial.induction_on'`. Use `next m' c =>`.

Rewrite using `[bC_euler_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[smul_eq_mul]`. Simplify using the standard rewrite rules.

Use `next p q hp hq =>`. Rewrite using `[hadd, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]`.
-/
theorem bC_coeff_euler {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv ℂ a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℂ) * coeff m f := by
  have hadd : ∀ p q : MvPolynomial (Fin r × Fin n) ℂ,
      rowDiv ℂ a a 1 (p + q) = rowDiv ℂ a a 1 p + rowDiv ℂ a a 1 q := by
    intro p q
    simp [rowDiv, map_add]
  induction f using MvPolynomial.induction_on'
  next m' c =>
    rw [bC_euler_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      simp [smul_eq_mul]
    · simp
  next p q hp hq =>
    rw [hadd, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

/- English proof (translation)
Proceed by induction on `V using Finset.induction_on`. Use `next =>`. Introduce `f _ hV t`. Establish `hf0 : f = 0`. Use extensionality with `m`.

Assume the negation of the conclusion as `hm`. Establish `h1` using `hV m (MvPolynomial.mem_support_iff.mpr (by simpa using hm))`. Simplify using `at h1`. Rewrite using `[hf0, map_zero]`. Conclude with `M.zero_mem`.

Use `next s V hs ih =>`. Introduce `f hf hV t`. Use `set g := rowDiv ℂ a a 1 f - (s : ℂ) • f with hg`. Establish `hgM : g ∈ M` using `M.sub_mem (hM a a 1 f hf) (M.smul_mem _ hf)`. Establish `hcg : ∀ m, MvPolynomial.coeff m g = ((Finsupp.weight (lgraded_wa a) m : ℂ) - s) * MvPolynomial.coeff m f`.

Introduce `m`. Rewrite using `[hg, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, bC_coeff_euler, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hgV : ∀ m ∈ g.support, Finsupp.weight (lgraded_wa a) m ∈ V`. Introduce `m hm`.

Rewrite `hm` using `[MvPolynomial.mem_support_iff, hcg]`. Establish `hfm : MvPolynomial.coeff m f ≠ 0` using `right_ne_zero_of_mul hm`. Establish `hws : (Finsupp.weight (lgraded_wa a) m : ℂ) - s ≠ 0` using `left_ne_zero_of_mul hm`. Break down `Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hfm)) with h | h` into its components or cases. Conclude with `(hws (by rw [h, sub_self])).elim`.

Conclude with `h`. Establish `hIH` using `ih g hgM hgV`. Establish `hcomp : ∀ t', t' ≠ s → weightedHomogeneousComponent (lgraded_wa a) t' f ∈ M`. Introduce `t' ht'`. Establish `e : weightedHomogeneousComponent (lgraded_wa a) t' f = ((t' : ℂ) - s)⁻¹ • weightedHomogeneousComponent (lgraded_wa a) t' g`.

Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_weightedHomogeneousComponent, hcg]`. Use `split_ifs with hm`. Rewrite using `[hm, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]`. Conclude with `sub_ne_zero.mpr (by exact_mod_cast ht')`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `M.smul_mem _ (hIH t')`. Distinguish the cases in `hts : t = s`. Rewrite using `[hts]`.

Establish `hsum : weightedHomogeneousComponent (lgraded_wa a) s f = f - ∑ t' ∈ V, weightedHomogeneousComponent (lgraded_wa a) t' f`. Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_sub, MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_weightedHomogeneousComponent]`. Rewrite using `[Finset.sum_ite_eq]`.

Distinguish the cases in `hm : MvPolynomial.coeff m f = 0`. Simplify using `[hm]`. Break down `Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hm)) with h | h` into its components or cases. Simplify using `[h, hs]`. Establish `hne : Finsupp.weight (lgraded_wa a) m ≠ s` using `fun e => hs (e ▸ h)`.

Simplify using `[h, hne]`. Rewrite using `[hsum]`. Conclude with `M.sub_mem hf (M.sum_mem fun t' ht' => hcomp t' (fun e => hs (e ▸ ht')))`. Conclude with `hcomp t hts`.
-/
theorem bC_sep {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (a : Fin r) (V : Finset ℕ) :
    ∀ f ∈ M, (∀ m ∈ f.support, Finsupp.weight (lgraded_wa a) m ∈ V) →
      ∀ t, weightedHomogeneousComponent (lgraded_wa a) t f ∈ M := by
  classical
  induction V using Finset.induction_on
  next =>
    intro f _ hV t
    have hf0 : f = 0 := by
      ext m
      by_contra hm
      have h1 := hV m (MvPolynomial.mem_support_iff.mpr (by simpa using hm))
      simp at h1
    rw [hf0, map_zero]
    exact M.zero_mem
  next s V hs ih =>
    intro f hf hV t
    set g := rowDiv ℂ a a 1 f - (s : ℂ) • f with hg
    have hgM : g ∈ M := M.sub_mem (hM a a 1 f hf) (M.smul_mem _ hf)
    have hcg : ∀ m, MvPolynomial.coeff m g =
        ((Finsupp.weight (lgraded_wa a) m : ℂ) - s) * MvPolynomial.coeff m f := by
      intro m
      rw [hg, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, bC_coeff_euler, smul_eq_mul]
      ring
    have hgV : ∀ m ∈ g.support, Finsupp.weight (lgraded_wa a) m ∈ V := by
      intro m hm
      rw [MvPolynomial.mem_support_iff, hcg] at hm
      have hfm : MvPolynomial.coeff m f ≠ 0 := right_ne_zero_of_mul hm
      have hws : (Finsupp.weight (lgraded_wa a) m : ℂ) - s ≠ 0 := left_ne_zero_of_mul hm
      rcases Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hfm)) with h | h
      · exact (hws (by rw [h, sub_self])).elim
      · exact h
    have hIH := ih g hgM hgV
    have hcomp : ∀ t', t' ≠ s → weightedHomogeneousComponent (lgraded_wa a) t' f ∈ M := by
      intro t' ht'
      have e : weightedHomogeneousComponent (lgraded_wa a) t' f =
          ((t' : ℂ) - s)⁻¹ • weightedHomogeneousComponent (lgraded_wa a) t' g := by
        ext m
        rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_weightedHomogeneousComponent,
          MvPolynomial.coeff_weightedHomogeneousComponent, hcg]
        split_ifs with hm
        · rw [hm, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
          exact sub_ne_zero.mpr (by exact_mod_cast ht')
        · simp
      rw [e]
      exact M.smul_mem _ (hIH t')
    by_cases hts : t = s
    · rw [hts]
      have hsum : weightedHomogeneousComponent (lgraded_wa a) s f =
          f - ∑ t' ∈ V, weightedHomogeneousComponent (lgraded_wa a) t' f := by
        ext m
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum]
        simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
        rw [Finset.sum_ite_eq]
        by_cases hm : MvPolynomial.coeff m f = 0
        · simp [hm]
        · rcases Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hm)) with h | h
          · simp [h, hs]
          · have hne : Finsupp.weight (lgraded_wa a) m ≠ s := fun e => hs (e ▸ h)
            simp [h, hne]
      rw [hsum]
      exact M.sub_mem hf (M.sum_mem fun t' ht' => hcomp t' (fun e => hs (e ▸ ht')))
    · exact hcomp t hts

/- English proof (translation)
Proceed by induction on `A using Finset.induction_on`. Use `next =>`. Introduce `f hf`. Conclude with `⟨f, hf, fun m => by simp⟩`. Use `next a0 A ha0 ih =>`.

Introduce `f hf`. Take `⟨h, hhM, hh⟩` from `ih f hf`. Use `⟨weightedHomogeneousComponent (lgraded_wa a0) (μ a0) h, bC_sep M hM a0 (h.support.image (Finsupp.weight (lgraded_wa a0))) h hhM (fun m hm => Finset.mem_image_of_mem _ hm) (μ a0), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_weightedHomogeneousComponent, hh]`. Distinguish the cases in `h1 : Finsupp.weight (lgraded_wa a0) m = μ a0`.

Simplify using `[h1, Finset.forall_mem_insert]`. Simplify using `[h1, Finset.forall_mem_insert]`.
-/
theorem bC_multi {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (μ : Fin r → ℕ) (A : Finset (Fin r)) :
    ∀ f ∈ M, ∃ h ∈ M, ∀ m, coeff m h =
      if (∀ a ∈ A, Finsupp.weight (lgraded_wa a) m = μ a) then coeff m f else 0 := by
  classical
  induction A using Finset.induction_on
  next =>
    intro f hf
    exact ⟨f, hf, fun m => by simp⟩
  next a0 A ha0 ih =>
    intro f hf
    obtain ⟨h, hhM, hh⟩ := ih f hf
    refine ⟨weightedHomogeneousComponent (lgraded_wa a0) (μ a0) h,
      bC_sep M hM a0 (h.support.image (Finsupp.weight (lgraded_wa a0))) h hhM
        (fun m hm => Finset.mem_image_of_mem _ hm) (μ a0), fun m => ?_⟩
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, hh]
    by_cases h1 : Finsupp.weight (lgraded_wa a0) m = μ a0
    · simp [h1, Finset.forall_mem_insert]
    · simp [h1, Finset.forall_mem_insert]

/- English proof (translation)
Establish `hw : ∀ (m : Fin r × Fin n →₀ ℕ) (a : Fin r), (Finsupp.weight (rowW r n) m) a = Finsupp.weight (lgraded_wa a) m`. Introduce `m a`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, rowW, lgraded_wa, Pi.smul_apply, Pi.single_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : v.1 = a`.

Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Take `⟨h, hhM, hh⟩` from `bC_multi M hM μ Finset.univ f hf`. Establish `e : weightedHomogeneousComponent (rowW r n) μ f = h`. Use extensionality with `m`.

Rewrite using `[MvPolynomial.coeff_weightedHomogeneousComponent, hh]`. Establish `hiff : Finsupp.weight (rowW r n) m = μ ↔ ∀ a ∈ Finset.univ, Finsupp.weight (lgraded_wa a) m = μ a`. Prove the components needed by the constructor for the conclusion. Introduce `e a _`. Rewrite using `[← hw, e]`.

Introduce `e`. Use function extensionality and compare the values at `a`. Rewrite using `[hw]`. Conclude with `e a (Finset.mem_univ a)`. Distinguish the cases in `e1 : Finsupp.weight (rowW r n) m = μ`.

Rewrite using `[if_pos e1, if_pos (hiff.mp e1)]`. Rewrite using `[if_neg e1, if_neg (fun h' => e1 (hiff.mpr h'))]`. Rewrite using `[e]`. Conclude with `hhM`.
-/
theorem bC_graded {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (hf : f ∈ M) (μ : Fin r → ℕ) :
    weightedHomogeneousComponent (rowW r n) μ f ∈ M := by
  classical
  have hw : ∀ (m : Fin r × Fin n →₀ ℕ) (a : Fin r),
      (Finsupp.weight (rowW r n) m) a = Finsupp.weight (lgraded_wa a) m := by
    intro m a
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, rowW, lgraded_wa, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : v.1 = a
    · simp [h]
    · simp [h, Ne.symm h]
  obtain ⟨h, hhM, hh⟩ := bC_multi M hM μ Finset.univ f hf
  have e : weightedHomogeneousComponent (rowW r n) μ f = h := by
    ext m
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, hh]
    have hiff : Finsupp.weight (rowW r n) m = μ ↔
        ∀ a ∈ Finset.univ, Finsupp.weight (lgraded_wa a) m = μ a := by
      constructor
      · intro e a _
        rw [← hw, e]
      · intro e
        funext a
        rw [hw]
        exact e a (Finset.mem_univ a)
    by_cases e1 : Finsupp.weight (rowW r n) m = μ
    · rw [if_pos e1, if_pos (hiff.mp e1)]
    · rw [if_neg e1, if_neg (fun h' => e1 (hiff.mpr h'))]
  rw [e]
  exact hhM

/- English proof (translation)
Simplify using `only [rowGen, MvPolynomial.aeval_X]`. Establish `hX : ∀ u : Fin r × Fin n, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (X u : MvPolynomial (Fin r × Fin n) ℂ) ((u.1 : ℕ) : ℤ)` using `fun u => MvPolynomial.isWeightedHomogeneous_X ℂ _ u`. Establish `h0 : ∀ e : ℤ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (0 : MvPolynomial (Fin r × Fin n) ℂ) e` using `fun e => MvPolynomial.isWeightedHomogeneous_zero ℂ _ e`. Distinguish the cases in `hb : v.1 = b`. Rewrite using `[if_pos hb, Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_monomial]`.

Distinguish the cases in `hk0 : k = 0`. Substitute `hk0` using the available equality. Simplify using `using hX v`. Distinguish the cases in `hk1 : k = 1`. Substitute `hk1` using the available equality.

Establish `e : ((v.1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) = ((a : ℕ) : ℤ)`. Rewrite using `[hb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Simplify using `using hX (a, v.2)`. Rewrite using `[if_neg hk0, if_neg (Ne.symm hk1), add_zero]`. Conclude with `h0 _`. Rewrite using `[if_neg hb, add_zero, Polynomial.coeff_C]`. Distinguish the cases in `hk0 : k = 0`.

Substitute `hk0` using the available equality. Simplify using `using hX v`. Rewrite using `[if_neg hk0]`. Conclude with `h0 _`.
-/
private theorem isWeightedHomogeneous_coeff_rowGen_X_fst_weight {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) (k : ℕ) :
    IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      ((rowGen ℂ a b (X v)).coeff k) (((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
  simp only [rowGen, MvPolynomial.aeval_X]
  have hX : ∀ u : Fin r × Fin n, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      (X u : MvPolynomial (Fin r × Fin n) ℂ) ((u.1 : ℕ) : ℤ) :=
    fun u => MvPolynomial.isWeightedHomogeneous_X ℂ _ u
  have h0 : ∀ e : ℤ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      (0 : MvPolynomial (Fin r × Fin n) ℂ) e :=
    fun e => MvPolynomial.isWeightedHomogeneous_zero ℂ _ e
  by_cases hb : v.1 = b
  · rw [if_pos hb, Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_add,
      Polynomial.coeff_C, Polynomial.coeff_monomial]
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hX v
    · by_cases hk1 : k = 1
      · subst hk1
        have e : ((v.1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) = ((a : ℕ) : ℤ) := by
          rw [hb]
          push_cast
          ring
        rw [e]
        simpa using hX (a, v.2)
      · rw [if_neg hk0, if_neg (Ne.symm hk1), add_zero]
        exact h0 _
  · rw [if_neg hb, add_zero, Polynomial.coeff_C]
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hX v
    · rw [if_neg hk0]
      exact h0 _

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Use `first`. Consider the case `(apply MvPolynomial.IsWeightedHomogeneous.sum`. Introduce `x hx`.

Establish `hx' : x.1 + x.2 = k` using `by simpa using hx`. Establish `e1 : d + e + (k : ℤ) * c = (d + (x.1 : ℤ) * c) + (e + (x.2 : ℤ) * c)`. Rewrite using `[← hx']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Conclude with `(hF x.1).mul (hG x.2))`. Consider the case `(rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]`. Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_weightedHomogeneousSubmodule]`.

Establish `hx' : x.1 + x.2 = k` using `by simpa using hx`. Establish `e1 : d + e + (k : ℤ) * c = (d + (x.1 : ℤ) * c) + (e + (x.2 : ℤ) * c)`. Rewrite using `[← hx']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Conclude with `(hF x.1).mul (hG x.2))`.
-/
private theorem isWeightedHomogeneous_coeff_mul_fst_weight {r n : ℕ} (c : ℤ)
    (F G : Polynomial (MvPolynomial (Fin r × Fin n) ℂ)) (d e : ℤ)
    (hF : ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (F.coeff k) (d + (k : ℤ) * c))
    (hG : ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (G.coeff k) (e + (k : ℤ) * c)) :
    ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) ((F * G).coeff k) (d + e + (k : ℤ) * c) := by
  intro k
  rw [Polynomial.coeff_mul]
  first
    | (apply MvPolynomial.IsWeightedHomogeneous.sum
       intro x hx
       have hx' : x.1 + x.2 = k := by simpa using hx
       have e1 : d + e + (k : ℤ) * c = (d + (x.1 : ℤ) * c) + (e + (x.2 : ℤ) * c) := by
         rw [← hx']
         push_cast
         ring
       rw [e1]
       exact (hF x.1).mul (hG x.2))
    | (rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
       refine Submodule.sum_mem _ fun x hx => ?_
       rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
       have hx' : x.1 + x.2 = k := by simpa using hx
       have e1 : d + e + (k : ℤ) * c = (d + (x.1 : ℤ) * c) + (e + (x.2 : ℤ) * c) := by
         rw [← hx']
         push_cast
         ring
       rw [e1]
       exact (hF x.1).mul (hG x.2))

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction`. Use `next =>`. Introduce `k`. Establish `hC : rowGen ℂ a b (monomial 0 c0 : MvPolynomial (Fin r × Fin n) ℂ) = Polynomial.C (MvPolynomial.C c0)`. Rewrite using `[MvPolynomial.monomial_zero']`.

Use `first`. Consider the case `simp [rowGen, MvPolynomial.aeval_C]`. Consider the case `rfl`. Rewrite using `[hC, Polynomial.coeff_C]`. Distinguish the cases in `hk : k = 0`.

Substitute `hk` using the available equality. Simplify using `using MvPolynomial.isWeightedHomogeneous_C (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) c0`. Rewrite using `[if_neg hk]`. Conclude with `MvPolynomial.isWeightedHomogeneous_zero ℂ _ _`. Use `next v e m _ _ ih =>`.

Introduce `k`. Rewrite using `[MvPolynomial.monomial_single_add, map_mul, map_pow]`. Establish `hw : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (Finsupp.single v e + m) = (e : ℤ) * ((v.1 : ℕ) : ℤ) + Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m`. Simplify using `[map_add, Finsupp.weight_apply, Finsupp.sum_single_index, nsmul_eq_mul]`. Rewrite using `[hw]`.

Establish `hpow : ∀ j : ℕ, ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (((rowGen ℂ a b (X v)) ^ j).coeff k) ((j : ℤ) * ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)))`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `k`.

Rewrite using `[pow_zero, Polynomial.coeff_one]`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Simplify using `using MvPolynomial.isWeightedHomogeneous_one ℂ (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))`. Rewrite using `[if_neg hk]`.

Conclude with `MvPolynomial.isWeightedHomogeneous_zero ℂ _ _`. Consider the case `succ j ihj`. Introduce `k`. Rewrite using `[pow_succ]`. Establish `h` using `isWeightedHomogeneous_coeff_mul_fst_weight (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) _ _ ((j : ℤ) * ((v.1 : ℕ) : ℤ)) ((v.1 : ℕ) : ℤ) ihj (isWeightedHomogeneous_coeff_rowGen_X_fst_weight a b v) k`.

Rewrite using `[show ((j + 1 : ℕ) : ℤ) * ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) = (j : ℤ) * ((v.1 : ℕ) : ℤ) + ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) by push_cast; ring]`. Conclude with `h`. Conclude with `isWeightedHomogeneous_coeff_mul_fst_weight (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) _ _ _ _ (hpow e) ih k`.
-/
private theorem isWeightedHomogeneous_coeff_rowGen_monomial {r n : ℕ} (a b : Fin r) (m : Fin r × Fin n →₀ ℕ) (c0 : ℂ) :
    ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) ((rowGen ℂ a b (monomial m c0)).coeff k)
      (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
  induction m using Finsupp.induction
  next =>
    intro k
    have hC : rowGen ℂ a b (monomial 0 c0 : MvPolynomial (Fin r × Fin n) ℂ) =
        Polynomial.C (MvPolynomial.C c0) := by
      rw [MvPolynomial.monomial_zero']
      first
        | simp [rowGen, MvPolynomial.aeval_C]
        | rfl
    rw [hC, Polynomial.coeff_C]
    by_cases hk : k = 0
    · subst hk
      simpa using MvPolynomial.isWeightedHomogeneous_C (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) c0
    · rw [if_neg hk]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  next v e m _ _ ih =>
    intro k
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow]
    have hw : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (Finsupp.single v e + m) =
        (e : ℤ) * ((v.1 : ℕ) : ℤ) + Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m := by
      simp [map_add, Finsupp.weight_apply, Finsupp.sum_single_index, nsmul_eq_mul]
    rw [hw]
    have hpow : ∀ j : ℕ, ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
        (((rowGen ℂ a b (X v)) ^ j).coeff k) ((j : ℤ) * ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
      intro j
      induction j with
      | zero =>
        intro k
        rw [pow_zero, Polynomial.coeff_one]
        by_cases hk : k = 0
        · subst hk
          simpa using MvPolynomial.isWeightedHomogeneous_one ℂ (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
        · rw [if_neg hk]
          exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
      | succ j ihj =>
        intro k
        rw [pow_succ]
        have h := isWeightedHomogeneous_coeff_mul_fst_weight (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) _ _ ((j : ℤ) * ((v.1 : ℕ) : ℤ)) ((v.1 : ℕ) : ℤ) ihj
          (isWeightedHomogeneous_coeff_rowGen_X_fst_weight a b v) k
        rw [show ((j + 1 : ℕ) : ℤ) * ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) =
          (j : ℤ) * ((v.1 : ℕ) : ℤ) + ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) by push_cast; ring]
        exact h
    exact isWeightedHomogeneous_coeff_mul_fst_weight (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) _ _ _ _ (hpow e) ih k

/- English proof (translation)
Rewrite using `[MvPolynomial.as_sum p]`. Unfold `rowDiv`. Rewrite using `[map_sum, Polynomial.finset_sum_coeff]`. Use `first`. Consider the case `(apply MvPolynomial.IsWeightedHomogeneous.sum`.

Introduce `x hx`. Establish `hmd : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) x = d` using `hp (MvPolynomial.mem_support_iff.mp hx)`. Rewrite using `[← hmd]`. Conclude with `isWeightedHomogeneous_coeff_rowGen_monomial a b x _ k)`. Consider the case `(rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]`.

Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_weightedHomogeneousSubmodule]`. Establish `hmd : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) x = d` using `hp (MvPolynomial.mem_support_iff.mp hx)`. Rewrite using `[← hmd]`. Conclude with `isWeightedHomogeneous_coeff_rowGen_monomial a b x _ k)`.
-/
private theorem isWeightedHomogeneous_rowDiv {r n : ℕ} (a b : Fin r) (p : MvPolynomial (Fin r × Fin n) ℂ) (d : ℤ)
    (hp : IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) p d) (k : ℕ) :
    IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (rowDiv ℂ a b k p) (d + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
  classical
  rw [MvPolynomial.as_sum p]
  unfold rowDiv
  rw [map_sum, Polynomial.finset_sum_coeff]
  first
    | (apply MvPolynomial.IsWeightedHomogeneous.sum
       intro x hx
       have hmd : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) x = d := hp (MvPolynomial.mem_support_iff.mp hx)
       rw [← hmd]
       exact isWeightedHomogeneous_coeff_rowGen_monomial a b x _ k)
    | (rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
       refine Submodule.sum_mem _ fun x hx => ?_
       rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
       have hmd : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) x = d := hp (MvPolynomial.mem_support_iff.mp hx)
       rw [← hmd]
       exact isWeightedHomogeneous_coeff_rowGen_monomial a b x _ k)

/- English proof (translation)
Establish `hnn : ∀ (p : MvPolynomial (Fin r × Fin n) ℂ) (e : ℤ), IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) p e → p ≠ 0 → 0 ≤ e`. Introduce `p e hp hp0`. Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.mp hp0`. Rewrite using `[← hp hm, Finsupp.weight_apply, Finsupp.sum]`. Conclude with `Finset.sum_nonneg fun v _ => nsmul_nonneg (by show (0 : ℤ) ≤ ((v.1 : ℕ) : ℤ); positivity) _`.

Establish `main : ∀ N : ℕ, ∀ g ∈ M, g ≠ 0 → IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) g (N : ℤ) → ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `g hgM hg0 hgN`.

Distinguish the cases in `hk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k g = 0`. Conclude with `⟨g, hgM, hg0, hk⟩`. Use `push_neg at hk`. Take `⟨a, b, hab, k, hk1, hne⟩` from `hk`. Establish `hh` using `isWeightedHomogeneous_rowDiv a b g _ hgN k`.

Establish `h0` using `hnn _ _ hh hne`. Establish `hab' : (a : ℕ) < b` using `hab`. Use `set s : ℤ := (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) with hs`. Establish `hneg : s ≤ -1`. Establish `h1 : (1 : ℤ) ≤ k` using `by exact_mod_cast hk1`.

Establish `h2 : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) ≤ -1` using `by omega`. Rewrite using `[hs]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlt : ((((N : ℤ) + s).toNat : ℕ) : ℤ) < (N : ℤ)`. Rewrite using `[Int.toNat_of_nonneg h0]`.

Use linear arithmetic over natural numbers and integers. Use `ih (((N : ℤ) + s).toNat) (by exact_mod_cast hlt) _ (hM a b k g hgM) hne ?_` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg h0]`. Conclude with `hh`. Establish `hL : ∀ m : Fin r × Fin n →₀ ℕ, Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m = ∑ i : Fin r, ((i : ℕ) : ℤ) * ((Finsupp.weight (rowW r n) m i : ℕ) : ℤ)`.

Introduce `m`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `simp [Pi.single_apply] <;> ring`.

Take `⟨f, hfM, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.mp hf0`. Establish `hg0M : weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f ∈ M` using `bC_graded M hM f hfM _`. Establish `hg0c : coeff m0 (weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f) = coeff m0 f`. Rewrite using `[MvPolynomial.coeff_weightedHomogeneousComponent, if_pos rfl]`.

Establish `hg0ne : weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f ≠ 0`. Introduce `h`. Apply `hm0` to reduce the goal to its premises. Rewrite using `[← hg0c, h, MvPolynomial.coeff_zero]`. Establish `hg0h : IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f) (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m0)`.

Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.coeff_weightedHomogeneousComponent]`. Use `split_ifs at hm with h`. Rewrite using `[hL, hL, h]`. Conclude with `absurd rfl hm`.

Establish `hnn0` using `hnn _ _ hg0h hg0ne`. Conclude with `main (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m0).toNat _ hg0M hg0ne (by rw [Int.toNat_of_nonneg hnn0]; exact hg0h)`.
-/
theorem bC_exists_killed {r n : ℕ}
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
  classical
  have hnn : ∀ (p : MvPolynomial (Fin r × Fin n) ℂ) (e : ℤ), IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) p e →
      p ≠ 0 → 0 ≤ e := by
    intro p e hp hp0
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hp0
    rw [← hp hm, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun v _ => nsmul_nonneg (by show (0 : ℤ) ≤ ((v.1 : ℕ) : ℤ); positivity) _
  have main : ∀ N : ℕ, ∀ g ∈ M, g ≠ 0 → IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) g (N : ℤ) →
      ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro g hgM hg0 hgN
      by_cases hk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k g = 0
      · exact ⟨g, hgM, hg0, hk⟩
      · push_neg at hk
        obtain ⟨a, b, hab, k, hk1, hne⟩ := hk
        have hh := isWeightedHomogeneous_rowDiv a b g _ hgN k
        have h0 := hnn _ _ hh hne
        have hab' : (a : ℕ) < b := hab
        set s : ℤ := (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) with hs
        have hneg : s ≤ -1 := by
          have h1 : (1 : ℤ) ≤ k := by exact_mod_cast hk1
          have h2 : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) ≤ -1 := by omega
          rw [hs]
          nlinarith
        have hlt : ((((N : ℤ) + s).toNat : ℕ) : ℤ) < (N : ℤ) := by
          rw [Int.toNat_of_nonneg h0]
          omega
        refine ih (((N : ℤ) + s).toNat) (by exact_mod_cast hlt) _ (hM a b k g hgM) hne ?_
        rw [Int.toNat_of_nonneg h0]
        exact hh
  have hL : ∀ m : Fin r × Fin n →₀ ℕ, Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m =
      ∑ i : Fin r, ((i : ℕ) : ℤ) * ((Finsupp.weight (rowW r n) m i : ℕ) : ℤ) := by
    intro m
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, rowW, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply] <;> ring
  obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hf0
  have hg0M : weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f ∈ M :=
    bC_graded M hM f hfM _
  have hg0c : coeff m0 (weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f) =
      coeff m0 f := by
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos rfl]
  have hg0ne : weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f ≠ 0 := by
    intro h
    apply hm0
    rw [← hg0c, h, MvPolynomial.coeff_zero]
  have hg0h : IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      (weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f)
      (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m0) := by
    intro m hm
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
    split_ifs at hm with h
    · rw [hL, hL, h]
    · exact absurd rfl hm
  have hnn0 := hnn _ _ hg0h hg0ne
  exact main (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m0).toNat _ hg0M hg0ne (by rw [Int.toNat_of_nonneg hnn0]; exact hg0h)

end PI.WHw
