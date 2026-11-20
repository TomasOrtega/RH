import Mathlib

namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial

variable {σ : Type*}

def mfact (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mfact_pos (m : σ →₀ ℕ) : 0 < mfact m :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mfact_add_single [DecidableEq σ] (s : σ →₀ ℕ) (a : σ) :
    mfact (s + Finsupp.single a 1) = mfact s * (s a + 1) := by
  unfold mfact
  have h1 := Finsupp.mul_prod_erase' (s + Finsupp.single a 1) a (fun _ k => k.factorial)
    (fun _ => Nat.factorial_zero)
  have h2 := Finsupp.mul_prod_erase' s a (fun _ k => k.factorial) (fun _ => Nat.factorial_zero)
  have he : Finsupp.erase a (s + Finsupp.single a 1) = Finsupp.erase a s := by
    ext v
    by_cases hv : v = a
    · subst hv; simp
    · simp [Finsupp.erase_ne hv]
  rw [← h1, ← h2, he]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

noncomputable def fischer (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ g.support, (mfact m : ℂ) * star (coeff m f) * coeff m g

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fischer_eq_sum (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hg : g.support ⊆ s) :
    fischer f g = ∑ m ∈ s, (mfact m : ℂ) * star (coeff m f) * coeff m g :=
  Finset.sum_subset hg fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fischer_add_left (f f' g : MvPolynomial σ ℂ) :
    fischer (f + f') g = fischer f g + fischer f' g := by
  simp only [fischer, coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fischer_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer (c • f) g = star c * fischer f g := by
  simp only [fischer, coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fischer_add_right (f g g' : MvPolynomial σ ℂ) :
    fischer f (g + g') = fischer f g + fischer f g' := by
  classical
  set s := g.support ∪ g'.support
  rw [fischer_eq_sum f (g + g') s (MvPolynomial.support_add),
    fischer_eq_sum f g s Finset.subset_union_left, fischer_eq_sum f g' s Finset.subset_union_right]
  simp only [coeff_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fischer_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer f (c • g) = c * fischer f g := by
  rw [fischer_eq_sum f (c • g) g.support (MvPolynomial.support_smul), fischer, Finset.mul_sum]
  simp only [coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
@[simp] theorem fischer_zero_left (g : MvPolynomial σ ℂ) : fischer 0 g = 0 := by simp [fischer]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
@[simp] theorem fischer_zero_right (f : MvPolynomial σ ℂ) : fischer f 0 = 0 := by simp [fischer]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (g : MvPolynomial σ ℂ) : fischer (∑ i ∈ s, f i) g = ∑ i ∈ s, fischer (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem fischer_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ)
    (g : ι → MvPolynomial σ ℂ) : fischer f (∑ i ∈ s, g i) = ∑ i ∈ s, fischer f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fischer_conj_symm (f g : MvPolynomial σ ℂ) : star (fischer f g) = fischer g f := by
  classical
  rw [fischer_eq_sum g f (f.support ∪ g.support) Finset.subset_union_left,
    fischer_eq_sum f g (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_natCast, Complex.conj_conj]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem fischer_monomial [DecidableEq σ] (s t : σ →₀ ℕ) (c d : ℂ) :
    fischer (monomial s c) (monomial t d) = if s = t then (mfact s : ℂ) * star c * d else 0 := by
  rw [fischer_eq_sum _ _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton]
  simp only [coeff_monomial]
  by_cases h : s = t
  · subst h; simp
  · simp [h]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fischer_X_mul (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (X a * f) g = fischer f (pderiv a g) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, fischer_add_left, fischer_add_left, hp, hq]
  | monomial s c =>
    induction g using MvPolynomial.induction_on' with
    | add p q hp hq => rw [fischer_add_right, map_add, fischer_add_right, hp, hq]
    | monomial t d =>
      rw [X, monomial_mul, one_mul, pderiv_monomial, fischer_monomial, fischer_monomial]
      by_cases ht : t a = 0
      · have hne : Finsupp.single a 1 + s ≠ t := by
          intro h
          have := congrArg (fun m => m a) h
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
          omega
        rw [if_neg hne]
        split_ifs <;> simp [ht]
      · have hle : Finsupp.single a 1 ≤ t := by
          intro v
          by_cases hv : v = a
          · subst hv; simp only [Finsupp.single_eq_same]; omega
          · rw [Finsupp.single_apply, if_neg (Ne.symm hv)]; exact Nat.zero_le _
        have hiff : Finsupp.single a 1 + s = t ↔ s = t - Finsupp.single a 1 := by
          constructor
          · rintro rfl; simp
          · rintro rfl; rw [add_comm]; exact tsub_add_cancel_of_le hle
        by_cases h : s = t - Finsupp.single a 1
        · have h' := hiff.2 h
          rw [if_pos h', if_pos h]
          have hsa : (s a + 1 : ℕ) = t a := by
            rw [← h']; simp [add_comm]
          rw [add_comm (Finsupp.single a 1) s, mfact_add_single, ← hsa]
          push_cast
          ring
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fischer_pderiv (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (pderiv a f) g = fischer f (X a * g) := by
  rw [← fischer_conj_symm, ← fischer_X_mul, fischer_conj_symm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem fischer_self (f : MvPolynomial σ ℂ) :
    fischer f f = ((∑ m ∈ f.support, (mfact m : ℝ) * Complex.normSq (coeff m f) : ℝ) : ℂ) := by
  rw [fischer]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem fischer_self_eq_zero_iff (f : MvPolynomial σ ℂ) : fischer f f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [fischer_self, Complex.ofReal_eq_zero] at h
  have hnn : ∀ m ∈ f.support, 0 ≤ (mfact m : ℝ) * Complex.normSq (coeff m f) :=
    fun m _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext m
  by_contra hm
  have hm' : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have := hz m hm'
  rcases mul_eq_zero.1 this with h1 | h1
  · exact (Nat.cast_ne_zero.2 (mfact_pos m).ne') h1
  · exact hm (Complex.normSq_eq_zero.1 h1)

end GroundTheory.Automorphic.HarishChandra
