import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeDeriv

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
-/
theorem hasDerivAt_det {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (A' : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) (∑ j, ∑ i, adjugate (A 0) j i * A' i j) 0 := by
  have h1 : HasDerivAt (fun t => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ j, (∏ i ∈ univ.erase j, A 0 (σ i) i) • A' (σ j) j) 0 := by
    refine HasDerivAt.fun_sum fun σ _ => HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_finset_prod (f := fun i t => A t (σ i) i) fun i _ => h _ _
  have h2 : ∀ j, ∑ i, adjugate (A 0) j i * A' i j = ((A 0).updateCol j fun i => A' i j).det := by
    intro j
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  simp only [h2, Matrix.det_apply']
  convert h1 using 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul _ _ (mem_univ j), updateCol_self, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun i hi => updateCol_ne (ne_of_mem_erase hi)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem det_one_submatrix {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g).det = if univ.image f = univ.image g then 1 else 0 := by
  split_ifs with h
  · have : f = g := by
      refine (hf.range_inj hg).1 ?_
      have := congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
      simpa using this
    subst this
    rw [submatrix_one _ hf.injective, det_one]
  · have : ∃ i, f i ∉ univ.image g := by
      by_contra hc
      push Not at hc
      apply h
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, _, rfl⟩ := mem_image.1 hx
        exact hc i
      · rw [card_image_of_injective _ hf.injective, card_image_of_injective _ hg.injective]
    obtain ⟨i, hi⟩ := this
    refine det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [submatrix_apply, one_apply_ne]
    intro he
    exact hi (mem_image.2 ⟨j, mem_univ _, he.symm⟩)

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.
-/
theorem card_filter_lt {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (i : Fin m) :
    (((univ.image f).erase (f i)).filter fun c => c < f i).card = i := by
  have : (((univ.image f).erase (f i)).filter fun c => c < f i) = (Iio i).image f := by
    ext x
    simp only [mem_filter, mem_erase, mem_image, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨⟨_, j, rfl⟩, h⟩
      exact ⟨j, hf.lt_iff_lt.1 h, rfl⟩
    · rintro ⟨j, h, rfl⟩
      exact ⟨⟨(hf h).ne, j, rfl⟩, hf h⟩
  rw [this, card_image_of_injective _ hf.injective, Fin.card_Iio]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem image_succAbove {m n : ℕ} (f : Fin (m + 1) → Fin n) (hf : StrictMono f) (i : Fin (m + 1)) :
    univ.image (f ∘ i.succAbove) = (univ.image f).erase (f i) := by
  ext x
  simp only [mem_erase, mem_image, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne _ _ (hf.injective h), _, rfl⟩
  · rintro ⟨h, j, rfl⟩
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (fun e => h (by rw [e]))
    exact ⟨l, rfl⟩

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_adj {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) (a b : Fin n) :
    ∑ j, ∑ i, adjugate ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g) j i *
      (Matrix.single a b (1 : ℂ)) (f i) (g j) =
    if b ∈ univ.image g ∧ a ∉ (univ.image g).erase b ∧ univ.image f = insert a ((univ.image g).erase b) then
      (-1) ^ (((univ.image g).erase b).filter fun c => c < a).card *
        (-1) ^ (((univ.image g).erase b).filter fun c => c < b).card else 0 := by
  by_cases hb : b ∈ univ.image g
  swap
  · rw [if_neg (fun h => hb h.1)]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨_, rfl⟩
    exact hb (mem_image_of_mem _ (mem_univ _))
  by_cases ha : a ∈ univ.image f
  swap
  · rw [if_neg (by rintro ⟨_, _, h⟩; exact ha (h ▸ mem_insert_self _ _))]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨rfl, _⟩
    exact ha (mem_image_of_mem _ (mem_univ _))
  obtain ⟨j, _, rfl⟩ := mem_image.1 hb
  obtain ⟨i, _, rfl⟩ := mem_image.1 ha
  rw [sum_eq_single j, sum_eq_single i, single_apply_same, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := i.pos; omega⟩
    rw [adjugate_fin_succ_eq_det_submatrix, submatrix_submatrix,
      det_one_submatrix _ _ (hf.comp (Fin.strictMono_succAbove i)) (hg.comp (Fin.strictMono_succAbove j)),
      image_succAbove f hf, image_succAbove g hg]
    by_cases h : (univ.image f).erase (f i) = (univ.image g).erase (g j)
    · rw [if_pos h, if_pos, card_filter_lt g hg, ← h, card_filter_lt f hf, mul_one, pow_add]
      refine ⟨hb, ?_, ?_⟩
      · rw [← h]; exact notMem_erase _ _
      · rw [← h, insert_erase ha]
    · rw [if_neg h, if_neg, mul_zero]
      rintro ⟨_, h1, h2⟩
      apply h
      rw [h2, erase_insert h1]
  · intro i' _ hi
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hi (hf.injective h.1).symm
  · simp
  · intro j' _ hj
    refine sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hj (hg.injective h.2).symm
  · simp

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dR_wedge (k r m : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (J J' : Sub (2 * r + k + 1) m) :
    (wedge k r m).dR X J J' = ∑ j, ∑ i, adjugate ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) j i * X (J.1.orderEmbOfFin J.2 i) (J'.1.orderEmbOfFin J'.2 j) := by
  have h := hasDerivAt_det (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) (X.submatrix (J.1.orderEmbOfFin J.2) (J'.1.orderEmbOfFin J'.2))
      fun i j => PI.ComplexConjugateDerivative.exp_entry X _ _
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, submatrix_apply] at h
  exact h.deriv

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : reH k r Y + Complex.I • imH k r Y = Y := by
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [reH, imH, smul_smul, this, ← smul_add]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem dC_wedge_single : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by
  intro k r m a b J J'
  have h := sum_adj _ _ (J.1.orderEmbOfFin J.2).strictMono (J'.1.orderEmbOfFin J'.2).strictMono a b
  rw [Finset.image_orderEmbOfFin_univ, Finset.image_orderEmbOfFin_univ] at h
  rw [← h, FRep.dC, Matrix.add_apply, Matrix.smul_apply, dR_wedge, dR_wedge, smul_eq_mul, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← reH_add_imH k r (Matrix.single a b 1)]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.WedgeDeriv
