import Mathlib

noncomputable section

namespace PI.WGL.XiU

open Matrix

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem normSq_sum_eq {N : ℕ} (u : Fin N → ℂ) :
    star u ⬝ᵥ u = ((∑ a, Complex.normSq (u a) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem normSq_sum_mulVec {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (w : Fin N → ℂ) : ∑ a, Complex.normSq ((x *ᵥ w) a) = ∑ b, Complex.normSq (w b) := by
  apply Complex.ofReal_injective
  rw [← normSq_sum_eq, ← normSq_sum_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hx,
    Matrix.one_mulVec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_comp_le {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (f : Fin N → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∑ p, f (I p) ≤ ∑ a, f a := by
  rw [← Finset.sum_image (fun p _ q _ h => hI h)]
  exact Finset.sum_le_univ_sum_of_nonneg hf

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem sum_comp_eq {N s : ℕ} {M : Type*} [AddCommMonoid M] (I : Fin s → Fin N) (hI : Function.Injective I)
    (f : Fin N → M) (hf : ∀ b, b ∉ Set.range I → f b = 0) : ∑ b, f b = ∑ p, f (I p) := by
  rw [← Finset.sum_image (fun p _ q _ h => hI h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  apply hf
  rintro ⟨p, rfl⟩
  exact hb (Finset.mem_image_of_mem _ (Finset.mem_univ p))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem sub_contract {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) (v : Fin s → ℂ) :
    ∑ p, Complex.normSq (((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p) ≤ ∑ q, Complex.normSq (v q) := by
  set w : Fin N → ℂ := Function.extend J v 0 with hw
  have hwJ : ∀ q, w (J q) = v q := fun q => hJ.extend_apply v 0 q
  have hw0 : ∀ b, b ∉ Set.range J → w b = 0 := by
    intro b hb
    rw [hw, Function.extend_apply' _ _ _ hb]
    rfl
  have hmv : ∀ p, ((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p = (x *ᵥ w) (I p) := by
    intro p
    have hs := sum_comp_eq J hJ (fun b => x (I p) b * w b) (fun b hb => by simp [hw0 b hb])
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [hs]
    simp only [hwJ]
  have hnorm : ∑ b, Complex.normSq (w b) = ∑ q, Complex.normSq (v q) := by
    have hs := sum_comp_eq J hJ (fun b => Complex.normSq (w b)) (fun b hb => by simp [hw0 b hb])
    rw [hs]
    simp only [hwJ]
  calc ∑ p, Complex.normSq (((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p)
      = ∑ p, Complex.normSq ((x *ᵥ w) (I p)) := by simp only [hmv]
    _ ≤ ∑ a, Complex.normSq ((x *ᵥ w) a) :=
        sum_comp_le I hI _ (fun a => Complex.normSq_nonneg _)
    _ = ∑ b, Complex.normSq (w b) := normSq_sum_mulVec x hx w
    _ = ∑ q, Complex.normSq (v q) := hnorm

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem multiset_prod_norm_le_one (m : Multiset ℂ) (h : ∀ μ ∈ m, ‖μ‖ ≤ 1) : ‖m.prod‖ ≤ 1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := h a (by simp)
    have hs := ih (fun μ hμ => h μ (by simp [hμ]))
    exact mul_le_one₀ ha (norm_nonneg _) hs

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

A detailed English derivation is pending.
-/
theorem det_sub_norm_le_one {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) :
    ‖(Matrix.of fun p q => x (I p) (J q)).det‖ ≤ 1 := by
  set A := Matrix.of fun p q => x (I p) (J q) with hA
  rw [Matrix.det_eq_prod_roots_charpoly]
  apply multiset_prod_norm_le_one
  intro μ hμ
  have hroot : A.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).1 hμ
  have hspec : μ ∈ spectrum ℂ A := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hspec
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hspec
  have hAv : A *ᵥ v = μ • v := by
    first
    | rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hv
    | rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
        Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  have hc := sub_contract x hx I J hI hJ v
  rw [← hA, hAv] at hc
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, ← Finset.mul_sum] at hc
  have hpos : 0 < ∑ q, Complex.normSq (v q) := by
    obtain ⟨q, hq⟩ := Function.ne_iff.1 hv0
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hq)
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (v i)) (Finset.mem_univ q))
  have h1 : Complex.normSq μ ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have h2 := Complex.normSq_eq_norm_sq μ
  nlinarith [norm_nonneg μ]

end PI.WGL.XiU
