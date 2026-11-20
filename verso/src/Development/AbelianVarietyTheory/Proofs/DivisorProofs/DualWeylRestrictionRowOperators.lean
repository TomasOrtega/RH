import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a' b'`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, add_tmul]`. Rewrite using `[mul_comm b' b]`. Consider the case `add y y' hy hy' => simp only [mul_add, map_add, hy, hy', add_mul]`. Normalize the expressions using the abelian group laws.

Consider the case `add x x' hx hx' => simp only [add_mul, mul_add, map_add, hx, hx']`. Normalize the expressions using the abelian group laws.
-/
theorem rTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ A A) (x y : A ⊗[ℚ] B) :
    LinearMap.rTensor B (D : A →ₗ[ℚ] A) (x * y) =
      x * LinearMap.rTensor B (D : A →ₗ[ℚ] A) y + y * LinearMap.rTensor B (D : A →ₗ[ℚ] A) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, add_tmul]
      rw [mul_comm b' b]
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add, hx, hx']; abel

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a' b'`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, tmul_add]`. Rewrite using `[mul_comm a' a]`. Consider the case `add y y' hy hy' => simp only [mul_add, map_add, hy, hy', add_mul]`. Normalize the expressions using the abelian group laws.

Consider the case `add x x' hx hx' => simp only [add_mul, mul_add, map_add, hx, hx']`. Normalize the expressions using the abelian group laws.
-/
theorem lTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ B B) (x y : A ⊗[ℚ] B) :
    LinearMap.lTensor A (D : B →ₗ[ℚ] B) (x * y) =
      x * LinearMap.lTensor A (D : B →ₗ[ℚ] B) y + y * LinearMap.lTensor A (D : B →ₗ[ℚ] B) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, tmul_add]
      rw [mul_comm a' a]
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add, hx, hx']; abel

/- English proof (translation)
Rewrite using `[Ne, Fin.ext_iff]`. Simplify using `only [Fin.coe_natAdd, Fin.coe_castAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natAdd_ne_castAdd' {p q : ℕ} (b : Fin q) (d : Fin p) : Fin.natAdd p b ≠ Fin.castAdd q d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

/- English proof (translation)
Rewrite using `[Ne, Fin.ext_iff]`. Simplify using `only [Fin.coe_natAdd, Fin.coe_castAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem castAdd_ne_natAdd' {p q : ℕ} (a : Fin p) (d : Fin q) : Fin.castAdd q a ≠ Fin.natAdd p d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

/- English proof (translation)
Take `⟨v1, v2⟩` from `v`. Rewrite using `[Formalism.CohomologicalDescent.LR.der_X]`. Proceed by induction on `v1 using Fin.addCases with`. Consider the case `left a`. Proceed by induction on `v2 using Fin.addCases with`.

Consider the case `left s`. Distinguish the cases in `h : a = d`. Substitute `h` using the available equality. Simplify using `[resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]`. Simplify using `[resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]`.

Consider the case `right t`. Distinguish the cases in `h : a = d`. Substitute `h` using the available equality. Simplify using `[resT, resVarT]`. Simplify using `[resT, resVarT, h]`.

Consider the case `right b`. Rewrite using `[if_neg (natAdd_ne_castAdd' b d)]`. Proceed by induction on `v2 using Fin.addCases with`. Consider the case `left s => simp [resT, resVarT]`. Consider the case `right t => simp [resT, resVarT]`.
-/
theorem resT_der_left_X (p q : ℕ) (c d : Fin p) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) (X v)) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]
    | right t =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
  | right b =>
    rw [if_neg (natAdd_ne_castAdd' b d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]

/- English proof (translation)
Take `⟨v1, v2⟩` from `v`. Rewrite using `[Formalism.CohomologicalDescent.LR.der_X]`. Proceed by induction on `v1 using Fin.addCases with`. Consider the case `left a`. Rewrite using `[if_neg (castAdd_ne_natAdd' a d)]`.

Proceed by induction on `v2 using Fin.addCases with`. Consider the case `left s => simp [resT, resVarT]`. Consider the case `right t => simp [resT, resVarT]`. Consider the case `right b`. Proceed by induction on `v2 using Fin.addCases with`.

Consider the case `left s`. Distinguish the cases in `h : b = d`. Substitute `h` using the available equality. Simplify using `[resT, resVarT]`. Simplify using `[resT, resVarT, h]`.

Consider the case `right t`. Distinguish the cases in `h : b = d`. Substitute `h` using the available equality. Simplify using `[resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]`. Simplify using `[resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]`.
-/
theorem resT_der_right_X (p q : ℕ) (c d : Fin q) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) (X v)) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    rw [if_neg (castAdd_ne_natAdd' a d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]
  | right b =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
    | right t =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]`. Simplify using `[rowW, Pi.single_apply]`.
-/
theorem weight_rowW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (x : Fin N) :
    Finsupp.weight (rowW N N) m x = ∑ s, m (x, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [rowW, Pi.single_apply]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]`. Simplify using `[colW, Pi.single_apply]`.
-/
theorem weight_colW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (y : Fin N) :
    Finsupp.weight (colW N N) m y = ∑ a, m (a, y) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [colW, Pi.single_apply]

/- English proof (translation)
Rewrite using `[resT, aeval_monomial]`. Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hm) (by simp only [hv]; exact zero_pow hm)`.
-/
theorem resT_monomial_eq_zero (p q : ℕ) (m : Fin (p + q) × Fin (p + q) →₀ ℕ) (a : ℚ)
    (v : Fin (p + q) × Fin (p + q)) (hv : resVarT ℚ p q v = 0) (hm : m v ≠ 0) : resT ℚ p q (monomial m a) = 0 := by
  rw [resT, aeval_monomial]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hm) (by simp only [hv]; exact zero_pow hm)

/- English proof (translation)
Simplify using `[resVarT]`.
-/
theorem resVarT_castAdd_natAdd (p q : ℕ) (a : Fin p) (t : Fin q) :
    resVarT ℚ p q (Fin.castAdd q a, Fin.natAdd p t) = 0 := by simp [resVarT]

/- English proof (translation)
Simplify using `[resVarT]`.
-/
theorem resVarT_natAdd_castAdd (p q : ℕ) (b : Fin q) (s : Fin p) :
    resVarT ℚ p q (Fin.natAdd p b, Fin.castAdd q s) = 0 := by simp [resVarT]

/- English proof (translation)
Rewrite using `[f.as_sum, map_sum]`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `hc : coeff m f ≠ 0` using `mem_support_iff.1 hm`. Assume the negation of the conclusion as `hne`. Establish `h1 : ∀ (a : Fin p) (t' : Fin q), m (Fin.castAdd q a, Fin.natAdd p t') = 0`.

Introduce `a t'`. Assume the negation of the conclusion as `h0`. Conclude with `hne (resT_monomial_eq_zero p q m _ _ (resVarT_castAdd_natAdd p q a t') h0)`. Establish `h2 : ∀ (b : Fin q) (s : Fin p), m (Fin.natAdd p b, Fin.castAdd q s) = 0`. Introduce `b s`.

Assume the negation of the conclusion as `h0`. Conclude with `hne (resT_monomial_eq_zero p q m _ _ (resVarT_natAdd_castAdd p q b s) h0)`. Establish `hw : Finsupp.weight (colW (p + q) (p + q)) m = ν` using `hf hc`. Establish `ht' : t = ∑ c : Fin p, ((Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) : ℕ) : ℚ)`. Establish `h3` using `congrArg (coeff m) hsum`.

Rewrite `h3` using `[coeff_sum, coeff_smul, smul_eq_mul]`. Simplify using `only [Formalism.CohomologicalDescent.LR.coeff_der_diag] at h3`. Rewrite `h3` using `[← Finset.sum_mul]`. Conclude with `(mul_right_cancel₀ hc h3).symm`. Establish `key : ∑ c : Fin p, Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) = ∑ c : Fin p, Finsupp.weight (colW (p + q) (p + q)) m (Fin.castAdd q c)`.

Simplify using `only [weight_rowW_apply, weight_colW_apply, Fin.sum_univ_add, h1, h2, Finset.sum_const_zero, add_zero]`. Conclude with `Finset.sum_comm`. Apply `ht` to reduce the goal to its premises. Rewrite using `[ht', ← hw]`. Conclude with `key` after adjusting the coercions.
-/
theorem resT_wrong_degree (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (ν : Fin (p + q) → ℕ) (t : ℚ)
    (hf : IsWeightedHomogeneous (colW (p + q) (p + q)) f ν)
    (hsum : ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f)
    (ht : t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ)) : resT ℚ p q f = 0 := by
  rw [f.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hc : coeff m f ≠ 0 := mem_support_iff.1 hm
  by_contra hne
  have h1 : ∀ (a : Fin p) (t' : Fin q), m (Fin.castAdd q a, Fin.natAdd p t') = 0 := by
    intro a t'
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_castAdd_natAdd p q a t') h0)
  have h2 : ∀ (b : Fin q) (s : Fin p), m (Fin.natAdd p b, Fin.castAdd q s) = 0 := by
    intro b s
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_natAdd_castAdd p q b s) h0)
  have hw : Finsupp.weight (colW (p + q) (p + q)) m = ν := hf hc
  have ht' : t = ∑ c : Fin p, ((Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) : ℕ) : ℚ) := by
    have h3 := congrArg (coeff m) hsum
    rw [coeff_sum, coeff_smul, smul_eq_mul] at h3
    simp only [Formalism.CohomologicalDescent.LR.coeff_der_diag] at h3
    rw [← Finset.sum_mul] at h3
    exact (mul_right_cancel₀ hc h3).symm
  have key : ∑ c : Fin p, Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) =
      ∑ c : Fin p, Finsupp.weight (colW (p + q) (p + q)) m (Fin.castAdd q c) := by
    simp only [weight_rowW_apply, weight_colW_apply, Fin.sum_univ_add, h1, h2, Finset.sum_const_zero, add_zero]
    exact Finset.sum_comm
  apply ht
  rw [ht', ← hw]
  exact_mod_cast key

/- English proof (translation)
Introduce `p q f`. Use `⟨fun c d => ?_, fun c d => ?_, fun ν t hf hsum ht => resT_wrong_degree p q f ν t hf hsum ht⟩` and prove the remaining obligations. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, LinearMap.rTensor_tmul]`.

Simplify using the standard rewrite rules. Consider the case `add g h hg hh => rw [map_add, map_add, map_add, hg, hh, map_add]`. Consider the case `mul_X g v hg`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul, rTensor_der_mul, resT_der_left_X, hg]`. Proceed by induction on `f using MvPolynomial.induction_on with`.

Consider the case `C a`. Rewrite using `[← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul]`. Simplify using the standard rewrite rules. Consider the case `add g h hg hh => rw [map_add, map_add, map_add, hg, hh, map_add]`. Consider the case `mul_X g v hg`.

Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul, lTensor_der_mul, resT_der_right_X, hg]`.
-/
theorem dualWeyl_resDer : ResDer := by
  intro p q f
  refine ⟨fun c d => ?_, fun c d => ?_, fun ν t hf hsum ht => resT_wrong_degree p q f ν t hf hsum ht⟩
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.rTensor_tmul]
      simp
    | add g h hg hh => rw [map_add, map_add, map_add, hg, hh, map_add]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul, rTensor_der_mul, resT_der_left_X, hg]
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul]
      simp
    | add g h hg hh => rw [map_add, map_add, map_add, hg, hh, map_add]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul, lTensor_der_mul, resT_der_right_X, hg]

end GlobalTheory.LeviCut
