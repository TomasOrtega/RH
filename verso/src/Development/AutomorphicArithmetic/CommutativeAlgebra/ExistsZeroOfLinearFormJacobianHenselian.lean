import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCommonZeroOfJacobianIsUnitHenselian

noncomputable section
open IsLocalRing UpperTheory.Et

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]`. Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial s a`. Rewrite using `[MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`. Distinguish the cases in `hs : s = Finsupp.single j 1`.

Substitute `hs` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hs] split_ifs with h`. Distinguish the cases in `hsj : s j = 0`. Simplify using `[hsj]`.

It suffices to derive a contradiction. Apply `hs` to reduce the goal to its premises. Use extensionality with `k`. Establish `hk` using `DFunLike.congr_fun h k`. Distinguish the cases in `hkj : k = j`.

Substitute `hkj` using the available equality. Simplify using `at hk ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `[Finsupp.single_apply, hkj, Ne.symm hkj] at hk ⊢`. Conclude with `hk`.

Both sides reduce to the same expression. Consider the case `add p q hp hq`. Rewrite using `[map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]`.
-/
private lemma UpperTheory.eval_zero_pderiv {R : Type} [CommRing R] {n : ℕ} (j : Fin n)
    (P : MvPolynomial (Fin n) R) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv j P) = MvPolynomial.coeff (Finsupp.single j 1) P := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = Finsupp.single j 1
    · subst hs
      simp
    · rw [if_neg hs]
      split_ifs with h
      · by_cases hsj : s j = 0
        · simp [hsj]
        · exfalso
          apply hs
          ext k
          have hk := DFunLike.congr_fun h k
          by_cases hkj : k = j
          · subst hkj
            simp at hk ⊢
            omega
          · simp [Finsupp.single_apply, hkj, Ne.symm hkj] at hk ⊢
            exact hk
      · rfl
  | add p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]

/- English proof (translation)
Introduce `A E _ _ _ _ n Φ L h0 h1`. Set `G : Fin n → MvPolynomial (Fin n) E → MvPolynomial (Fin n) A` to `fun i P => ∑ d ∈ P.support, MvPolynomial.monomial d (L (MvPolynomial.coeff d P) i)`. Establish `hG : ∀ i d P, MvPolynomial.coeff d (G i P) = L (MvPolynomial.coeff d P) i`. Introduce `i d P`. Simplify using `only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']`.

Use `split_ifs with h`. Both sides reduce to the same expression. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at h`. Simplify using `[h]`. Establish `hGadd : ∀ i p q, G i (p + q) = G i p + G i q`.

Introduce `i p q`. Use extensionality with `d`. Rewrite using `[MvPolynomial.coeff_add, hG, hG, hG, MvPolynomial.coeff_add, map_add, Pi.add_apply]`. Establish `key : ∀ i (x : Fin n → A) (P : MvPolynomial (Fin n) E), MvPolynomial.eval x (G i P) = L (MvPolynomial.eval (fun j => algebraMap A E (x j)) P) i`. Introduce `i x P`.

Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial d c`. Establish `hm : G i (MvPolynomial.monomial d c) = MvPolynomial.monomial d (L c i)`. Use extensionality with `d'`. Rewrite using `[hG, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hm, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]`. Establish `hp : (d.prod fun k e => (algebraMap A E (x k)) ^ e) = algebraMap A E (d.prod fun k e => x k ^ e)`. Simplify using `[Finsupp.prod, map_prod, map_pow]`. Rewrite using `[hp, ← Algebra.commutes, ← Algebra.smul_def, map_smul]`.

Simplify using `[mul_comm]`. Consider the case `add p q hp hq`. Rewrite using `[hGadd, map_add, map_add, map_add, Pi.add_apply, hp, hq]`. Set `F : Fin n → MvPolynomial (Fin n) A` to `fun i => G i Φ`. Establish `hF0 : ∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A`.

Introduce `i`. Establish `h` using `key i 0 Φ`. Establish `e : (fun j => algebraMap A E ((0 : Fin n → A) j)) = 0`. Use `ext`. Simplify using the standard rewrite rules.

Rewrite `h` using `[e]`. Use `show MvPolynomial.eval 0 (G i Φ) ∈ maximalIdeal A`. Rewrite using `[h]`. Conclude with `h0 i`. Establish `hF1 : ∀ i j, MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)) = L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i`.

Introduce `i j`. Rewrite using `[UpperTheory.eval_zero_pderiv, UpperTheory.eval_zero_pderiv]`. Conclude with `hG i _ Φ`. Establish `hdet : IsUnit (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det`. Establish `hM : (residue A).mapMatrix (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))) = 1`.

Use extensionality with `i j`. Establish `h` using `(residue_eq_zero_iff _).mpr (h1 i j)`. Rewrite `h` using `[map_sub, sub_eq_zero]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hF1, h, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Assume the negation of the conclusion as `hu`. Establish `hm` using `(mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)`. Establish `h` using `(residue_eq_zero_iff _).mpr hm`. Rewrite `h` using `[RingHom.map_det, hM, Matrix.det_one]`. Conclude with `one_ne_zero h`.

Take `⟨x, hx, hxm⟩` from `UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian A n F hF0 hdet`. Use `⟨x, hxm, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[← key i x Φ]`. Conclude with `hx i`.
-/
theorem UpperTheory.exists_zero_of_linear_form_jacobian_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] (n : ℕ) (Φ : MvPolynomial (Fin n) E) (L : E →ₗ[A] (Fin n → A)),
      (∀ i, L (MvPolynomial.eval 0 Φ) i ∈ maximalIdeal A) →
      (∀ i j, L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i - (if i = j then 1 else 0) ∈ maximalIdeal A) →
      ∃ x : Fin n → A, (∀ j, x j ∈ maximalIdeal A) ∧ L (MvPolynomial.eval (fun j => algebraMap A E (x j)) Φ) = 0 := by
  intro A E _ _ _ _ n Φ L h0 h1
  let G : Fin n → MvPolynomial (Fin n) E → MvPolynomial (Fin n) A := fun i P =>
    ∑ d ∈ P.support, MvPolynomial.monomial d (L (MvPolynomial.coeff d P) i)
  have hG : ∀ i d P, MvPolynomial.coeff d (G i P) = L (MvPolynomial.coeff d P) i := by
    intro i d P
    simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [MvPolynomial.mem_support_iff, not_not] at h
      simp [h]
  have hGadd : ∀ i p q, G i (p + q) = G i p + G i q := by
    intro i p q
    ext d
    rw [MvPolynomial.coeff_add, hG, hG, hG, MvPolynomial.coeff_add, map_add, Pi.add_apply]
  have key : ∀ i (x : Fin n → A) (P : MvPolynomial (Fin n) E),
      MvPolynomial.eval x (G i P) = L (MvPolynomial.eval (fun j => algebraMap A E (x j)) P) i := by
    intro i x P
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      have hm : G i (MvPolynomial.monomial d c) = MvPolynomial.monomial d (L c i) := by
        ext d'
        rw [hG, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
        split_ifs <;> simp
      rw [hm, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      have hp : (d.prod fun k e => (algebraMap A E (x k)) ^ e) = algebraMap A E (d.prod fun k e => x k ^ e) := by
        simp [Finsupp.prod, map_prod, map_pow]
      rw [hp, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
      simp [mul_comm]
    | add p q hp hq =>
      rw [hGadd, map_add, map_add, map_add, Pi.add_apply, hp, hq]
  let F : Fin n → MvPolynomial (Fin n) A := fun i => G i Φ
  have hF0 : ∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A := by
    intro i
    have h := key i 0 Φ
    have e : (fun j => algebraMap A E ((0 : Fin n → A) j)) = 0 := by
      ext
      simp
    rw [e] at h
    show MvPolynomial.eval 0 (G i Φ) ∈ maximalIdeal A
    rw [h]
    exact h0 i
  have hF1 : ∀ i j, MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)) =
      L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i := by
    intro i j
    rw [UpperTheory.eval_zero_pderiv, UpperTheory.eval_zero_pderiv]
    exact hG i _ Φ
  have hdet : IsUnit (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
    have hM : (residue A).mapMatrix (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))) = 1 := by
      ext i j
      have h := (residue_eq_zero_iff _).mpr (h1 i j)
      rw [map_sub, sub_eq_zero] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hF1, h, Matrix.one_apply]
      split_ifs <;> simp
    by_contra hu
    have hm := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
    have h := (residue_eq_zero_iff _).mpr hm
    rw [RingHom.map_det, hM, Matrix.det_one] at h
    exact one_ne_zero h
  obtain ⟨x, hx, hxm⟩ := UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian A n F hF0 hdet
  refine ⟨x, hxm, ?_⟩
  funext i
  rw [← key i x Φ]
  exact hx i

end
