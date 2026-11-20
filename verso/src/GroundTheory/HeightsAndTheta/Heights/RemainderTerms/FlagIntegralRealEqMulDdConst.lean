import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoeffRenameProdCongrRight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def flagIntegralReal (f N : ℕ) : MvPolynomial (Fin f × Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun G := ∑ α ∈ (blockVandermonde f N).support,
    coeff α G * ((coeff α (blockVandermonde f N) : ℚ) : ℝ) * α.prod (fun _ e => (e.factorial : ℝ))
  map_add' G H := by simp only [coeff_add, add_mul, sum_add_distrib]
  map_smul' c G := by simp only [coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[flagIntegralReal, flagIntegral, coeff_map, Finsupp.prod]`.
-/
theorem flagIntegralReal_map (f N : ℕ) (Φ : RootRing f N) :
    flagIntegralReal f N (map (algebraMap ℚ ℝ) Φ) = (flagIntegral f N Φ : ℝ) := by
  simp [flagIntegralReal, flagIntegral, coeff_map, Finsupp.prod]

namespace FlagEq

/- English proof (translation)
Establish `hsub : (blockVandermonde f N).support ⊆ (blockVandermonde f N).support ∪ univ.image (stairExp f N)` using `subset_union_left`. Use `show ∑ α ∈ _, _ = _`. Rewrite using `[sum_subset hsub (fun α _ hα => by rw [notMem_support_iff.mp hα]; simp)]`. Establish `hc : ∀ α : Fin f × Fin N →₀ ℕ, ((coeff α (blockVandermonde f N) : ℚ) : ℝ) = ∑ w, ((permSign f N w : ℤ) : ℝ) * if stairExp f N w = α then 1 else 0`. Introduce `α`.

Rewrite using `[coeff_blockVandermonde, Rat.cast_sum]`. Use `sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [hc, mul_sum, sum_mul]`. Rewrite using `[sum_comm]`.

Use `sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]`. Rewrite using `[sum_ite_eq, if_pos (mem_union_right _ (mem_image_of_mem _ (mem_univ w))), prod_factorial_stairExp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flagIntegralReal_eq {f N : ℕ} (G : MvPolynomial (Fin f × Fin N) ℝ) :
    flagIntegralReal f N G =
      stairConst f N * ∑ w, ((permSign f N w : ℤ) : ℝ) * coeff (stairExp f N w) G := by
  classical
  have hsub : (blockVandermonde f N).support ⊆
      (blockVandermonde f N).support ∪ univ.image (stairExp f N) := subset_union_left
  show ∑ α ∈ _, _ = _
  rw [sum_subset hsub (fun α _ hα => by rw [notMem_support_iff.mp hα]; simp)]
  have hc : ∀ α : Fin f × Fin N →₀ ℕ, ((coeff α (blockVandermonde f N) : ℚ) : ℝ) =
      ∑ w, ((permSign f N w : ℤ) : ℝ) * if stairExp f N w = α then 1 else 0 := by
    intro α
    rw [coeff_blockVandermonde, Rat.cast_sum]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hc, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [sum_ite_eq, if_pos (mem_union_right _ (mem_image_of_mem _ (mem_univ w))),
    prod_factorial_stairExp]
  ring

/- English proof (translation)
Simplify using `[IndefiniteRowSideFullHecke.RestTerms.ddConst, IndefiniteRowSideFullHecke.RestTerms.blockAntisym, permSign, rho, IndefiniteRowSideFullHecke.RestTerms.rhoMon, coeff_sum, coeff_smul, smul_eq_mul]`.
-/
theorem ddConst_apply (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      coeff (rho f (j + k)) (∑ w : Fin f → Equiv.Perm (Fin (j + k)),
        ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G) := by
  simp [IndefiniteRowSideFullHecke.RestTerms.ddConst, IndefiniteRowSideFullHecke.RestTerms.blockAntisym, permSign, rho,
    IndefiniteRowSideFullHecke.RestTerms.rhoMon, coeff_sum, coeff_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[ddConst_apply, coeff_rho_antisym]`.
-/
theorem ddConst_eq (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      ∑ w, ((permSign f (j + k) w : ℤ) : ℝ) * coeff (stairExp f (j + k) w) G := by
  rw [ddConst_apply, coeff_rho_antisym]

/- English proof (translation)
Simplify using `only [IndefiniteRowSideFullHecke.RestTerms.psumAt, map_sum, map_pow, rename_X, Equiv.prodCongrRight_apply]`. Conclude with `Equiv.sum_comp (w τ) (fun i => (X (τ, i) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) ^ m)`.
-/
theorem rename_psumAt (f j k m : ℕ) (τ : Fin f) (w : Fin f → Equiv.Perm (Fin (j + k))) :
    rename (Equiv.prodCongrRight w) (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by
  simp only [IndefiniteRowSideFullHecke.RestTerms.psumAt, map_sum, map_pow, rename_X, Equiv.prodCongrRight_apply]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) ^ m)

def antisym (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G

/- English proof (translation)
Simplify using `only [antisym, map_mul, rename_psumAt, mul_sum, mul_smul_comm]`.
-/
theorem antisym_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    antisym f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * antisym f j k G := by
  simp only [antisym, map_mul, rename_psumAt, mul_sum, mul_smul_comm]

/- English proof (translation)
Establish `hcomp : ∀ w : Fin f → Equiv.Perm (Fin (j + k)), rename (Equiv.prodCongrRight u) (rename (Equiv.prodCongrRight w) G) = rename (Equiv.prodCongrRight (u * w)) G`. Introduce `w`. Rewrite using `[rename_rename]`. Use `congr 1`. Establish `hs : ((permSign f (j + k) u : ℤ) : ℝ) * ((permSign f (j + k) u : ℤ) : ℝ) = 1`.

Conclude with `permSign_mul_self u` after adjusting the coercions. Simplify using `only [antisym, map_sum, map_smul, hcomp, smul_sum, smul_smul]`. Use `Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun w => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, permSign_mul]`. Use `push_cast`.

Rewrite using `[← mul_assoc, hs, one_mul]`.
-/
theorem rename_antisym (f j k : ℕ) (u : Fin f → Equiv.Perm (Fin (j + k)))
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    rename (Equiv.prodCongrRight u) (antisym f j k G) =
      ((permSign f (j + k) u : ℤ) : ℝ) • antisym f j k G := by
  have hcomp : ∀ w : Fin f → Equiv.Perm (Fin (j + k)),
      rename (Equiv.prodCongrRight u) (rename (Equiv.prodCongrRight w) G) =
        rename (Equiv.prodCongrRight (u * w)) G := by
    intro w
    rw [rename_rename]
    congr 1
  have hs : ((permSign f (j + k) u : ℤ) : ℝ) * ((permSign f (j + k) u : ℤ) : ℝ) = 1 := by
    exact_mod_cast permSign_mul_self u
  simp only [antisym, map_sum, map_smul, hcomp, smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft, permSign_mul]
  push_cast
  rw [← mul_assoc, hs, one_mul]

/- English proof (translation)
Set `u : Fin f → Equiv.Perm (Fin N)` to `Pi.mulSingle τ (Equiv.swap i i')`. Establish `hu1 : u τ = Equiv.swap i i'` using `Pi.mulSingle_eq_same _ _`. Establish `hu2 : ∀ τ', τ' ≠ τ → u τ' = 1` using `fun τ' h => Pi.mulSingle_eq_of_ne h _`. Establish `hs : permSign f N u = -1`. Rewrite using `[permSign, Fintype.prod_eq_single τ]`.

Rewrite using `[hu1, Equiv.Perm.sign_swap hii]`. Both sides reduce to the same expression. Introduce `τ' h`. Rewrite using `[hu2 τ' h]`. Simplify using the standard rewrite rules.

Establish `hfix : (Finsupp.equivFunOnFinite.symm fun v => β (Equiv.prodCongrRight u v)) = β`. Use extensionality with `⟨τ', l⟩`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm, Equiv.prodCongrRight_apply]`. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality.

Rewrite using `[hu1]`. Break down `eq_or_ne l i with rfl | h1` into its components or cases. Rewrite using `[Equiv.swap_apply_left, hβ]`. Break down `eq_or_ne l i' with rfl | h2` into its components or cases. Rewrite using `[Equiv.swap_apply_right, hβ]`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne h1 h2]`. Rewrite using `[hu2 τ' h]`. Both sides reduce to the same expression. Establish `h` using `congrArg (coeff β) (hA u)`. Rewrite `h` using `[coeff_rename_prodCongrRight, hfix, hs, coeff_smul, smul_eq_mul]`.

Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coeff_eq_zero_of_swap {f N : ℕ} (A : MvPolynomial (Fin f × Fin N) ℝ)
    (hA : ∀ u : Fin f → Equiv.Perm (Fin N),
      rename (Equiv.prodCongrRight u) A = ((permSign f N u : ℤ) : ℝ) • A)
    (β : Fin f × Fin N →₀ ℕ) (τ : Fin f) (i i' : Fin N) (hii : i ≠ i')
    (hβ : β (τ, i) = β (τ, i')) : coeff β A = 0 := by
  classical
  let u : Fin f → Equiv.Perm (Fin N) := Pi.mulSingle τ (Equiv.swap i i')
  have hu1 : u τ = Equiv.swap i i' := Pi.mulSingle_eq_same _ _
  have hu2 : ∀ τ', τ' ≠ τ → u τ' = 1 := fun τ' h => Pi.mulSingle_eq_of_ne h _
  have hs : permSign f N u = -1 := by
    rw [permSign, Fintype.prod_eq_single τ]
    · rw [hu1, Equiv.Perm.sign_swap hii]; rfl
    · intro τ' h; rw [hu2 τ' h]; simp
  have hfix : (Finsupp.equivFunOnFinite.symm fun v => β (Equiv.prodCongrRight u v)) = β := by
    ext ⟨τ', l⟩
    simp only [Finsupp.coe_equivFunOnFinite_symm, Equiv.prodCongrRight_apply]
    by_cases h : τ' = τ
    · subst h
      rw [hu1]
      rcases eq_or_ne l i with rfl | h1
      · rw [Equiv.swap_apply_left, hβ]
      · rcases eq_or_ne l i' with rfl | h2
        · rw [Equiv.swap_apply_right, hβ]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [hu2 τ' h]; rfl
  have h := congrArg (coeff β) (hA u)
  rw [coeff_rename_prodCongrRight, hfix, hs, coeff_smul, smul_eq_mul] at h
  push_cast at h
  linarith

/- English proof (translation)
Rewrite using `[ddConst_apply, ← antisym, antisym_psumAt_mul, IndefiniteRowSideFullHecke.RestTerms.psumAt, sum_mul, coeff_sum]`. Use `sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[X_pow_eq_monomial, coeff_monomial_mul']`. Use `split_ifs with h`. Rewrite `h` using `[Finsupp.single_le_iff]`.

Simplify using `only [rho, Finsupp.coe_equivFunOnFinite_symm] at h`. Establish `hi : (i : ℕ) + m < j + k` using `by have := i.isLt; omega`. Establish `hii : i ≠ ⟨(i : ℕ) + m, hi⟩`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[coeff_eq_zero_of_swap _ (fun u => rename_antisym f j k u G) _ τ i ⟨(i : ℕ) + m, hi⟩ hii, mul_zero]`. Rewrite using `[Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by intro h'; simp at h'; exact hii h'.symm)]`. Simplify using `only [rho, Finsupp.coe_equivFunOnFinite_symm]`.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem ddConst_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hm : 1 ≤ m) : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0 := by
  classical
  rw [ddConst_apply, ← antisym, antisym_psumAt_mul, IndefiniteRowSideFullHecke.RestTerms.psumAt, sum_mul, coeff_sum]
  refine sum_eq_zero fun i _ => ?_
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [Finsupp.single_le_iff] at h
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm] at h
    have hi : (i : ℕ) + m < j + k := by have := i.isLt; omega
    have hii : i ≠ ⟨(i : ℕ) + m, hi⟩ := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    rw [coeff_eq_zero_of_swap _ (fun u => rename_antisym f j k u G) _ τ i ⟨(i : ℕ) + m, hi⟩ hii, mul_zero]
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by intro h'; simp at h'; exact hii h'.symm)]
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm]
    omega
  · rfl

/- English proof (translation)
Rewrite using `[ddConst_eq, Fintype.sum_eq_single 1]`. Simplify using `[stairExp_one, permSign_one]`. Introduce `w hw`. Rewrite using `[coeff_monomial, if_neg (fun h => hw (eq_one_of_stairExp_eq w h.symm)), mul_zero]`.
-/
theorem ddConst_monomial_rho (f j k : ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (monomial (rho f (j + k)) (1 : ℝ)) = 1 := by
  rw [ddConst_eq, Fintype.sum_eq_single 1]
  · simp [stairExp_one, permSign_one]
  · intro w hw
    rw [coeff_monomial, if_neg (fun h => hw (eq_one_of_stairExp_eq w h.symm)), mul_zero]

end FlagEq

open FlagEq in

/- English proof (translation)
Rewrite using `[flagIntegralReal_eq, ddConst_eq]`.
-/
theorem flagIntegralReal_eq_mul_ddConst (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    flagIntegralReal f (j + k) G = stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G := by
  rw [flagIntegralReal_eq, ddConst_eq]

end

end GroundTheory.Heights₂.Heights.RestTerms
