import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.SumCCMulSumOfMulEqOne

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

/- English proof (translation)
Rewrite using `[divDer, coeff_sum]`. Rewrite using `[Finset.sum_congr rfl (g := fun m => if m = μ + be then coeff m F * ((be.prod fun k j => (m k).choose j : ℕ) : R) else 0)]`. Rewrite using `[Finset.sum_ite_eq'] split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.mp h, zero_mul]`.

Introduce `m _`. Distinguish the cases in `h1 : be ≤ m`. Rewrite using `[if_pos h1, coeff_monomial]`. Distinguish the cases in `h2 : m = μ + be`. Substitute `h2` using the available equality.

Rewrite using `[if_pos (add_tsub_cancel_right μ be), if_pos rfl]`. Rewrite using `[if_neg h2, if_neg]`. Introduce `h3`. Apply `h2` to reduce the goal to its premises. Rewrite using `[← h3, tsub_add_cancel_of_le h1]`.

Rewrite using `[if_neg h1, coeff_zero, if_neg]`. Introduce and unpack `rfl`. Conclude with `h1 le_add_self`.
-/
theorem coeff_divDer (be μ : ι × Fin n →₀ ℕ) (F : MvPolynomial (ι × Fin n) R) :
    coeff μ (divDer be F) = coeff (μ + be) F * ((be.prod fun k j => ((μ + be) k).choose j : ℕ) : R) := by
  classical
  rw [divDer, coeff_sum]
  rw [Finset.sum_congr rfl (g := fun m => if m = μ + be then
      coeff m F * ((be.prod fun k j => (m k).choose j : ℕ) : R) else 0)]
  · rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, zero_mul]
  · intro m _
    by_cases h1 : be ≤ m
    · rw [if_pos h1, coeff_monomial]
      by_cases h2 : m = μ + be
      · subst h2
        rw [if_pos (add_tsub_cancel_right μ be), if_pos rfl]
      · rw [if_neg h2, if_neg]
        intro h3
        apply h2
        rw [← h3, tsub_add_cancel_of_le h1]
    · rw [if_neg h1, coeff_zero, if_neg]
      rintro rfl
      exact h1 le_add_self

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[coeff_divDer]`. Simplify using the standard rewrite rules.
-/
theorem divDer_zero' (F : MvPolynomial (ι × Fin n) R) : divDer 0 F = F := by
  ext μ
  rw [coeff_divDer]
  simp

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Use extensionality with `μ`. Rewrite using `[coeff_divDer, pderiv_monomial, coeff_monomial, coeff_monomial]`. Distinguish the cases in `h : u = μ + Finsupp.single v 1`.

Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos (add_tsub_cancel_right μ _)]`. Simplify using `[Finsupp.prod_single_index, Nat.choose_one_right]`. Rewrite using `[if_neg h, zero_mul] split_ifs with h2`. Establish `hv : u v = 0`.

Assume the negation of the conclusion as `hv`. Establish `hle : Finsupp.single v 1 ≤ u` using `Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)`. Apply `h` to reduce the goal to its premises. Rewrite using `[← h2, tsub_add_cancel_of_le hle]`. Rewrite using `[hv, Nat.cast_zero, mul_zero]`.

Both sides reduce to the same expression. Consider the case `add p q hp hq`. Rewrite using `[map_add, ← hp, ← hq]`. Use extensionality with `μ`. Rewrite using `[coeff_add, coeff_divDer, coeff_divDer, coeff_divDer, coeff_add, add_mul]`.
-/
theorem divDer_single_one (v : ι × Fin n) (F : MvPolynomial (ι × Fin n) R) :
    divDer (Finsupp.single v 1) F = pderiv v F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    ext μ
    rw [coeff_divDer, pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = μ + Finsupp.single v 1
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_right μ _)]
      simp [Finsupp.prod_single_index, Nat.choose_one_right]
    · rw [if_neg h, zero_mul]
      split_ifs with h2
      · have hv : u v = 0 := by
          by_contra hv
          have hle : Finsupp.single v 1 ≤ u :=
            Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          apply h
          rw [← h2, tsub_add_cancel_of_le hle]
        rw [hv, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq]
    ext μ
    rw [coeff_add, coeff_divDer, coeff_divDer, coeff_divDer, coeff_add, add_mul]

/- English proof (translation)
Simplify using `[vecDeg]`.
-/
theorem vecDeg_zero' (S : Set ι) : vecDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [vecDeg]

/- English proof (translation)
Simplify using `[covDeg]`.
-/
theorem covDeg_zero' (S : Set ι) : covDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [covDeg]

/- English proof (translation)
Rewrite using `[vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem vecDeg_single_le (S : Set ι) (v : ι × Fin n) : vecDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem covDeg_single_le (S : Set ι) (v : ι × Fin n) : covDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Rewrite `h2` using `[h h1]`. Conclude with `absurd h2 (by decide)`.
-/
theorem vecDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    vecDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

/- English proof (translation)
Rewrite using `[covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Rewrite `h2` using `[h h1]`. Conclude with `absurd h2 (by decide)`.
-/
theorem covDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    covDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem X_eq_monomial' (v : ι × Fin n) : (X v : MvPolynomial (ι × Fin n) R) = monomial (Finsupp.single v 1) 1 := rfl

/- English proof (translation)
Simplify using `[twistSub, h]`.
-/
theorem twistSub_X_out (j : Fin n) (v : ι × Fin n) (h : v.1 ∉ S) :
    twistSub (R := R) LL S j (X v) = X v := by
  simp [twistSub, h]

/- English proof (translation)
Rewrite `h`, the goal using `[laurentCoeffFiltration, flt_lift_mem]`. Introduce `m`. Establish `hm` using `h (Finsupp.single v 1 + m)`. Rewrite `hm` using `[coeff_X_mul]`. Simplify using `using hm`.
-/
theorem mem_of_X_mul_mem {e t : ℤ} (v : ι × Fin n) (P : MvPolynomial (ι × Fin n) (GLLaurent R n))
    (h : X v * P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t := by
  rw [laurentCoeffFiltration, flt_lift_mem] at h ⊢
  intro m
  have hm := h (Finsupp.single v 1 + m)
  rw [coeff_X_mul] at hm
  simpa using hm

/- English proof (translation)
Establish `hv` using `flt_op_valS LL S F (Finsupp.single v 1) 0 0 (by rw [covDeg_single_of LL S v h, vecDeg_zero'])`. Rewrite `hv` using `[divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithTop.coe_zero, add_zero]`. Conclude with `hv`.
-/
theorem valS_X_mul_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    valS LL S F ≤ valS LL S (X v * F) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 0
    (by rw [covDeg_single_of LL S v h, vecDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithTop.coe_zero, add_zero] at hv
  exact hv

/- English proof (translation)
Establish `hv` using `flt_op_valS LL S F (Finsupp.single v 1) 0 1 (by rw [vecDeg_zero', add_zero]; exact covDeg_single_le LL S v)`. Rewrite `hv` using `[divDer_zero', ← X_eq_monomial', Nat.cast_one]`. Conclude with `hv`.
-/
theorem valS_X_mul (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (X v * F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 1
    (by rw [vecDeg_zero', add_zero]; exact covDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

/- English proof (translation)
Establish `hv` using `flt_op_valS LL S F 0 (Finsupp.single v 1) 0 (by rw [covDeg_zero', vecDeg_single_of LL S v h])`. Rewrite `hv` using `[divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero, WithTop.coe_zero, add_zero]`. Conclude with `hv`.
-/
theorem valS_pderiv_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    valS LL S F ≤ valS LL S (pderiv v F) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 0
    (by rw [covDeg_zero', vecDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithTop.coe_zero, add_zero] at hv
  exact hv

/- English proof (translation)
Establish `hv` using `flt_op_valS LL S F 0 (Finsupp.single v 1) 1 (by rw [covDeg_zero', zero_add]; exact vecDeg_single_le LL S v)`. Rewrite `hv` using `[divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one]`. Conclude with `hv`.
-/
theorem valS_pderiv (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (pderiv v F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 1
    (by rw [covDeg_zero', zero_add]; exact vecDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv

/- English proof (translation)
Consider the cases of `b with`. Consider the case `top => exact le_top`. Consider the case `coe m`. Consider the cases of `a with`. Consider the case `top => exact absurd (WithTop.coe_le_coe.mp (h (m + 1) le_top)) (by omega)`.

Consider the case `coe k => exact h k le_rfl`.
-/
private lemma withTop_int_le_of_forall_coe_le {a b : WithTop ℤ}
    (h : ∀ t : ℤ, (t : WithTop ℤ) ≤ a → (t : WithTop ℤ) ≤ b) : a ≤ b := by
  cases b with
  | top => exact le_top
  | coe m =>
    cases a with
    | top => exact absurd (WithTop.coe_le_coe.mp (h (m + 1) le_top)) (by omega)
    | coe k => exact h k le_rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `withTop_int_le_of_forall_coe_le` to reduce the goal to its premises. Introduce `t ht`. Rewrite `ht`, the goal using `[flt_le_valS]`. Rewrite `ht` using `[map_mul, twistSub_X_out LL S _ v h]`.

Conclude with `mem_of_X_mul_mem v _ ht`. Conclude with `valS_X_mul_of LL S F v (fun hv => absurd hv h)`.
-/
theorem valS_X_mul_out (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∉ S) :
    valS LL S (X v * F) = valS LL S F := by
  apply le_antisymm
  · apply withTop_int_le_of_forall_coe_le
    intro t ht
    rw [flt_le_valS] at ht ⊢
    rw [map_mul, twistSub_X_out LL S _ v h] at ht
    exact mem_of_X_mul_mem v _ ht
  · exact valS_X_mul_of LL S F v (fun hv => absurd hv h)

/- English proof (translation)
Establish `hv` using `flt_op_lam1S LL S F (Finsupp.single v 1) 0 0 (by rw [vecDeg_single_of LL S v h, covDeg_zero'])`. Rewrite `hv` using `[divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithBot.coe_zero, add_zero]`. Conclude with `hv`.
-/
theorem maxTwistDegree_X_mul_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    lam1S LL S (X v * F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 0
    (by rw [vecDeg_single_of LL S v h, covDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithBot.coe_zero, add_zero] at hv
  exact hv

/- English proof (translation)
Establish `hv` using `flt_op_lam1S LL S F (Finsupp.single v 1) 0 1 (by rw [covDeg_zero', add_zero]; exact vecDeg_single_le LL S v)`. Rewrite `hv` using `[divDer_zero', ← X_eq_monomial', Nat.cast_one]`. Conclude with `hv`.
-/
theorem maxTwistDegree_X_mul_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (X v * F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 1
    (by rw [covDeg_zero', add_zero]; exact vecDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

/- English proof (translation)
Establish `hv` using `flt_op_lam1S LL S F 0 (Finsupp.single v 1) 0 (by rw [vecDeg_zero', covDeg_single_of LL S v h])`. Rewrite `hv` using `[divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero, WithBot.coe_zero, add_zero]`. Conclude with `hv`.
-/
theorem maxTwistDegree_pderiv_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 0
    (by rw [vecDeg_zero', covDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithBot.coe_zero, add_zero] at hv
  exact hv

/- English proof (translation)
Establish `hv` using `flt_op_lam1S LL S F 0 (Finsupp.single v 1) 1 (by rw [vecDeg_zero', zero_add]; exact covDeg_single_le LL S v)`. Rewrite `hv` using `[divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one]`. Conclude with `hv`.
-/
theorem maxTwistDegree_pderiv_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 1
    (by rw [vecDeg_zero', zero_add]; exact covDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv

/- English proof (translation)
Consider the cases of `a with`. Consider the case `bot => exact bot_le`. Consider the case `coe k`. Consider the cases of `b with`. Consider the case `bot => exact absurd (WithBot.coe_le_coe.mp (h (k - 1) bot_le)) (by omega)`.

Consider the case `coe m => exact h m le_rfl`.
-/
private lemma withBot_int_le_of_forall_le_coe {a b : WithBot ℤ}
    (h : ∀ M : ℤ, b ≤ (M : WithBot ℤ) → a ≤ (M : WithBot ℤ)) : a ≤ b := by
  cases a with
  | bot => exact bot_le
  | coe k =>
    cases b with
    | bot => exact absurd (WithBot.coe_le_coe.mp (h (k - 1) bot_le)) (by omega)
    | coe m => exact h m le_rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `maxTwistDegree_X_mul_le_of LL S F v (fun hv => absurd hv h)`. Apply `withBot_int_le_of_forall_le_coe` to reduce the goal to its premises. Introduce `M hM`. Rewrite `hM`, the goal using `[flt_lam1S_le]`.

Rewrite `hM` using `[map_mul, twistSub_X_out LL S _ v h]`. Conclude with `mem_of_X_mul_mem v _ hM`.
-/
theorem maxTwistDegree_X_mul_of_not_mem (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∉ S) :
    lam1S LL S (X v * F) = lam1S LL S F := by
  apply le_antisymm
  · exact maxTwistDegree_X_mul_le_of LL S F v (fun hv => absurd hv h)
  · apply withBot_int_le_of_forall_le_coe
    intro M hM
    rw [flt_lam1S_le] at hM ⊢
    rw [map_mul, twistSub_X_out LL S _ v h] at hM
    exact mem_of_X_mul_mem v _ hM

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
