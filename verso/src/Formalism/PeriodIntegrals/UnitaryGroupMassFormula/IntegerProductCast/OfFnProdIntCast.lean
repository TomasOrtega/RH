import Formalism.PeriodIntegrals.QmStar
import Formalism.PeriodIntegrals.QmRowForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

open Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmStar

/- English proof (translation)
The claim follows from `| 0, f => by simp | t + 1, f => by rw [List.ofFn_succ, List.prod_cons, star_mul, star_ofFn_prod (fun i => f i.succ), List.ofFn_succ' (fun i : Fin (t + 1) => star (f i.rev)), List.prod_concat] simp only [Fin.rev_last, Fin.rev_castSucc]`.
-/
theorem star_ofFn_prod {A : Type*} [Ring A] [StarRing A] : ∀ {t : ℕ} (f : Fin t → A),
    star (List.ofFn f).prod = (List.ofFn fun i => star (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, star_mul, star_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => star (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

/- English proof (translation)
The claim follows from `| 0, s, g => by simp | t + 1, s, g => by have ih := ofFn_prod_intCast (fun k => s k.succ) (fun k => g k.succ) rw [List.ofFn_succ, List.prod_cons, ih, List.ofFn_succ (f := g), List.prod_cons, Fin.prod_univ_succ, Int.cast_mul] simp only [mul_assoc] congr 1 rw [← mul_assoc, ← mul_as …`.
-/
theorem ofFn_prod_intCast {A : Type*} [Ring A] : ∀ {t : ℕ} (s : Fin t → ℤ) (g : Fin t → A),
    (List.ofFn fun k => (s k : A) * g k).prod = ((∏ k, s k : ℤ) : A) * (List.ofFn g).prod
  | 0, s, g => by simp
  | t + 1, s, g => by
    have ih := ofFn_prod_intCast (fun k => s k.succ) (fun k => g k.succ)
    rw [List.ofFn_succ, List.prod_cons, ih, List.ofFn_succ (f := g), List.prod_cons,
      Fin.prod_univ_succ, Int.cast_mul]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, Int.cast_comm]

/- English proof (translation)
Unfold `Tm`. Rewrite using `[star_add, hs]`. Distinguish the cases in `h : c = d`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, star_smul, star_one]`.

Conclude with `(one_mul _).symm`. Rewrite using `[if_neg h, if_neg (Ne.symm h), star_zero, zero_add, zero_add]`.
-/
theorem star_Tm {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (u : ℂ) (c d : Fin n) :
    star (Tm E u c d) = (((ε c * ε d : ℤˣ) : ℤ) : A) * Tm E (star u) d c := by
  unfold Tm
  rw [star_add, hs]
  by_cases h : c = d
  · subst h
    rw [if_pos rfl, if_pos rfl, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, star_smul, star_one]
    exact (one_mul _).symm
  · rw [if_neg h, if_neg (Ne.symm h), star_zero, zero_add, zero_add]

def conjRev (t : ℕ) : Equiv.Perm (Fin t) ≃ Equiv.Perm (Fin t) where
  toFun σ := Fin.revPerm * σ * Fin.revPerm
  invFun σ := Fin.revPerm * σ * Fin.revPerm
  left_inv σ := Equiv.ext fun i => by simp [Equiv.Perm.mul_apply]
  right_inv σ := Equiv.ext fun i => by simp [Equiv.Perm.mul_apply]

/- English proof (translation)
Simplify using `[conjRev, Equiv.Perm.mul_apply]`.
-/
theorem conjRev_apply {t : ℕ} (σ : Equiv.Perm (Fin t)) (k : Fin t) : conjRev t σ k = (σ k.rev).rev := by
  simp [conjRev, Equiv.Perm.mul_apply]

/- English proof (translation)
Simplify using `only [conjRev, Equiv.coe_fn_mk, Equiv.Perm.sign_mul]`. Rewrite using `[mul_comm, ← mul_assoc, Int.units_mul_self, one_mul]`.
-/
theorem sign_conjRev {t : ℕ} (σ : Equiv.Perm (Fin t)) :
    Equiv.Perm.sign (conjRev t σ) = Equiv.Perm.sign σ := by
  simp only [conjRev, Equiv.coe_fn_mk, Equiv.Perm.sign_mul]
  rw [mul_comm, ← mul_assoc, Int.units_mul_self, one_mul]

/- English proof (translation)
Rewrite using `[← Units.coe_prod]`. Use `congr 1`. Rewrite using `[Finset.prod_mul_distrib]`. Use `congr 1`. Conclude with `Equiv.prod_comp (Fin.revPerm.trans σ) (fun k => ε (a k))`.

Conclude with `Equiv.prod_comp Fin.revPerm (fun k => ε (b k))`.
-/
theorem prod_signs {n t : ℕ} (ε : Fin n → ℤˣ) (a b : Fin t → Fin n) (σ : Equiv.Perm (Fin t)) :
    (∏ k : Fin t, ((ε (a (σ k.rev)) * ε (b k.rev) : ℤˣ) : ℤ)) =
      (((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) := by
  rw [← Units.coe_prod]
  congr 1
  rw [Finset.prod_mul_distrib]
  congr 1
  · exact Equiv.prod_comp (Fin.revPerm.trans σ) (fun k => ε (a k))
  · exact Equiv.prod_comp Fin.revPerm (fun k => ε (b k))

/- English proof (translation)
Establish `hj` using `j.isLt`. Rewrite using `[star_sub, Fin.val_rev]`. Establish `e : star (((t - (↑j + 1) : ℕ)) : ℂ) = ((t - (↑j + 1) : ℕ) : ℂ)` using `by simp`. Rewrite using `[e, Nat.cast_sub (by omega)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem arg_rev {t : ℕ} (w : ℂ) (j : Fin t) :
    star (w - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = star w - (t : ℂ) + 1 + ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [star_sub, Fin.val_rev]
  have e : star (((t - (↑j + 1) : ℕ)) : ℂ) = ((t - (↑j + 1) : ℕ) : ℂ) := by simp
  rw [e, Nat.cast_sub (by omega)]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[star_mul, star_ofFn_prod]`. Simplify using `only [star_Tm E ε hs, arg_rev]`. Rewrite using `[ofFn_prod_intCast (fun k : Fin t => ((ε (a (σ k.rev)) * ε (b k.rev) : ℤˣ) : ℤ)) (fun k : Fin t => Tm E (star w - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (b k.rev) (a (σ k.rev))), prod_signs, star_intCast, mul_assoc, ← (Int.cast_commute _ _).eq]`.
-/
theorem star_term {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (a b : Fin t → Fin n) (w : ℂ)
    (σ : Equiv.Perm (Fin t)) :
    star ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun k : Fin t => Tm E (w - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).prod) =
      ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) * ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin t =>
          Tm E (star w - (t : ℂ) + 1 + ((j : ℕ) : ℂ)) (b j.rev) (a (σ j.rev))).prod) := by
  rw [star_mul, star_ofFn_prod]
  simp only [star_Tm E ε hs, arg_rev]
  rw [ofFn_prod_intCast (fun k : Fin t => ((ε (a (σ k.rev)) * ε (b k.rev) : ℤˣ) : ℤ))
    (fun k : Fin t => Tm E (star w - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (b k.rev) (a (σ k.rev))),
    prod_signs, star_intCast, mul_assoc, ← (Int.cast_commute _ _).eq]

/- English proof (translation)
Unfold `qminor PI.qminorRow`. Rewrite using `[star_sum]`. Simplify using `only [star_term E ε hs]`. Rewrite using `[← Finset.mul_sum]`. Use `congr 1`.

Rewrite using `[← Equiv.sum_comp (conjRev t)]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[sign_conjRev]`. Use `congr 3`. Use function extensionality and compare the values at `j`.

Simplify using `[conjRev_apply, Function.comp]`.
-/
theorem star_qminor {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (a b : Fin t → Fin n) (w : ℂ) :
    star (qminor E a b w) = ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) *
      PI.qminorRow E (b ∘ Fin.rev) (a ∘ Fin.rev) (star w) := by
  unfold qminor PI.qminorRow
  rw [star_sum]
  simp only [star_term E ε hs]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp (conjRev t)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [sign_conjRev]
  congr 3
  funext j
  simp [conjRev_apply, Function.comp]

/- English proof (translation)
Use `show qminor E (a ∘ (Fin.revPerm : Equiv.Perm (Fin t))) (b ∘ (Fin.revPerm : Equiv.Perm (Fin t))) u = _`. Rewrite using `[quantumMinorRowSkew_holds A n t E a (b ∘ (Fin.revPerm : Equiv.Perm (Fin t))) Fin.revPerm u, quantumMinorColSkew_holds A n t E hE a b Fin.revPerm u, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]`.
-/
theorem qminor_rev_rev {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin t → Fin n) (u : ℂ) : qminor E (a ∘ Fin.rev) (b ∘ Fin.rev) u = qminor E a b u := by
  show qminor E (a ∘ (Fin.revPerm : Equiv.Perm (Fin t))) (b ∘ (Fin.revPerm : Equiv.Perm (Fin t))) u = _
  rw [quantumMinorRowSkew_holds A n t E a (b ∘ (Fin.revPerm : Equiv.Perm (Fin t))) Fin.revPerm u,
    quantumMinorColSkew_holds A n t E hE a b Fin.revPerm u, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]

/- English proof (translation)
Unfold `PI.QmStar PI.StarMinor`. Introduce `A _ _ _ _ n t E ε hE hs a b w`. Rewrite using `[star_qminor E ε hs, ← hrow A n t E hE, qminor_rev_rev E hE]`.
-/
theorem qmStar_of (hrow : PI.RowForm) : PI.QmStar := by
  unfold PI.QmStar PI.StarMinor
  intro A _ _ _ _ n t E ε hE hs a b w
  rw [star_qminor E ε hs, ← hrow A n t E hE, qminor_rev_rev E hE]

/- English proof (translation)
The claim follows from `qmStar_of h`.
-/
theorem qmStar_of_rowForm (h : PI.QmRowForm) : PI.QmStar := qmStar_of h

end PI.UnitaryGroupMassFormula.QmStar
