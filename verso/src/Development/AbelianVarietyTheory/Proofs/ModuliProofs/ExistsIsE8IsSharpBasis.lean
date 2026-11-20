import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

def twistSnd {h : ℕ} (A : Matrix (Fin 8) (Fin 8) ℤ) :
    (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun y := fun u => Sum.elim (fun a => y u (.inl a)) (fun a => A.mulVec (fun w => y w (.inr a)) u)
  map_add' y y' := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Both sides reduce to the same expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem twistSnd_twistSnd {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) ℤ) (hAB : A * B = 1)
    (y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) : twistSnd A (twistSnd B y) = y := by
  funext u c
  rcases c with a | a
  · rfl
  · change A.mulVec (B.mulVec (fun w => y w (.inr a))) u = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Both sides reduce to the same expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem sum_omegaStd_twistSnd {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) ℤ) (hA : A.transpose = A)
    (hAB : A * B = 1) (y y' : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, A u v * omegaStd (twistSnd B y u) (twistSnd B y' v) = ∑ u, omegaStd (y u) (y' u) := by
  have key : ∀ (z : Fin 8 → ℤ) (u : Fin 8), ∑ v, A u v * B.mulVec z v = z u := by
    intro z u
    change A.mulVec (B.mulVec z) u = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  have hs : ∀ u v, A u v = A v u := fun u v => by
    conv_lhs => rw [← hA]
    rfl
  have h1 : ∑ u, ∑ v, A u v * ∑ a, y u (.inl a) * B.mulVec (fun w => y' w (.inr a)) v
      = ∑ u, ∑ a, y u (.inl a) * y' u (.inr a) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key (fun w => y' w (.inr a)) u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : ∑ u, ∑ v, A u v * ∑ a, B.mulVec (fun w => y w (.inr a)) u * y' v (.inl a)
      = ∑ u, ∑ a, y u (.inr a) * y' u (.inl a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key (fun w => y w (.inr a)) v, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [hs u v]; ring
  simp only [omegaStd, Finset.sum_sub_distrib, mul_sub]
  rw [← h1, ← h2]
  rfl

def sharpIndex (h : ℕ) : Fin 8 × (Fin h ⊕ Fin h) ≃ Fin (2 * (8 * h)) :=
  (Equiv.prodSumDistrib _ _ _).trans <|
    (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans <|
      finSumFinEquiv.trans (finCongr (two_mul _).symm)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sharpIndex_inl (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inl a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) := by
  simp [sharpIndex]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sharpIndex_inr (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inr a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) + 8 * h := by
  simp [sharpIndex]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sum_omegaStd_single (h : ℕ) (i j : Fin (2 * (8 * h))) :
    ∑ u, omegaStd (fun c => (Pi.single i 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c)))
      (fun c => (Pi.single j 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c))) = Out.stdSymp (8 * h) i j := by
  obtain ⟨⟨u, c⟩, rfl⟩ := (sharpIndex h).surjective i
  obtain ⟨⟨v, d⟩, rfl⟩ := (sharpIndex h).surjective j
  have hinj : ∀ (u v : Fin 8) (a b : Fin h),
      ((finProdFinEquiv (u, a) : ℕ) = (finProdFinEquiv (v, b) : ℕ)) ↔ (u = v ∧ a = b) := by
    intro u v a b
    rw [Fin.val_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  rcases c with a | a <;> rcases d with b | b
  all_goals
    have h1 := (finProdFinEquiv (u, a)).isLt
    have h2 := (finProdFinEquiv (v, b)).isLt
    have h3 := hinj u v a b
    simp only [omegaStd, Out.stdSymp, Pi.single_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq,
      sharpIndex_inl, sharpIndex_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
      if_false, mul_zero, zero_mul, sub_zero, zero_sub, Finset.sum_const_zero, sub_self]
    generalize (finProdFinEquiv (u, a) : ℕ) = m at *
    generalize (finProdFinEquiv (v, b) : ℕ) = n at *
  · rw [if_neg (by omega), if_neg (by omega)]
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_neg (by omega), if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · rw [if_neg (by omega), if_neg (by omega)]

def sharpReindex (h : ℕ) : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun x := fun u c => x (sharpIndex h (u, c))
  invFun y := fun i => y ((sharpIndex h).symm i).1 ((sharpIndex h).symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext i; simp
  right_inv y := by funext u c; simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isE8_isSharpBasis : ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ∀ h : ℕ, ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  refine ⟨GlobalTheory.W8, ?_, fun h => ?_⟩
  · unfold IsE8
    rw [GlobalTheory.w8_add_transpose_eq_e8]
    exact ⟨GlobalTheory.e8_posDef, GlobalTheory.e8_det_eq_one⟩
  · let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
      { twistSnd GlobalTheory.E8inv with
        invFun := twistSnd GlobalTheory.E8
        left_inv := twistSnd_twistSnd _ _ GlobalTheory.e8_mul_e8inv
        right_inv := twistSnd_twistSnd _ _ GlobalTheory.e8inv_mul_e8 }
    refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
    rw [GlobalTheory.w8_add_transpose_eq_e8, ← sum_omegaStd_single h i j]
    exact sum_omegaStd_twistSnd _ _ GlobalTheory.e8_transpose GlobalTheory.e8_mul_e8inv _ _

end GlobalTheory.ZM
end
