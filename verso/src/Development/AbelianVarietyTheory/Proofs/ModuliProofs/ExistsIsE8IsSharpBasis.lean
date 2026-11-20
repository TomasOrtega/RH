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
Use function extensionality and compare the values at `u c`. Break down `c with a | a` into its components or cases. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `A.mulVec (B.mulVec (fun w => y w (.inr a))) u = _`. Rewrite using `[Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]`.
-/
theorem twistSnd_twistSnd {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) ℤ) (hAB : A * B = 1)
    (y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) : twistSnd A (twistSnd B y) = y := by
  funext u c
  rcases c with a | a
  · rfl
  · change A.mulVec (B.mulVec (fun w => y w (.inr a))) u = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

/- English proof (translation)
Establish `key : ∀ (z : Fin 8 → ℤ) (u : Fin 8), ∑ v, A u v * B.mulVec z v = z u`. Introduce `z u`. Express the relevant statement in the definitionally equal form `A.mulVec (B.mulVec z) u = _`. Rewrite using `[Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]`. Establish `hs : ∀ u v, A u v = A v u` using `fun u v => by conv_lhs => rw [← hA]`.

Both sides reduce to the same expression. Establish `h1 : ∑ u, ∑ v, A u v * ∑ a, y u (.inl a) * B.mulVec (fun w => y' w (.inr a)) v = ∑ u, ∑ a, y u (.inl a) * y' u (.inr a)`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← key (fun w => y' w (.inr a)) u, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun v _ => by ring`. Establish `h2 : ∑ u, ∑ v, A u v * ∑ a, B.mulVec (fun w => y w (.inr a)) u * y' v (.inl a) = ∑ u, ∑ a, y u (.inr a) * y' u (.inl a)`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← key (fun w => y w (.inr a)) v, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun u _ => by rw [hs u v]; ring`. Simplify using `only [omegaStd, Finset.sum_sub_distrib, mul_sub]`. Rewrite using `[← h1, ← h2]`. Both sides reduce to the same expression.
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
Simplify using `[sharpIndex]`.
-/
theorem sharpIndex_inl (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inl a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) := by
  simp [sharpIndex]

/- English proof (translation)
Simplify using `[sharpIndex]`.
-/
theorem sharpIndex_inr (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inr a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) + 8 * h := by
  simp [sharpIndex]

/- English proof (translation)
Take `⟨⟨u, c⟩, rfl⟩` from `(sharpIndex h).surjective i`. Take `⟨⟨v, d⟩, rfl⟩` from `(sharpIndex h).surjective j`. Establish `hinj : ∀ (u v : Fin 8) (a b : Fin h), ((finProdFinEquiv (u, a) : ℕ) = (finProdFinEquiv (v, b) : ℕ)) ↔ (u = v ∧ a = b)`. Introduce `u v a b`. Rewrite using `[Fin.val_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]`.

Apply the tactic sequence `rcases c with a | a <;> rcases d with b | b`. Use `all_goals`. Establish `h1` using `(finProdFinEquiv (u, a)).isLt`. Establish `h2` using `(finProdFinEquiv (v, b)).isLt`. Establish `h3` using `hinj u v a b`.

Simplify using `only [omegaStd, Out.stdSymp, Pi.single_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq, sharpIndex_inl, sharpIndex_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false, if_false, mul_zero, zero_mul, sub_zero, zero_sub, Finset.sum_const_zero, sub_self]`. Generalize the expression as in `(finProdFinEquiv (u, a) : ℕ) = m at *`. Generalize the expression as in `(finProdFinEquiv (v, b) : ℕ) = n at *`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Distinguish the cases in `huv : u = v ∧ a = b`.

Take `⟨rfl, rfl⟩` from `huv`. Establish `: m = n` using `h3.2 ⟨rfl, rfl⟩`. Rewrite using `[if_pos (by omega)]`. Simplify using `[ite_and]`. Establish `: m ≠ n` using `fun e => huv (h3.1 e)`.

Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Use `Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with p q`. Conclude with `absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv`. Apply the tactic sequence `all_goals simp`.

Distinguish the cases in `huv : u = v ∧ a = b`. Take `⟨rfl, rfl⟩` from `huv`. Establish `: m = n` using `h3.2 ⟨rfl, rfl⟩`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`. Simplify using `[ite_and]`.

Establish `: m ≠ n` using `fun e => huv (h3.1 e)`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Use `Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with p q`. Conclude with `absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv`.

Apply the tactic sequence `all_goals simp`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`.
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
Use `⟨GlobalTheory.W8, ?_, fun h => ?_⟩` and prove the remaining obligations. Unfold `IsE8`. Rewrite using `[GlobalTheory.w8_add_transpose_eq_e8]`. Conclude with `⟨GlobalTheory.e8_posDef, GlobalTheory.e8_det_eq_one⟩`. Set `e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))` to `{ twistSnd GlobalTheory.E8inv with invFun := twistSnd GlobalTheory.E8 left_inv := twistSnd_twistSnd _ _ GlobalTheory.e8_mul_e8inv right_inv := twistSnd_twistSnd _ _ GlobalTheory.e8inv_mul_e8 }`.

Use `⟨(sharpReindex h).trans e, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.w8_add_transpose_eq_e8, ← sum_omegaStd_single h i j]`. Conclude with `sum_omegaStd_twistSnd _ _ GlobalTheory.e8_transpose GlobalTheory.e8_mul_e8inv _ _`.
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
