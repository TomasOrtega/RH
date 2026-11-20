import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotAlgIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

namespace FlagPivotAlgIndep

variable (F : Type) [Field F] (n : ℕ)

abbrev genFrac (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  algebraMap (MvPolynomial (Fin n × Fin n) F) _ (X p)

/- English proof (translation)
Simplify using `only [genFrac, ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `X_ne_zero p`.
-/
theorem genFrac_ne_zero (p : Fin n × Fin n) : genFrac F n p ≠ 0 := by
  simp only [genFrac, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact X_ne_zero p

def spec (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  if (p.2 : ℕ) < p.1 then 0
  else if h : (p.1 : ℕ) = 0 then genFrac F n p
  else genFrac F n p / genFrac F n (⟨p.1 - 1, by omega⟩, ⟨p.1 - 1, by omega⟩)

/- English proof (translation)
Proceed by induction on `m generalizing c with`. Consider the case `zero => simp [spec]`. Consider the case `succ m ih`. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using `only [Fin.val_castSucc, Fin.val_last]`.

Rewrite using `[ih (by omega) ⟨m, by omega⟩ le_rfl]`. Establish `e : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩` using `Fin.ext (by simp)`. Simplify using `only [spec, show ¬ ((c : ℕ) < m + 1) by omega, if_false, show m + 1 ≠ 0 by omega, dif_neg, not_false_eq_true, e]`. Conclude with `mul_div_cancel₀ _ (genFrac_ne_zero F n _)`.
-/
theorem prod_spec (m : ℕ) (hm : m < n) (c : Fin n) (hc : m ≤ (c : ℕ)) :
    (∏ i : Fin m, spec F n (⟨i, by omega⟩, ⟨i, by omega⟩)) * spec F n (⟨m, hm⟩, c) = genFrac F n (⟨m, hm⟩, c) := by
  induction m generalizing c with
  | zero => simp [spec]
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega) ⟨m, by omega⟩ le_rfl]
    have e : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext (by simp)
    simp only [spec, show ¬ ((c : ℕ) < m + 1) by omega, if_false, show m + 1 ≠ 0 by omega, dif_neg, not_false_eq_true, e]
    exact mul_div_cancel₀ _ (genFrac_ne_zero F n _)

/- English proof (translation)
Establish `ha : (a : ℕ) < n` using `by have := a.2; omega`. Unfold `pivotMinor`. Rewrite using `[AlgHom.map_det, Matrix.det_of_isUpperTriangular]`. Rewrite using `[Fin.prod_univ_castSucc]`. Use `Eq.trans ?_ (prod_spec F n a ha b hab)` and prove the remaining obligations.

Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]`. Both sides reduce to the same expression. Simplify using `[AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]`.

Both sides reduce to the same expression. Introduce `i j hji`. Establish `hji' : (j : ℕ) < i` using `hji`. Establish `hj : (j : ℕ) < a` using `by have := i.2; omega`. Simplify using `[AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X, spec, hj, hji']`.
-/
theorem spec_pivotMinor (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    aeval (spec F n) (pivotMinor (genMat F n) a b) = genFrac F n (Fin.castLE (Nat.sub_le n 1) a, b) := by
  have ha : (a : ℕ) < n := by have := a.2; omega
  unfold pivotMinor
  rw [AlgHom.map_det, Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_castSucc]
    refine Eq.trans ?_ (prod_spec F n a ha b hab)
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
    · simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
  · intro i j hji
    have hji' : (j : ℕ) < i := hji
    have hj : (j : ℕ) < a := by have := i.2; omega
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X, spec, hj, hji']

/- English proof (translation)
Introduce `F _ n`. Use `AlgebraicIndependent.of_comp (aeval (spec F n)) ?_` and prove the remaining obligations. Establish `hfun : ⇑(aeval (spec F n)) ∘ (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1) = ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (FractionRing (MvPolynomial (Fin n × Fin n) F))) ∘ ((X : Fin n × Fin n → MvPolynomial (Fin n × F …`. Use function extensionality and compare the values at `q`. Conclude with `spec_pivotMinor F n q.1 q.2.1 q.2.2`.

Rewrite using `[hfun]`. Use `AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)` and prove the remaining obligations. Use `(algebraicIndependent_X (Fin n × Fin n) F).comp _ ?_` and prove the remaining obligations. Introduce and unpack `⟨a, b, hb⟩ ⟨a', b', hb'⟩ h`. Simplify using `only [Prod.mk.injEq] at h`.

Take `⟨h1, h2⟩` from `h`. Establish `h1' : a = a'` using `Fin.ext (by simpa using congrArg Fin.val h1)`. Substitute `h1' h2` using the available equality. Both sides reduce to the same expression.
-/
theorem proof : FlagPivotAlgIndep.Statement := by
  intro F _ n
  refine AlgebraicIndependent.of_comp (aeval (spec F n)) ?_
  have hfun : ⇑(aeval (spec F n)) ∘
        (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1) =
      ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (FractionRing (MvPolynomial (Fin n × Fin n) F))) ∘
        ((X : Fin n × Fin n → MvPolynomial (Fin n × Fin n) F) ∘
          fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => (Fin.castLE (Nat.sub_le n 1) q.1, q.2.1)) := by
    funext q
    exact spec_pivotMinor F n q.1 q.2.1 q.2.2
  rw [hfun]
  refine AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)
  refine (algebraicIndependent_X (Fin n × Fin n) F).comp _ ?_
  rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : a = a' := Fin.ext (by simpa using congrArg Fin.val h1)
  subst h1' h2
  rfl

end FlagPivotAlgIndep

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
