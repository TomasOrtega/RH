import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.SignatureAddition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use `conv_rhs => rw [← B.frame.sum_repr x, ← B.frame.sum_repr y]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, HSpace.gram, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations.
-/
theorem coords_gram (B : HSpace E) (x y : B.V) :
    ∑ l, (∑ k, star (B.frame.repr x k) * B.gram k l) * B.frame.repr y l = B.hT x y := by
  conv_rhs => rw [← B.frame.sum_repr x, ← B.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, HSpace.gram, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

def middleSymmetricBasisVector (E : Type) [Field E] (c : ℕ) (p : Fin c) : Fin c → E :=
  Pi.single p (if 2 * p.1 + 1 ≤ c then 1 else -1 / 2) +
    Pi.single p.rev (if 2 * p.1 + 1 < c then 1 else if 2 * p.1 + 1 = c then 0 else 1 / 2)

/- English proof (translation)
Establish `hp` using `p.2`. Establish `hq` using `q.2`. Take `⟨P, hP⟩ : ∃ P, P = if neg then c / 2 else (c + 1) / 2` from `⟨_, rfl⟩`. Apply the tactic sequence `have hP1 : c / 2 ≤ P ∧ P ≤ (c + 1) / 2 := by rw [hP]; split_ifs <;> omega`. Establish `hm : 2 * p.1 + 1 = c → (P ≤ p.1 ↔ neg = true)`.

Apply the tactic sequence `intro h; rw [hP]; cases neg <;> simp <;> omega`. Rewrite using `[← hP]`. Simplify using `only [middleSymmetricBasisVector, map_add, LinearMap.add_apply, Examples₂.diagForm_single_left, Pi.single_apply, Pi.add_apply, GlobalTheory.UnitPerp.negFrom, Examples₂.sgn, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, decide_eq_true_eq]`. Generalize the expression as in `p.1 = a at *`. Generalize the expression as in `q.1 = b at *`.

Use `clear hP`. Establish `e1 : (c - (a + 1) = c - (b + 1)) = (a = b)` using `propext (by omega)`. Establish `e2 : (a = c - (b + 1)) = (a + b + 1 = c)` using `propext (by omega)`. Establish `e3 : (c - (a + 1) = b) = (a + b + 1 = c)` using `propext (by omega)`. Simplify using `only [e1, e2, e3]`.

Apply the tactic sequence `by_cases h1 : a = b <;> by_cases h2 : a + b + 1 = c`. Substitute `h1` using the available equality. Establish `h : 2 * a + 1 = c` using `by omega`. Simplify using `only [if_pos h.le, if_pos h, if_neg (show ¬ 2 * a + 1 < c by omega), hm h, if_pos h2]`. Apply the tactic sequence `cases neg <;> simp`.

Substitute `h1` using the available equality. Break down `(show 2 * a + 1 < c ∨ c < 2 * a + 1 by omega) with h | h` into its components or cases. Simplify using `only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega), if_neg h2]`. Simplify using the standard rewrite rules. Simplify using `only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega), if_neg (show ¬ P ≤ c - (a + 1) by omega), if_neg h2]`.

Evaluate the numerical expressions. Break down `(show (2 * a + 1 < c ∧ c < 2 * b + 1) ∨ (2 * b + 1 < c ∧ c < 2 * a + 1) by omega) with ⟨h, h'⟩ | ⟨h', h⟩` into its components or cases. Simplify using `only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega), if_neg h'.not_ge, if_neg h'.not_gt, if_neg h'.ne', if_neg h1, if_pos h2]`. Evaluate the numerical expressions. Simplify using `only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega), if_neg (show ¬ P ≤ c - (a + 1) by omega), if_pos h'.le, if_pos h', if_neg h1, if_pos h2]`.

Evaluate the numerical expressions. Simplify using `only [if_neg h1, if_neg h2, add_zero, mul_zero]`.
-/
theorem middleSymmetricBasisVectors_gram_antiDiagonal (c : ℕ) (neg : Bool) (p q : Fin c) :
    Examples₂.diagForm c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2)) (middleSymmetricBasisVector E c p) (middleSymmetricBasisVector E c q) =
      antiDiagonalSignGramMatrix c (if neg then -1 else 1) p q := by
  have hp := p.2
  have hq := q.2
  obtain ⟨P, hP⟩ : ∃ P, P = if neg then c / 2 else (c + 1) / 2 := ⟨_, rfl⟩
  have hP1 : c / 2 ≤ P ∧ P ≤ (c + 1) / 2 := by rw [hP]; split_ifs <;> omega
  have hm : 2 * p.1 + 1 = c → (P ≤ p.1 ↔ neg = true) := by
    intro h; rw [hP]; cases neg <;> simp <;> omega
  rw [← hP]
  simp only [middleSymmetricBasisVector, map_add, LinearMap.add_apply, Examples₂.diagForm_single_left, Pi.single_apply, Pi.add_apply,
    GlobalTheory.UnitPerp.negFrom, Examples₂.sgn, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, decide_eq_true_eq]
  generalize p.1 = a at *
  generalize q.1 = b at *
  clear hP
  have e1 : (c - (a + 1) = c - (b + 1)) = (a = b) := propext (by omega)
  have e2 : (a = c - (b + 1)) = (a + b + 1 = c) := propext (by omega)
  have e3 : (c - (a + 1) = b) = (a + b + 1 = c) := propext (by omega)
  simp only [e1, e2, e3]
  by_cases h1 : a = b <;> by_cases h2 : a + b + 1 = c
  · subst h1
    have h : 2 * a + 1 = c := by omega
    simp only [if_pos h.le, if_pos h, if_neg (show ¬ 2 * a + 1 < c by omega), hm h, if_pos h2]
    cases neg <;> simp
  · subst h1
    rcases (show 2 * a + 1 < c ∨ c < 2 * a + 1 by omega) with h | h
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega), if_neg h2]
      simp
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_neg h2]
      norm_num
  · rcases (show (2 * a + 1 < c ∧ c < 2 * b + 1) ∨ (2 * b + 1 < c ∧ c < 2 * a + 1) by omega) with ⟨h, h'⟩ | ⟨h', h⟩
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega),
        if_neg h'.not_ge, if_neg h'.not_gt, if_neg h'.ne', if_neg h1, if_pos h2]
      norm_num
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_pos h'.le, if_pos h', if_neg h1, if_pos h2]
      norm_num
  · simp only [if_neg h1, if_neg h2, add_zero, mul_zero]

end Generic

/- English proof (translation)
Apply the tactic sequence `have hc : c = (if neg then c / 2 else (c + 1) / 2) + (if neg then (c + 1) / 2 else c / 2) := by split_ifs <;> omega`. Establish `hW` using `GlobalTheory.UnitPerp.ofKind_stdSpace (E := D.host.E) hc`. Use `set W : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2)) (if neg then c / 2 else (c + 1) / 2) (if neg then (c + 1) / 2 else c / 2) with hWd`. Use `⟨GlobalTheory.Doubling.hsum A W, ⟨?_⟩, GlobalTheory.Doubling.sigOK_hsum hA hW.2.1, fun τ => ?_⟩` and prove the remaining obligations. Use `{ ι := LinearMap.inl _ _ _ isom := GlobalTheory.Doubling.isIsomEmb_inl A W a := fun k j => (GlobalTheory.Doubling.hsum A W).frame.repr ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V) k gram := Matrix.ext fun i j => ?_ perp := Matrix.ext fun i j => ?_ rank := rfl }` and prove the remaining obligations.

Use `Eq.trans (coords_gram (GlobalTheory.Doubling.hsum A W) ((0, middleSymmetricBasisVector D.host.E c i) : A.V × W.V) ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)) ?_` and prove the remaining obligations. Use `(GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_` and prove the remaining obligations. Rewrite using `[map_zero, zero_add]`. Conclude with `middleSymmetricBasisVectors_gram_antiDiagonal c neg i j`. Use `Eq.trans ?_ ((coords_gram (GlobalTheory.Doubling.hsum A W) ((A.frame i, 0) : A.V × W.V) ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)).trans ?_)` and prove the remaining obligations.

Establish `e : frameMat (GlobalTheory.Doubling.hsum A W) A (LinearMap.inl _ _ _) = fun k i => (GlobalTheory.Doubling.hsum A W).frame.repr ((A.frame i, 0) : A.V × W.V) k` using `Matrix.ext fun k i => LinearMap.toMatrix_apply A.frame (GlobalTheory.Doubling.hsum A W).frame _ k i`. Rewrite using `[e]`. Both sides reduce to the same expression. Use `(GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_` and prove the remaining obligations. Rewrite using `[map_zero, map_zero, zero_add]`.

Both sides reduce to the same expression. Use `show A.sig τ + W.sig τ = _`. Rewrite using `[hs τ]`. Both sides reduce to the same expression.
-/
theorem exists_hermitian_space_add_signature (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool) (hA : A.SigOK) (hs : ∀ τ, A.sig τ = (p, q)) :
    ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧
      ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  have hc : c = (if neg then c / 2 else (c + 1) / 2) + (if neg then (c + 1) / 2 else c / 2) := by
    split_ifs <;> omega
  have hW := GlobalTheory.UnitPerp.ofKind_stdSpace (E := D.host.E) hc
  set W : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2))
    (if neg then c / 2 else (c + 1) / 2) (if neg then (c + 1) / 2 else c / 2) with hWd
  refine ⟨GlobalTheory.Doubling.hsum A W, ⟨?_⟩, GlobalTheory.Doubling.sigOK_hsum hA hW.2.1, fun τ => ?_⟩
  · refine
      { ι := LinearMap.inl _ _ _
        isom := GlobalTheory.Doubling.isIsomEmb_inl A W
        a := fun k j => (GlobalTheory.Doubling.hsum A W).frame.repr ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V) k
        gram := Matrix.ext fun i j => ?_
        perp := Matrix.ext fun i j => ?_
        rank := rfl }
    · refine Eq.trans (coords_gram (GlobalTheory.Doubling.hsum A W) ((0, middleSymmetricBasisVector D.host.E c i) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)) ?_
      refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
      rw [map_zero, zero_add]
      exact middleSymmetricBasisVectors_gram_antiDiagonal c neg i j
    · refine Eq.trans ?_ ((coords_gram (GlobalTheory.Doubling.hsum A W) ((A.frame i, 0) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)).trans ?_)
      · have e : frameMat (GlobalTheory.Doubling.hsum A W) A (LinearMap.inl _ _ _) =
            fun k i => (GlobalTheory.Doubling.hsum A W).frame.repr ((A.frame i, 0) : A.V × W.V) k :=
          Matrix.ext fun k i => LinearMap.toMatrix_apply A.frame (GlobalTheory.Doubling.hsum A W).frame _ k i
        rw [e]
        rfl
      · refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
        rw [map_zero, map_zero, zero_add]
        rfl
  · show A.sig τ + W.sig τ = _
    rw [hs τ]
    rfl

end GlobalTheory.SignatureAddition

end
