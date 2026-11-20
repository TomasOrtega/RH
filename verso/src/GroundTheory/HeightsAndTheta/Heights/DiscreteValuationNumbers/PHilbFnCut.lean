import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `F _ K _ _ ι _ I x e hI hx hnzd m`. Distinguish the cases in `hm : ∀ k, 0 ≤ m k`. Use `set n : K → ℕ := fun k => (m k).toNat with hn`. Establish `hA` using `h1 F K ι (I ⊔ Ideal.span {x}) n`. Establish `hB` using `h1 F K ι I n`.

Establish `hC` using `h2 F K ι I x e n hI hx hnzd`. Establish `hL : hilbFn (I ⊔ Ideal.span {x}) m = (Module.finrank F (gradedPiece (I ⊔ Ideal.span {x}) n) : ℤ)`. Unfold `hilbFn`. Rewrite using `[if_pos hm]`. Establish `hM : hilbFn I m = (Module.finrank F (gradedPiece I n) : ℤ)`.

Unfold `hilbFn`. Rewrite using `[if_pos hm]`. Rewrite using `[hL, hM, hA, hB]`. Distinguish the cases in `he : e ≤ n`. Establish `hme : ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k`.

Introduce `k`. Establish `h1k` using `he k`. Establish `h0` using `hm k`. Simplify using `only [Pi.sub_apply, hn] at h1k ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `hq : (fun k => ((m - fun k => (e k : ℤ)) k).toNat) = n - e`. Use function extensionality and compare the values at `k`. Establish `h1k` using `he k`. Establish `h0` using `hm k`. Simplify using `only [Pi.sub_apply, hn] at h1k ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hN : hilbFn I (m - fun k => (e k : ℤ)) = (Module.finrank F (gradedPiece I (n - e)) : ℤ)`. Unfold `hilbFn`. Rewrite using `[if_pos hme, hq]`. Rewrite using `[hN, h1 F K ι I (n - e)]`.

Rewrite `hC` using `[if_pos he]`. Rewrite using `[hC]`. Expand and normalize the polynomial expressions, which then agree. Establish `hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k`. Introduce `hall`.

Apply `he` to reduce the goal to its premises. Introduce `k`. Establish `h1k` using `hall k`. Establish `h0` using `hm k`. Simplify using `only [Pi.sub_apply, hn] at h1k ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hN : hilbFn I (m - fun k => (e k : ℤ)) = 0`. Unfold `hilbFn`. Rewrite using `[if_neg hme]`. Rewrite using `[hN]`.

Rewrite `hC` using `[if_neg he]`. Rewrite using `[hC]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, hk⟩` from `not_forall.mp hm`. Establish `hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k`.

Introduce `hall`. Use `hall k` as an intermediate fact. Simplify using `only [Pi.sub_apply] at this`. Use linear arithmetic over natural numbers and integers. Unfold `hilbFn`.

Rewrite using `[if_neg hm, if_neg hm, if_neg hme, sub_zero]`.
-/
theorem HilbFnCut.proof (h1 : GradedPieceQuot.Statement.{u}) (h2 : CutPieces.Statement.{u}) :
    HilbFnCut.Statement.{u} := by
  intro F _ K _ _ ι _ I x e hI hx hnzd m
  by_cases hm : ∀ k, 0 ≤ m k
  · set n : K → ℕ := fun k => (m k).toNat with hn
    have hA := h1 F K ι (I ⊔ Ideal.span {x}) n
    have hB := h1 F K ι I n
    have hC := h2 F K ι I x e n hI hx hnzd
    have hL : hilbFn (I ⊔ Ideal.span {x}) m =
        (Module.finrank F (gradedPiece (I ⊔ Ideal.span {x}) n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    have hM : hilbFn I m = (Module.finrank F (gradedPiece I n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    rw [hL, hM, hA, hB]
    by_cases he : e ≤ n
    · have hme : ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hq : (fun k => ((m - fun k => (e k : ℤ)) k).toNat) = n - e := by
        funext k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) =
          (Module.finrank F (gradedPiece I (n - e)) : ℤ) := by
        unfold hilbFn; rw [if_pos hme, hq]
      rw [hN, h1 F K ι I (n - e)]
      rw [if_pos he] at hC
      rw [hC]
      ring
    · have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro hall
        apply he
        intro k
        have h1k := hall k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) = 0 := by
        unfold hilbFn; rw [if_neg hme]
      rw [hN]
      rw [if_neg he] at hC
      rw [hC]
      ring
  · obtain ⟨k, hk⟩ := not_forall.mp hm
    have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
      intro hall
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    unfold hilbFn
    rw [if_neg hm, if_neg hm, if_neg hme, sub_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
