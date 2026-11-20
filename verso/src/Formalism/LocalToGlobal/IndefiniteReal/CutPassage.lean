import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.NonGenericAndKTwoTheorems
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.LocalToGlobal.GlobalTheory.DivPassageP

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

/- English proof (translation)
Establish `hex : ∃ R : Matrix (Fin n) (Fin d) K, P * R = 1` using `by choose f hf using h`. Use `⟨Matrix.of fun i k => f (Pi.single k 1) i, ?_⟩` and prove the remaining obligations. Use extensionality with `i k`. Establish `h1` using `congrFun (hf (Pi.single k 1)) i`. Rewrite `h1` using `[Pi.single_apply]`.

Rewrite using `[Matrix.one_apply, ← h1]`. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]`. Unfold `rinv`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`.
-/
theorem rinv_spec {d n : ℕ} (P : Matrix (Fin d) (Fin n) K) (h : Function.Surjective P.mulVec) :
    P * rinv P = 1 := by
  have hex : ∃ R : Matrix (Fin n) (Fin d) K, P * R = 1 := by
    choose f hf using h
    refine ⟨Matrix.of fun i k => f (Pi.single k 1) i, ?_⟩
    ext i k
    have h1 := congrFun (hf (Pi.single k 1)) i
    rw [Pi.single_apply] at h1
    rw [Matrix.one_apply, ← h1]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  unfold rinv
  rw [dif_pos hex]
  exact hex.choose_spec

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)

/- English proof (translation)
Introduce `ζ sEE hW h2 hBt hMI hZ`. Use `⟨?_, fun u => by simp [colDef, colOf, hZ.1 u], fun u t => inv_ne_zero (hZ.2.1 u t), fun u w => ?_⟩` and prove the remaining obligations. Use `swap`. Use `show vw w (ζ u (X.μ w))⁻¹ = 0`. Rewrite using `[ValuationRepresentative.vw_inv, hZ.2.2 u w, neg_zero]`.

Introduce `u t φ F`. Distinguish the cases in `ht : t = Bs.μ0`. Substitute `ht show (fc X.zs).Dc.Pt u Bs.μ0 φ F = (ζ u Bs.μ0)⁻¹ * X.Bdef u φ ((X.rowMat cr true Bs.μ0).mulVec (((lv (fc X.zs) true).Pq Bs.μ0).mulVec F))` using the available equality. Rewrite using `[rowMat_base X cr true h2, Matrix.one_mulVec, hZ.1 u, inv_one, one_mul]`. Use `show (fc X.zs).Dc.Pt u Bs.μ0 φ F = (fc X.zs).Dc.Pt u Bs.μ0 φ ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F))`.

Establish `hR` using `rinv_spec _ (hW.Pq_surj Bs.μ0)`. Establish `hk : F - (rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F) ∈ (fc X.zs).Df1.U Bs.μ0`. Rewrite using `[DefSide.U, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec, sub_self]`. Establish `h0` using `hBt u φ _ hk`. Rewrite `h0` using `[map_sub, sub_eq_zero]`.

Conclude with `h0`. Use `show (fc X.zs).Dc.Pt u t φ F = (ζ u t)⁻¹ * X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))`. Rewrite using `[← hMI u t ht φ F, ← mul_assoc, inv_mul_cancel₀ (hZ.2.1 u t), one_mul]`.
-/
theorem cutPairing : X.CutPairing cr := by
  intro ζ sEE hW h2 hBt hMI hZ
  refine ⟨?_, fun u => by simp [colDef, colOf, hZ.1 u], fun u t => inv_ne_zero (hZ.2.1 u t),
    fun u w => ?_⟩
  swap
  · show vw w (ζ u (X.μ w))⁻¹ = 0
    rw [ValuationRepresentative.vw_inv, hZ.2.2 u w, neg_zero]
  intro u t φ F
  by_cases ht : t = Bs.μ0
  · subst ht
    show (fc X.zs).Dc.Pt u Bs.μ0 φ F =
      (ζ u Bs.μ0)⁻¹ * X.Bdef u φ ((X.rowMat cr true Bs.μ0).mulVec (((lv (fc X.zs) true).Pq Bs.μ0).mulVec F))
    rw [rowMat_base X cr true h2, Matrix.one_mulVec, hZ.1 u, inv_one, one_mul]
    show (fc X.zs).Dc.Pt u Bs.μ0 φ F = (fc X.zs).Dc.Pt u Bs.μ0 φ
      ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F))
    have hR := rinv_spec _ (hW.Pq_surj Bs.μ0)
    have hk : F - (rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F) ∈
        (fc X.zs).Df1.U Bs.μ0 := by
      rw [DefSide.U, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hR,
        Matrix.one_mulVec, sub_self]
    have h0 := hBt u φ _ hk
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · show (fc X.zs).Dc.Pt u t φ F = (ζ u t)⁻¹ * X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))
    rw [← hMI u t ht φ F, ← mul_assoc, inv_mul_cancel₀ (hZ.2.1 u t), one_mul]

/- English proof (translation)
Introduce `hH0 hW1`. Apply `Formalism.IndefR.NonGenericAndKTwoTheorems.hecke_tuple_condition K Bs _ (X.data cr false) _` to reduce the goal to its premises. Introduce and unpack `w ⟨j, hj⟩ show X.μ w ≠ Bs.μ0`. Rewrite using `[← hH0.2 w]`. Apply `hW1` to reduce the goal to its premises.

Break down `hj with h | h` into its components or cases. Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises. Simplify using `only [CxData.W1, not_exists, not_or, not_not] at hc`. Take `⟨h1, h2, h3, -, -, -⟩` from `hc j`.

Simplify using `[Formalism.IndefR.HeckeTupleConditions.Atup, h1, h2, h3]`. Conclude with `⟨j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩`. Conclude with `hH0.2`.
-/
theorem cutTuples2 (C CH : ℝ) : X.CutTuples2 cr C CH := by
  intro hH0 hW1
  apply Formalism.IndefR.NonGenericAndKTwoTheorems.hecke_tuple_condition K Bs _ (X.data cr false) _
  · rintro w ⟨j, hj⟩
    show X.μ w ≠ Bs.μ0
    rw [← hH0.2 w]
    apply hW1
    rcases hj with h | h
    · by_contra hc
      apply h
      simp only [CxData.W1, not_exists, not_or, not_not] at hc
      obtain ⟨h1, h2, h3, -, -, -⟩ := hc j
      simp [Formalism.IndefR.HeckeTupleConditions.Atup, h1, h2, h3]
    · exact ⟨j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact hH0.2

end CxData

end Formalism.IndefR.Cx
