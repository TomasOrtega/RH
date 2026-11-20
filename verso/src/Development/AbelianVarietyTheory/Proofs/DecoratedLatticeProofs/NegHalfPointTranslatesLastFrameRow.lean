import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualPickDot
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TraceInverseGramConjSmulEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

/- English proof (translation)
Introduce `D k _ _ _ _ p n n'' _ _ _ _ S₀ A L W₀ o ζ β γ γ₀ hsum t`. Establish `hes : ∀ a, p.e * p.sec a = p.sec a` using `fun a => by rw [← p.sec_pr, p.pr_sec]`. Rewrite using `[OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.neg_apply, wRow, Matrix.of_apply, mul_left_comm, mul_neg, hes, mul_neg]`. Use `set c : Fin S₀.rank → k := fun i => p.pr (ratV (vecB o ζ) i) with hc`. Establish `hmap : Matrix.map (o.jB * -wRow p ζ β t : Mx D S₀.rank W₀.rank) p.pr = -vecMulVec c (t ᵥ* β.b')`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.map_apply, Matrix.mul_apply, map_sum, Matrix.neg_apply, vecMulVec_apply, hc]`. Simplify using `only [ratV, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.neg_apply, wRow, Matrix.of_apply, map_neg, p.pr_sec, mul_neg, mul_assoc]`. Both sides reduce to the same expression.

Establish `hcol : (γ₀.b' *ᵥ c) i = Sum.elim (fun _ => 0) (fun _ => 1) i`. Establish `h` using `congrFun (congrFun γ₀.b'b i) (Sum.inr 0)`. Rewrite `h` using `[hsum, Matrix.mul_apply]`. Simplify using `only [fromCols_apply_inr, replicateCol_apply] at h`. Use `h.trans ?_` and prove the remaining obligations.

Break down `i with i | i` into its components or cases. Simplify using the standard rewrite rules. Take `rfl` from `Subsingleton.elim i 0`. Simplify using the standard rewrite rules. Rewrite using `[rd, hmap, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, β.b'b, Matrix.vecMul_one, Matrix.neg_apply, vecMulVec_apply, hcol]`.

Apply the tactic sequence `rcases i with i | i <;> simp`.
-/
theorem neg_wRow_half_rd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf p.e ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) ∧ ∀ i j, rd β γ₀ ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) i j = Sum.elim (fun _ => 0) (fun _ => -t j) i := by
  intro D k _ _ _ _ p n n'' _ _ _ _ S₀ A L W₀ o ζ β γ γ₀ hsum t
  have hes : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.neg_apply, wRow, Matrix.of_apply, mul_left_comm, mul_neg, hes, mul_neg]
  · set c : Fin S₀.rank → k := fun i => p.pr (ratV (vecB o ζ) i) with hc
    have hmap : Matrix.map (o.jB * -wRow p ζ β t : Mx D S₀.rank W₀.rank) p.pr = -vecMulVec c (t ᵥ* β.b') := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.map_apply, Matrix.mul_apply, map_sum, Matrix.neg_apply, vecMulVec_apply, hc]
      simp only [ratV, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.neg_apply, wRow, Matrix.of_apply, map_neg, p.pr_sec, mul_neg, mul_assoc]
      rfl
    have hcol : (γ₀.b' *ᵥ c) i = Sum.elim (fun _ => 0) (fun _ => 1) i := by
      have h := congrFun (congrFun γ₀.b'b i) (Sum.inr 0)
      rw [hsum, Matrix.mul_apply] at h
      simp only [fromCols_apply_inr, replicateCol_apply] at h
      refine h.trans ?_
      rcases i with i | i
      · simp
      · obtain rfl := Subsingleton.elim i 0
        simp
    rw [rd, hmap, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, β.b'b,
      Matrix.vecMul_one, Matrix.neg_apply, vecMulVec_apply, hcol]
    rcases i with i | i <;> simp

end GlobalTheory.FinPl.LineAct

end
