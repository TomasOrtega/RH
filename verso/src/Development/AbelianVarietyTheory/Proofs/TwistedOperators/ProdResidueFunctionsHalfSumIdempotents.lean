import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.StepVec

/- English proof (translation)
Establish `hm : ((c • t : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D c • (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)`. Use extensionality with `k l`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]`. Simplify using `only [frMapO]`. Rewrite using `[hm, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem frMapO_smul (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (c : AE D) (t : WO S T) :
    frMapO S T βS βT (c • t) = toEAf D c • frMapO S T βS βT t := by
  have hm : ((c • t : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) =
      toEAf D c • (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) := by
    ext k l
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  simp only [frMapO]
  rw [hm, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Introduce `D S T βS βT s es hid ω t hhalf`. Establish `hint : ∀ PP ∈ s, ∃ h : toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP), h⟩ = 1` using `fun PP hPP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hid PP hPP)`. Establish `hhalfPP : ∀ PP ∈ s, IsHalf (es PP) (es PP • t)`. Introduce `PP hPP i j`. Establish `he : es PP * es PP = es PP` using `(hid PP hPP).1.1`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]`. Simplify using `only [locFn]`. Use `split_ifs with hN`. Use `Finset.prod_congr rfl fun PP hPP => ?_` and prove the remaining obligations. Take `⟨hi, h1⟩` from `hint PP hPP`.

Establish `hN' : IsIntM (frMapO S T βS βT (es PP • t))`. Introduce `i j`. Rewrite using `[frMapO_smul, Matrix.smul_apply, smul_eq_mul]`. Conclude with `(Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem hi (hN i j)`. Rewrite using `[if_pos ⟨hhalfPP PP hPP, hN'⟩]`.

Use `congr 1`. Use function extensionality and compare the values at `i j`. Establish `hmem : (frMapO S T βS βT (es PP • t)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `hN' i j`. Simplify using `only [redM, dif_pos (hN i j), dif_pos hmem]`. Establish `heq : (⟨(frMapO S T βS βT (es PP • t)) i j, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D (es PP), hi⟩ * ⟨(frMapO S T βS βT t) i j, hN i j⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subring.coe_mul, frMapO_smul, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[heq, map_mul, h1, one_mul]`. Establish `hex : ∃ PP ∈ s, ¬ IsIntM (frMapO S T βS βT (es PP • t))`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `hN` to reduce the goal to its premises. Introduce `i j`. Establish `ht : t = (∑ PP ∈ s, es PP) • t`. Use extensionality with `k l`.

Conclude with `(hhalf k l).symm`. Establish `hsum : frMapO S T βS βT t i j = ∑ PP ∈ s, frMapO S T βS βT (es PP • t) i j` using `by conv_lhs => rw [ht, frMapO_smul]`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_sum (toEAf D), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun PP _ => ?_` and prove the remaining obligations. Rewrite using `[frMapO_smul, Matrix.smul_apply, smul_eq_mul]`.

Rewrite using `[hsum]`. Conclude with `Subring.sum_mem _ fun PP hPP => hc PP hPP i j`. Take `⟨PP, hPP, hni⟩` from `hex`. Use `symm`. Conclude with `Finset.prod_eq_zero hPP (if_neg fun h => hni h.2)`.
-/
theorem prod_locFn_half : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (s : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D),
    (∀ PP ∈ s, Formalism.L2.NTheta.IsIdemAt (es PP) PP) →
    ∀ (ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) (t : WO S T),
      IsHalf (∑ PP ∈ s, es PP) t →
      (open Classical in (if IsIntM (frMapO S T βS βT t) then ∏ PP ∈ s, ω PP (redM PP (frMapO S T βS βT t)) else 0)) =
        ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t) := by
  intro D S T βS βT s es hid ω t hhalf
  classical
  have hint : ∀ PP ∈ s, ∃ h : toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP), h⟩ = 1 :=
    fun PP hPP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hid PP hPP)
  have hhalfPP : ∀ PP ∈ s, IsHalf (es PP) (es PP • t) := by
    intro PP hPP i j
    have he : es PP * es PP = es PP := (hid PP hPP).1.1
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
  simp only [locFn]
  split_ifs with hN
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    obtain ⟨hi, h1⟩ := hint PP hPP
    have hN' : IsIntM (frMapO S T βS βT (es PP • t)) := by
      intro i j
      rw [frMapO_smul, Matrix.smul_apply, smul_eq_mul]
      exact (Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem hi (hN i j)
    rw [if_pos ⟨hhalfPP PP hPP, hN'⟩]
    congr 1
    funext i j
    have hmem : (frMapO S T βS βT (es PP • t)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := hN' i j
    simp only [redM, dif_pos (hN i j), dif_pos hmem]
    have heq : (⟨(frMapO S T βS βT (es PP • t)) i j, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        ⟨toEAf D (es PP), hi⟩ * ⟨(frMapO S T βS βT t) i j, hN i j⟩ := by
      apply Subtype.ext
      simp only [Subring.coe_mul, frMapO_smul, Matrix.smul_apply, smul_eq_mul]
    rw [heq, map_mul, h1, one_mul]
  · have hex : ∃ PP ∈ s, ¬ IsIntM (frMapO S T βS βT (es PP • t)) := by
      by_contra hc
      push_neg at hc
      apply hN
      intro i j
      have ht : t = (∑ PP ∈ s, es PP) • t := by
        ext k l
        exact (hhalf k l).symm
      have hsum : frMapO S T βS βT t i j = ∑ PP ∈ s, frMapO S T βS βT (es PP • t) i j := by
        conv_lhs => rw [ht, frMapO_smul]
        rw [Matrix.smul_apply, smul_eq_mul, map_sum (toEAf D), Finset.sum_mul]
        refine Finset.sum_congr rfl fun PP _ => ?_
        rw [frMapO_smul, Matrix.smul_apply, smul_eq_mul]
      rw [hsum]
      exact Subring.sum_mem _ fun PP hPP => hc PP hPP i j
    obtain ⟨PP, hPP, hni⟩ := hex
    symm
    exact Finset.prod_eq_zero hPP (if_neg fun h => hni h.2)

end GlobalTheory.StepVec
