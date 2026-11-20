import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RootCoordinateFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianBlockSpans
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames

/- English proof (translation)
Unfold `nxt fam`. Use `split_ifs with h`. Establish `hs : a.succ = Fin.castSucc ⟨a.1 + 1, h⟩` using `Fin.ext (by simp)`. Rewrite using `[hs, Fin.snoc_castSucc]`. Establish `hs : a.succ = Fin.last r` using `Fin.ext (by simp; omega)`.

Rewrite using `[hs, Fin.snoc_last]`.
-/
theorem nxt_eq {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) : nxt e z a = fam e z a.succ := by
  unfold nxt fam
  split_ifs with h
  · have hs : a.succ = Fin.castSucc ⟨a.1 + 1, h⟩ := Fin.ext (by simp)
    rw [hs, Fin.snoc_castSucc]
  · have hs : a.succ = Fin.last r := Fin.ext (by simp; omega)
    rw [hs, Fin.snoc_last]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[star_sum, sum_dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem hJ_sum_left {n m : ℕ} (ε : Fin n → Bool) (c : Fin m → ℂ) (v : Fin m → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε (∑ i, c i • v i) w = ∑ i, star (c i) * hJ ε (v i) w := by
  unfold hJ
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[Matrix.mulVec_sum, dotProduct_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
private theorem hJ_fintype_sum_smul_right {n : ℕ} {ι : Type} [Fintype ι] (ε : Fin n → Bool) (x : Fin n → ℂ)
    (Q : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, Q c • y c) = ∑ c, Q c * hJ ε x (y c) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Introduce `n r ε e f z hfe hfz g P hP a`. Unfold `rootCoord`. Rewrite using `[nxt_eq, hP, hJ_fintype_sum_smul_right]`. Rewrite using `[Finset.sum_eq_single a.castSucc]`. Rewrite using `[show fam e z a.castSucc = e a from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe, if_pos rfl, mul_one]`.

Introduce `c _ hc`. Use `Fin.lastCases ?_ (fun b hb => ?_) c hc` and prove the remaining obligations. Introduce `_`. Rewrite using `[show fam e z (Fin.last r) = z from by unfold fam; exact Fin.snoc_last _ _, hfz, mul_zero]`. Rewrite using `[show fam e z b.castSucc = e b from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe]`.

Establish `hab : a ≠ b` using `fun h => hb (by rw [h])`. Rewrite using `[if_neg hab, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem RootCoordFrame_holds : RootCoordFrame := by
  intro n r ε e f z hfe hfz g P hP a
  unfold rootCoord
  rw [nxt_eq, hP, hJ_fintype_sum_smul_right]
  rw [Finset.sum_eq_single a.castSucc]
  · rw [show fam e z a.castSucc = e a from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe, if_pos rfl, mul_one]
  · intro c _ hc
    refine Fin.lastCases ?_ (fun b hb => ?_) c hc
    · intro _
      rw [show fam e z (Fin.last r) = z from by unfold fam; exact Fin.snoc_last _ _, hfz, mul_zero]
    · rw [show fam e z b.castSucc = e b from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe]
      have hab : a ≠ b := fun h => hb (by rw [h])
      rw [if_neg hab, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `n r ε f f' s si s' g P P' hsi hinv hP hP'`. Establish `hs : s * si = 1` using `mul_eq_one_comm.mp hsi`. Use extensionality with `a b`. Establish `h1 : (si * g * s') *ᵥ f' b = si *ᵥ (g *ᵥ (s' *ᵥ f' b))`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.

Establish `h2 : hJ ε (f a) (si *ᵥ (g *ᵥ (s' *ᵥ f' b))) = hJ ε (s *ᵥ f a) (g *ᵥ (s' *ᵥ f' b))`. Rewrite using `[← hinv (f a) (si *ᵥ _), Matrix.mulVec_mulVec, hs, Matrix.one_mulVec]`. Use `show hJ ε (f a) ((si * g * s') *ᵥ f' b) = _`. Rewrite using `[h1, h2, hP a, hP' b, hJ_sum_left, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul, hJ_fintype_sum_smul_right, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Zhat, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ZhatNAct_holds : ZhatNAct := by
  intro n r ε f f' s si s' g P P' hsi hinv hP hP'
  have hs : s * si = 1 := mul_eq_one_comm.mp hsi
  ext a b
  have h1 : (si * g * s') *ᵥ f' b = si *ᵥ (g *ᵥ (s' *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 : hJ ε (f a) (si *ᵥ (g *ᵥ (s' *ᵥ f' b))) = hJ ε (s *ᵥ f a) (g *ᵥ (s' *ᵥ f' b)) := by
    rw [← hinv (f a) (si *ᵥ _), Matrix.mulVec_mulVec, hs, Matrix.one_mulVec]
  show hJ ε (f a) ((si * g * s') *ᵥ f' b) = _
  rw [h1, h2, hP a, hP' b, hJ_sum_left, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hJ_fintype_sum_smul_right, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Zhat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X u v`. Establish `hc : ∀ p q : (VS D).V, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) = embS D (X.pl v) ((VS D).hT p q)` using `fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd (X := X) v p q`. Establish `hs : ∀ p q : (VS D).V, (VS D).hT q p = starRingEnd D.host.E ((VS D).hT p q)`. Introduce `p q`. Use `first`.

Consider the case `exact ((VS D).herm.eq p q).symm`. Consider the case `exact ((VS D).herm p q).symm`. Simplify using `only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hc]`. Use `⟨fun a b => by rw [X.ee a b, map_zero], fun a b => by rw [X.ff a b, map_zero], fun a b => ?_, fun a b => ?_, fun a => ⟨by rw [(X.zu_orth u a).1, map_zero], by rw [(X.zu_orth u a).2, map_zero]⟩, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [X.ef a b] split_ifs <;> simp`.

Rewrite using `[hs, X.ef b a]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h, map_zero, map_zero]`.

Rewrite using `[X.zu_norm u, map_neg, map_natCast]`. Simplify using `[Tw]`. Unfold `Tw`. Conclude with `(D.mem u).A.T_prime.ne_zero` after adjusting the coercions.
-/
theorem FrameAtV_holds : FrameAtV := by
  intro D X u v
  have hc : ∀ p q : (VS D).V, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) =
      embS D (X.pl v) ((VS D).hT p q) := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd (X := X) v p q
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = starRingEnd D.host.E ((VS D).hT p q) := by
    intro p q
    first
    | exact ((VS D).herm.eq p q).symm
    | exact ((VS D).herm p q).symm
  simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hc]
  refine ⟨fun a b => by rw [X.ee a b, map_zero], fun a b => by rw [X.ff a b, map_zero],
    fun a b => ?_, fun a b => ?_,
    fun a => ⟨by rw [(X.zu_orth u a).1, map_zero], by rw [(X.zu_orth u a).2, map_zero]⟩, ?_, ?_⟩
  · rw [X.ef a b]
    split_ifs <;> simp
  · rw [hs, X.ef b a]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero, map_zero]
  · rw [X.zu_norm u, map_neg, map_natCast]
    simp [Tw]
  · unfold Tw
    exact_mod_cast (D.mem u).A.T_prime.ne_zero

end Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames
