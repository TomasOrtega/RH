import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderPicOfIsReducedFiniteIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTensorLineBundleGlobalSectionsEquivStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowNowhereZero

/- English proof (translation)
The claim follows from `GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv T A B hA hB`.
-/
theorem tensSec (T : Scheme.{0}) [IsAffine T] (A B : LB T) (hA : A.IsLB) (hB : B.IsLB) :
    Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (CechPic.tens A B)) :=
  GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv T A B hA hB

variable {T : Scheme.{0}}

def tp (L : LB T) (k : ℕ) : LB T :=
  Nat.rec (LB.triv T) (fun _ M => CechPic.tens L M) k

/- English proof (translation)
The claim follows from `| 0 => LB.isLB_triv T | k + 1 => CechPic.isLB_tens hL (isLB_tp hL k)`.
-/
theorem isLB_tp {L : LB T} (hL : L.IsLB) : ∀ k, (tp L k).IsLB
  | 0 => LB.isLB_triv T
  | k + 1 => CechPic.isLB_tens hL (isLB_tp hL k)

/- English proof (translation)
The claim follows from `| 0 => by simp only [zero_smul]; rfl | k + 1 => by rw [succ_nsmul'] change CechPic.cls (CechPic.tens L (tp L k)) (CechPic.isLB_tens hL (isLB_tp hL k)) = _ rw [CechPic.cls_tens hL (isLB_tp hL k), cls_tp hL k]`.
-/
theorem cls_tp {L : LB T} (hL : L.IsLB) : ∀ k, CechPic.cls (tp L k) (isLB_tp hL k) = k • CechPic.cls L hL
  | 0 => by simp only [zero_smul]; rfl
  | k + 1 => by
    rw [succ_nsmul']
    change CechPic.cls (CechPic.tens L (tp L k)) (CechPic.isLB_tens hL (isLB_tp hL k)) = _
    rw [CechPic.cls_tens hL (isLB_tp hL k), cls_tp hL k]

/- English proof (translation)
The claim follows from `| 0 => by have := LB.invertible_sec_top (isLB_tp hL 0) rw [pow_zero, CommRing.Pic.mk_eq_one_iff_free, ← LB.exists_isGen_iff_free_top (isLB_tp hL 0), ← CechPic.cls_eq_zero_iff (isLB_tp hL 0)] rfl | k + 1 => by have := LB.invertible_sec_top hL have := LB.invertible_sec_top (isLB_tp …`.
-/
theorem mk_tp [IsAffine T] {L : LB T} (hL : L.IsLB) : ∀ k,
    @CommRing.Pic.mk Γ(T, ⊤) (LB.Sec (tp L k)) _ _ _ (LB.invertible_sec_top (isLB_tp hL k)) =
      (@CommRing.Pic.mk Γ(T, ⊤) (LB.Sec L) _ _ _ (LB.invertible_sec_top hL)) ^ k
  | 0 => by
    have := LB.invertible_sec_top (isLB_tp hL 0)
    rw [pow_zero, CommRing.Pic.mk_eq_one_iff_free, ← LB.exists_isGen_iff_free_top (isLB_tp hL 0),
      ← CechPic.cls_eq_zero_iff (isLB_tp hL 0)]
    rfl
  | k + 1 => by
    have := LB.invertible_sec_top hL
    have := LB.invertible_sec_top (isLB_tp hL k)
    have : Module.Invertible Γ(T, ⊤) (LB.Sec (CechPic.tens L (tp L k))) :=
      LB.invertible_sec_top (CechPic.isLB_tens hL (isLB_tp hL k))
    obtain ⟨e⟩ := tensSec T L (tp L k) hL (isLB_tp hL k)
    rw [pow_succ', ← mk_tp hL k, ← CommRing.Pic.mk_tensor]
    exact (CommRing.Pic.mk_eq_mk_iff.2 ⟨e⟩).symm

/- English proof (translation)
Introduce `T _ _ hfin L hL`. Use `LB.invertible_sec_top hL` as an intermediate fact. Take `⟨n, hn, hpow⟩` from `(GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int Γ(T, ⊤) (CommRing.Pic.mk Γ(T, ⊤) (LB.Sec L))).exists_pow_eq_one`. Establish `hk` using `isLB_tp hL n`. Use `LB.invertible_sec_top hk` as an intermediate fact.

Establish `h1 : CechPic.cls (tp L n) hk = 0`. Rewrite using `[CechPic.cls_eq_zero_iff hk, LB.exists_isGen_iff_free_top hk, ← CommRing.Pic.mk_eq_one_iff_free, mk_tp hL n, hpow]`. Establish `hP : (lbPow L n).IsLB` using `LB.isLB_linComb hL _ _`. Establish `h2 : CechPic.cls (lbPow L n) hP = 0` using `by rw [CechPic.cls_lbPow hL n hP, ← cls_tp hL n, h1]`. Take `⟨t, ht⟩` from `(CechPic.cls_eq_zero_iff hP).1 h2`.

Use `⟨n, DVR.genSec t ht, hn, top_unique fun x _ => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (hP.cover.ge (Opens.mem_top x))`. Use `Opens.mem_iSup.2 ⟨i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ T.basicOpen ((t.s i : Γ(T, (lbPow L n).U i)))`. Rewrite using `[Scheme.basicOpen_of_isUnit _ (t.s i).isUnit]`.

Conclude with `hi`.
-/
theorem main : ∀ (T : Scheme.{0}) [IsAffine T] [AlgebraicGeometry.IsReduced T], Module.Finite ℤ Γ(T, ⊤) →
    ∀ L : LB T, L.IsLB → ∃ (n : ℕ) (s : (lbPow L n).Sec), 1 ≤ n ∧ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ := by
  intro T _ _ hfin L hL
  have := LB.invertible_sec_top hL
  obtain ⟨n, hn, hpow⟩ := (GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int Γ(T, ⊤) (CommRing.Pic.mk Γ(T, ⊤) (LB.Sec L))).exists_pow_eq_one
  have hk := isLB_tp hL n
  have := LB.invertible_sec_top hk
  have h1 : CechPic.cls (tp L n) hk = 0 := by
    rw [CechPic.cls_eq_zero_iff hk, LB.exists_isGen_iff_free_top hk, ← CommRing.Pic.mk_eq_one_iff_free, mk_tp hL n,
      hpow]
  have hP : (lbPow L n).IsLB := LB.isLB_linComb hL _ _
  have h2 : CechPic.cls (lbPow L n) hP = 0 := by rw [CechPic.cls_lbPow hL n hP, ← cls_tp hL n, h1]
  obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff hP).1 h2
  refine ⟨n, DVR.genSec t ht, hn, top_unique fun x _ => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hP.cover.ge (Opens.mem_top x))
  refine Opens.mem_iSup.2 ⟨i, ?_⟩
  change x ∈ T.basicOpen ((t.s i : Γ(T, (lbPow L n).U i)))
  rw [Scheme.basicOpen_of_isUnit _ (t.s i).isUnit]
  exact hi

end GlobalTheory.PowNowhereZero
