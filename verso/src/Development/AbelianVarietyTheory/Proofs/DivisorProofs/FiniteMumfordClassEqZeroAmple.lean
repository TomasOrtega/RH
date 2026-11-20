import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleRankComparison
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Use `set P := ptOver K (AlgebraicClosure K)`. Establish `h1` using `congrArg (CechPic.pull (lift (snd P A.X) (fst P A.X)).left) h`. Rewrite `h1` using `[lam_eq, pull_lam, map_zero, lift_fst, lift_snd_assoc, lam_comm, ← lam_eq]`. Establish `h0 : CechPic.pull (fst P A.X ≫ x).left (cls L hL) = 0`. Rewrite using `[Over.comp_left, pull_comp, GlobalTheory.PrimitiveOverField.pic_field (K := AlgebraicClosure K) (CechPic.pull x.left (cls L hL)), map_zero]`.

Rewrite `h1` using `[AbVar.lam, h0, sub_zero]`. Introduce `p`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Establish `hD : (Out.translDiff A.X L x).IsLB` using `LB.isLB_linComb hL _ _`. Use `(cls_eq_zero_iff (pull_isLB hD _)).1 ?_` and prove the remaining obligations.

Rewrite using `[cls_pull hD]`. Use `(congrArg _ ?_).trans (map_zero _)` and prove the remaining obligations. Use `(cls_linComb hL _ _ hD).trans (Eq.trans ?_ h1)` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two, sub_eq_add_neg]`. Conclude with `congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)`.
-/
theorem memKL_of_lam_geom_eq_zero {K : Type} [Field K] (A : AbVar K) {L : LB A.X.left} (hL : L.IsLB)
    (x : A.Pt) (h : AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0) :
    MemKL A.X L x := by
  set P := ptOver K (AlgebraicClosure K)
  have h1 := congrArg (CechPic.pull (lift (snd P A.X) (fst P A.X)).left) h
  rw [lam_eq, pull_lam, map_zero, lift_fst, lift_snd_assoc, lam_comm, ← lam_eq] at h1
  have h0 : CechPic.pull (fst P A.X ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, pull_comp, GlobalTheory.PrimitiveOverField.pic_field (K := AlgebraicClosure K) (CechPic.pull x.left (cls L hL)), map_zero]
  rw [AbVar.lam, h0, sub_zero] at h1
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A.X L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ h1)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

end GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A c ⟨L, hL, ha, hc⟩`. Substitute `hc` using the available equality. Take `⟨H, _, i, -, hmono, hfin, -, hH⟩` from `GlobalTheory.kernel_finiteFlat_subgroup K A.X A.ab L hL ha`. Establish `hF` using `GlobalTheory.FlagCovQF.finite_points H.hom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))`. Use `haveI := hF.to_subtype`.

Establish `hz : ∀ x : {x : A.Pt // AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0}, ∃ z : ptOver K (AlgebraicClosure K) ⟶ H, z ≫ i = x.1` using `fun x => (hH _ x.1).1 (memKL_of_lam_geom_eq_zero A hL x.1 x.2)`. Use `choose z hz using hz`. Use `Finite.of_injective (fun x => (⟨(z x).left, Over.w (z x)⟩ : {y : Sp (AlgebraicClosure K) ⟶ H.left | y ≫ H.hom = spMap (algebraMap K (AlgebraicClosure K))})) ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `e : z a = z b` using `Over.OverMorphism.ext (congrArg Subtype.val hab)`.

Conclude with `Subtype.ext ((hz a).symm.trans (e ▸ hz b))`.
-/
theorem GlobalTheory.AV.AbVar.finite_lam_eq_zero : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  intro K _ A c ⟨L, hL, ha, hc⟩
  subst hc
  obtain ⟨H, _, i, -, hmono, hfin, -, hH⟩ := GlobalTheory.kernel_finiteFlat_subgroup K A.X A.ab L hL ha
  have hF := GlobalTheory.FlagCovQF.finite_points H.hom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
  haveI := hF.to_subtype
  have hz : ∀ x : {x : A.Pt // AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0},
      ∃ z : ptOver K (AlgebraicClosure K) ⟶ H, z ≫ i = x.1 := fun x =>
    (hH _ x.1).1 (memKL_of_lam_geom_eq_zero A hL x.1 x.2)
  choose z hz using hz
  refine Finite.of_injective (fun x => (⟨(z x).left, Over.w (z x)⟩ :
    {y : Sp (AlgebraicClosure K) ⟶ H.left | y ≫ H.hom = spMap (algebraMap K (AlgebraicClosure K))})) ?_
  intro a b hab
  have e : z a = z b := Over.OverMorphism.ext (congrArg Subtype.val hab)
  exact Subtype.ext ((hz a).symm.trans (e ▸ hz b))
