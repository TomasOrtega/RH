import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartsOfUpre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartJoin

/- English proof (translation)
Introduce `hU E _ _ _ H Dw hpq φ hpol hnsi l Xo c`. Take `⟨Z, zs, i, OZ, N, d, J, S, π, j, BD, hUP, hSep⟩` from `hU E H Dw hpq φ hpol hnsi l Xo c`. Take `⟨⟨-, -, -, -, -, hOZ, -⟩, ⟨hN, hdet⟩, -, ⟨hd, hJ, -⟩, ⟨-, -, hj, -, hji, -, hBD, -⟩, k₀, hamp⟩` from `id hUP`. Use `haveI := hj`. Establish `hpre` using `GlobalTheory.T.exists_tripleChart_unitary_boundary_point Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep`.

Take `⟨Y, ε, hYj, hYs, hsab⟩` from `GlobalTheory.T.unitary_compactification_isModel_of_charts Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre`. Take `⟨hsm, hsnc⟩` from `GlobalTheory.T.toroidalCompactification_smooth_snc_boundary Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre`. Establish `hch` using `fun x hx => GlobalTheory.UChartOf.charts_of_upre Y ε hYj hsab hpre x hx`. Establish `hYi : Y.j ≫ ε.hom ≫ π = i` using `by rw [← Category.assoc, hYj, hji]`. Use `⟨Y, BD.pull ε.hom (BD.keepsRegular_of_flat _), d, N * max k₀ 1, hd, ?_, ?_, ?_, ?_, fun x hx => (hch x hx).1, ?_, fun x hx _ => (hch x hx).2⟩` and prove the remaining obligations.

Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))`. Establish `h2 : genStr Y ≫ spMap (RingHom.id c.F) = genStr Y`. Rewrite using `[show spMap (RingHom.id c.F) = 𝟙 (Sp c.F) by simp [spMap]]`. Conclude with `Category.comp_id _`. Establish `e : genStr Y = (genι Y ≫ ε.hom) ≫ (π ≫ zs)`.

Rewrite using `[← h2, ← pullback.condition]`. Conclude with `(congrArg (genι Y ≫ ·) hYs).trans (by simp only [Category.assoc])`. Rewrite using `[e]`. Use `smoothOfRelativeDimension_comp (n := 0) (m := Dw.dim) (genι Y ≫ ε.hom) (π ≫ zs)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Use `GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y ≫ ε.hom) j.opensRange.compl (genBd Y) (fun a => ?_) hsnc` and prove the remaining obligations. Rewrite using `[mem_genBd]`. Use `show a ∉ Set.range Y.jQ ↔ (genι Y ≫ ε.hom) a ∉ Set.range j`. Use `not_congr ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z, rfl⟩`.

Conclude with `⟨z, by rw [← hYj]; rfl⟩`. Introduce and unpack `⟨z, hz⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `h1 : (genι Y ≫ ε.hom) (Y.jQ z) = (genι Y ≫ ε.hom) a`. Rewrite using `[← hz, ← hYj]`.

Both sides reduce to the same expression. Rewrite using `[← GlobalTheory.UChartOf.inv_apply_self (genι Y ≫ ε.hom) (Y.jQ z), h1, GlobalTheory.UChartOf.inv_apply_self]`. Introduce `x hx hab`. Rewrite `hx` using `[EffCartierData.idealSheaf_pull, hBD, Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]`. Take `⟨g, rfl⟩ : ∃ g : gen Y, genι Y g = x` from `⟨inv (genι Y) x, by`.

Rewrite using `[← Scheme.Hom.comp_apply, IsIso.inv_hom_id]`. Use the proof step `rfl⟩`. Establish `hg : g ∈ Set.range Y.jQ` using `by rw [← Y.ab_gen]; exact hab`. Take `⟨z, rfl⟩` from `hg`. Use `hJ _ hx ⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hYi]`. Both sides reduce to the same expression. Introduce `hL`. Establish `hk : k₀ ≤ max k₀ 1` using `le_max_left _ _`. Establish `hBL` using `BD.isLB_lb`.

Establish `hL'` using `(BD.pull ε.hom (BD.keepsRegular_of_flat _)).isLB_lb`. Establish `hA` using `(hamp _ hk).pull_of_isAffineHom ε.hom`. Establish `hAS : (CechPic.tens (lbPow (OZ.pull π) (max k₀ 1)) (CechPic.dual BD.lb)).IsLB` using `CechPic.isLB_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL)`. Establish `hP : (GlobalTheory.TorRef.polOf Y (N * max k₀ 1) (BD.pull ε.hom (BD.keepsRegular_of_flat _))).IsLB` using `CechPic.isLB_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL')`. Use `hA.of_lbIso hP ((CechPic.cls_eq_iff hP (LB.isLB_pull hAS ε.hom)).1 ?_)` and prove the remaining obligations.

Establish `e1 : CechPic.cls _ (LB.isLB_pull hOZ (ε.hom ≫ π)) = N • CechPic.cls _ hL`. Rewrite using `[(CechPic.cls_eq_iff _ (isLB_lbPow hL N)).2 (hdet Y (ε.hom ≫ π) hYi hL), CechPic.cls_lbPow hL]`. Establish `e2 : CechPic.cls _ hL' = CechPic.pull ε.hom (CechPic.cls _ hBL)`. Rewrite using `[(CechPic.cls_eq_iff _ (LB.isLB_pull hBL _)).2 (BD.lbIso_pull _ _), CechPic.cls_pull hBL]`. Rewrite `e1` using `[CechPic.cls_pull hOZ, CechPic.pull_comp]`.

Use `(CechPic.cls_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL') hP).trans ?_` and prove the remaining obligations. Rewrite using `[CechPic.cls_pull hAS ε.hom, CechPic.cls_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL), CechPic.cls_lbPow hL, CechPic.cls_lbPow (LB.isLB_pull hOZ π), CechPic.cls_dual hL', CechPic.cls_dual hBL, CechPic.cls_pull hOZ π, e2, map_add, map_nsmul, map_neg, e1, mul_ns …`.
-/
theorem rigidForFan_of_uStB : UStB → GlobalTheory.RigChart.RigidForFan := by
  intro hU E _ _ _ H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨Z, zs, i, OZ, N, d, J, S, π, j, BD, hUP, hSep⟩ := hU E H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨⟨-, -, -, -, -, hOZ, -⟩, ⟨hN, hdet⟩, -, ⟨hd, hJ, -⟩, ⟨-, -, hj, -, hji, -, hBD, -⟩, k₀, hamp⟩ := id hUP
  haveI := hj
  have hpre := GlobalTheory.T.exists_tripleChart_unitary_boundary_point Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep
  obtain ⟨Y, ε, hYj, hYs, hsab⟩ := GlobalTheory.T.unitary_compactification_isModel_of_charts Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  obtain ⟨hsm, hsnc⟩ := GlobalTheory.T.toroidalCompactification_smooth_snc_boundary Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  have hch := fun x hx => GlobalTheory.UChartOf.charts_of_upre Y ε hYj hsab hpre x hx
  have hYi : Y.j ≫ ε.hom ≫ π = i := by rw [← Category.assoc, hYj, hji]
  refine ⟨Y, BD.pull ε.hom (BD.keepsRegular_of_flat _), d, N * max k₀ 1, hd, ?_, ?_, ?_, ?_, fun x hx => (hch x hx).1, ?_,
    fun x hx _ => (hch x hx).2⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  ·
    have h2 : genStr Y ≫ spMap (RingHom.id c.F) = genStr Y := by
      rw [show spMap (RingHom.id c.F) = 𝟙 (Sp c.F) by simp [spMap]]
      exact Category.comp_id _
    have e : genStr Y = (genι Y ≫ ε.hom) ≫ (π ≫ zs) := by
      rw [← h2, ← pullback.condition]
      exact (congrArg (genι Y ≫ ·) hYs).trans (by simp only [Category.assoc])
    rw [e]
    have := smoothOfRelativeDimension_comp (n := 0) (m := Dw.dim) (genι Y ≫ ε.hom) (π ≫ zs)
    rwa [zero_add] at this
  ·
    refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y ≫ ε.hom) j.opensRange.compl (genBd Y) (fun a => ?_) hsnc
    rw [mem_genBd]
    show a ∉ Set.range Y.jQ ↔ (genι Y ≫ ε.hom) a ∉ Set.range j
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hYj]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have h1 : (genι Y ≫ ε.hom) (Y.jQ z) = (genι Y ≫ ε.hom) a := by
        rw [← hz, ← hYj]; rfl
      rw [← GlobalTheory.UChartOf.inv_apply_self (genι Y ≫ ε.hom) (Y.jQ z), h1, GlobalTheory.UChartOf.inv_apply_self]
  ·
    intro x hx hab
    rw [EffCartierData.idealSheaf_pull, hBD, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨g, rfl⟩ : ∃ g : gen Y, genι Y g = x := ⟨inv (genι Y) x, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hg : g ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hab
    obtain ⟨z, rfl⟩ := hg
    refine hJ _ hx ⟨z, ?_⟩
    rw [← hYi]
    rfl
  ·
    intro hL
    have hk : k₀ ≤ max k₀ 1 := le_max_left _ _
    have hBL := BD.isLB_lb
    have hL' := (BD.pull ε.hom (BD.keepsRegular_of_flat _)).isLB_lb
    have hA := (hamp _ hk).pull_of_isAffineHom ε.hom
    have hAS : (CechPic.tens (lbPow (OZ.pull π) (max k₀ 1)) (CechPic.dual BD.lb)).IsLB :=
      CechPic.isLB_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL)
    have hP : (GlobalTheory.TorRef.polOf Y (N * max k₀ 1) (BD.pull ε.hom (BD.keepsRegular_of_flat _))).IsLB :=
      CechPic.isLB_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL')
    refine hA.of_lbIso hP ((CechPic.cls_eq_iff hP (LB.isLB_pull hAS ε.hom)).1 ?_)
    have e1 : CechPic.cls _ (LB.isLB_pull hOZ (ε.hom ≫ π)) = N • CechPic.cls _ hL := by
      rw [(CechPic.cls_eq_iff _ (isLB_lbPow hL N)).2 (hdet Y (ε.hom ≫ π) hYi hL), CechPic.cls_lbPow hL]
    have e2 : CechPic.cls _ hL' = CechPic.pull ε.hom (CechPic.cls _ hBL) := by
      rw [(CechPic.cls_eq_iff _ (LB.isLB_pull hBL _)).2 (BD.lbIso_pull _ _), CechPic.cls_pull hBL]
    rw [CechPic.cls_pull hOZ, CechPic.pull_comp] at e1
    refine (CechPic.cls_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL') hP).trans ?_
    rw [CechPic.cls_pull hAS ε.hom,
      CechPic.cls_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL),
      CechPic.cls_lbPow hL, CechPic.cls_lbPow (LB.isLB_pull hOZ π), CechPic.cls_dual hL', CechPic.cls_dual hBL,
      CechPic.cls_pull hOZ π, e2, map_add, map_nsmul, map_neg, e1, mul_nsmul]

end GlobalTheory.UChartJoin
