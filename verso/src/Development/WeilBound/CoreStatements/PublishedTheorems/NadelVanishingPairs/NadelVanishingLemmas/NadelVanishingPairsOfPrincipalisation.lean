import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealSupportNonKlt
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingTheorem

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

/- English proof (translation)
Introduce `X _ _ _ p n hproj hdim N Δ m G r M₀ hN hΔ hm hlc hr hnef hbig hcurve`. Use `letI := algebraΓOfHom p`. Take `⟨η, hlm⟩` from `hlc.exists_isLogMult hm`. Take `⟨J, hJ, hsupp⟩` from `exists_isMultIdeal_support_iff_not_kltAt hP ℂ X p n hproj hdim Δ η m G hlm`. Take `⟨H, hH⟩` from `exists_isAmpleLB_of_isProjOver hproj`.

Establish `hM : M₀.IsLB` using `hnef.isLB`. Establish `hG : (toLB G).IsLB` using `isLB_toLB G`. Establish `hP1 : (lbPow N (m * r)).IsLB` using `isLB_lbPow hN _`. Establish `hP2 : (lbPow (toLB G) r).IsLB` using `isLB_lbPow hG _`. Establish `hP3 : (lbPow M₀ m).IsLB` using `isLB_lbPow hM _`.

Establish `hD2 : (dual (lbPow (toLB G) r)).IsLB` using `isLB_dual hP2`. Establish `hD3 : (dual (lbPow M₀ m)).IsLB` using `isLB_dual hP3`. Establish `hS : (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m))).IsLB` using `isLB_tens hD2 hD3`. Establish `hTl : (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))).IsLB` using `isLB_tens hP1 hS`. Establish `hclsS : cls _ hS = cls _ hD2 + cls _ hD3` using `cls_tens hD2 hD3 hS`.

Establish `hclsT : cls _ hTl = cls _ hP1 + cls _ hS` using `cls_tens hP1 hS hTl`. Establish `hT : IsNef ℂ (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m))))`. Use `⟨hTl, fun Z hZ => ?_⟩` and prove the remaining obligations. Establish `e1` using `hZ.interNumRed_of_cls_eq_add hH hTl hP1 hS hclsT`. Establish `e2` using `hZ.interNumRed_of_cls_eq_add hH hS hD2 hD3 hclsS`.

Establish `e3` using `hZ.interNumRed_dual (L := lbPow (toLB G) r) hH hP2`. Establish `e4` using `hZ.interNumRed_dual (L := lbPow M₀ m) hH hP3`. Establish `e5` using `hZ.interNumRed_lbPow hH hN (m * r)`. Establish `e6` using `hZ.interNumRed_lbPow hH hG r`. Establish `e7` using `hZ.interNumRed_lbPow hH hM m`.

Establish `hq` using `hcurve Z hZ`. Establish `hmq : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hrq : (r : ℚ) ≠ 0` using `by exact_mod_cast hr.ne'`. Establish `hz : ((m : ℤ) * r) * interNumRed ℂ Z ![N] = r * interNumRed ℂ Z ![toLB G] + m * interNumRed ℂ Z ![M₀]`. Establish `: ((m : ℚ) * r) * (interNumRed ℂ Z ![N] : ℚ) = r * (interNumRed ℂ Z ![toLB G] : ℚ) + m * (interNumRed ℂ Z ![M₀] : ℚ)`.

Rewrite using `[hq]`. Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions. Rewrite using `[e1, e2, e3, e4, e5, e6, e7]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcls : cls _ hT.isLB = (m * r) • cls N hN - r • toPic G - m • cls M₀ hM`. Rewrite using `[hclsT, hclsS, cls_dual hP2 hD2, cls_dual hP3 hD3, cls_lbPow hN (m * r) hP1, cls_lbPow hG r hP2, cls_lbPow hM m hP3]`. Establish `: cls (toLB G) hG = toPic G` using `rfl`. Rewrite using `[this]`.

Normalize the expressions using the abelian group laws. Conclude with `⟨J, hsupp, fun i hi => GlobalTheory.nadelVanishing hP ℂ X p n hproj hdim Δ η m G hΔ.nonneg hlm N M₀ _ hN hM r hT hr hcls hnef hbig J hJ i hi⟩`.
-/
theorem nadelVanishingPair_of_principalisation (hP : GlobalTheory.Published.Principalisation) :
    GlobalTheory.Published.NadelVanishingPair := by
  intro X _ _ _ p n hproj hdim N Δ m G r M₀ hN hΔ hm hlc hr hnef hbig hcurve
  letI := algebraΓOfHom p
  obtain ⟨η, hlm⟩ := hlc.exists_isLogMult hm
  obtain ⟨J, hJ, hsupp⟩ :=
    exists_isMultIdeal_support_iff_not_kltAt hP ℂ X p n hproj hdim Δ η m G hlm
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hM : M₀.IsLB := hnef.isLB
  have hG : (toLB G).IsLB := isLB_toLB G
  have hP1 : (lbPow N (m * r)).IsLB := isLB_lbPow hN _
  have hP2 : (lbPow (toLB G) r).IsLB := isLB_lbPow hG _
  have hP3 : (lbPow M₀ m).IsLB := isLB_lbPow hM _
  have hD2 : (dual (lbPow (toLB G) r)).IsLB := isLB_dual hP2
  have hD3 : (dual (lbPow M₀ m)).IsLB := isLB_dual hP3
  have hS : (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m))).IsLB := isLB_tens hD2 hD3
  have hTl : (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))).IsLB :=
    isLB_tens hP1 hS
  have hclsS : cls _ hS = cls _ hD2 + cls _ hD3 := cls_tens hD2 hD3 hS
  have hclsT : cls _ hTl = cls _ hP1 + cls _ hS := cls_tens hP1 hS hTl
  have hT : IsNef ℂ (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))) := by
    refine ⟨hTl, fun Z hZ => ?_⟩
    have e1 := hZ.interNumRed_of_cls_eq_add hH hTl hP1 hS hclsT
    have e2 := hZ.interNumRed_of_cls_eq_add hH hS hD2 hD3 hclsS
    have e3 := hZ.interNumRed_dual (L := lbPow (toLB G) r) hH hP2
    have e4 := hZ.interNumRed_dual (L := lbPow M₀ m) hH hP3
    have e5 := hZ.interNumRed_lbPow hH hN (m * r)
    have e6 := hZ.interNumRed_lbPow hH hG r
    have e7 := hZ.interNumRed_lbPow hH hM m
    have hq := hcurve Z hZ
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    have hz : ((m : ℤ) * r) * interNumRed ℂ Z ![N] = r * interNumRed ℂ Z ![toLB G] + m * interNumRed ℂ Z ![M₀] := by
      have : ((m : ℚ) * r) * (interNumRed ℂ Z ![N] : ℚ) = r * (interNumRed ℂ Z ![toLB G] : ℚ) + m * (interNumRed ℂ Z ![M₀] : ℚ) := by
        rw [hq]
        field_simp
      exact_mod_cast this
    rw [e1, e2, e3, e4, e5, e6, e7]
    push_cast
    linarith
  have hcls : cls _ hT.isLB = (m * r) • cls N hN - r • toPic G - m • cls M₀ hM := by
    rw [hclsT, hclsS, cls_dual hP2 hD2, cls_dual hP3 hD3, cls_lbPow hN (m * r) hP1, cls_lbPow hG r hP2,
      cls_lbPow hM m hP3]
    have : cls (toLB G) hG = toPic G := rfl
    rw [this]
    abel
  exact ⟨J, hsupp, fun i hi =>
    GlobalTheory.nadelVanishing hP ℂ X p n hproj hdim Δ η m G hΔ.nonneg hlm N M₀ _ hN hM r hT hr hcls hnef hbig J hJ i hi⟩

end GlobalTheory.Discrepancy
