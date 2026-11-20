import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolQuasiInverse
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.OneCompPrj
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLam
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KLiftSqToBase
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmple
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.ExistsQuat
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfCls
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIsMonHomIdPow

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

/- English proof (translation)
Take `⟨m, mu, hm, hmu, h₁, h₂⟩` from `hq`. Take `⟨α, hα, hα'⟩` from `exists_quat (4 * m ^ 2 - 1)`. Use `hpol.1` as an intermediate fact. Use `⟨zc hD.isLB l mu α, (zc_rigid hD l mu α).1, (zc_rigid hD l mu α).2, fun Ω _ _ s => ?_⟩` and prove the remaining obligations. Take `⟨L, hL, ha, e⟩` from `hpol.2 Ω s`.

Conclude with `⟨zb mu α s P L, isLB_zb mu α s hD.isLB hL, relAmple_zb hA hB hD hD' l mu α Ω s L hL e ha g hgA hgB m hm h₁ h₂ hα hα', kTriv_zb hA hB hD hD' l mu α Ω s L hL e m hm h₁ h₂ hα hα', lam_zb hA hB hD hD' l mu α Ω s L hL e⟩`.
-/
theorem principal_of_quasiInverse {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (l : A ⟶ B) (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (hD : IsDual A B P) (hD' : IsDual B A (swap P))
    (hpol : GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.IsPolarisation A B P l)
    (hq : ∃ (m : ℕ) (mu : B ⟶ A), 1 ≤ m ∧ IsMonHom mu ∧ l ≫ mu = 𝟙 A ^ m ∧ mu ≫ l = 𝟙 B ^ m) :
    ∃ c : Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left, IsPrincipalPol (G4 (A ⊗ B)) c := by
  obtain ⟨m, mu, hm, hmu, h₁, h₂⟩ := hq
  obtain ⟨α, hα, hα'⟩ := exists_quat (4 * m ^ 2 - 1)
  have := hpol.1
  refine ⟨zc hD.isLB l mu α, (zc_rigid hD l mu α).1, (zc_rigid hD l mu α).2, fun Ω _ _ s => ?_⟩
  obtain ⟨L, hL, ha, e⟩ := hpol.2 Ω s
  exact ⟨zb mu α s P L, isLB_zb mu α s hD.isLB hL,
    relAmple_zb hA hB hD hD' l mu α Ω s L hL e ha g hgA hgB m hm h₁ h₂ hα hα',
    kTriv_zb hA hB hD hD' l mu α Ω s L hL e m hm h₁ h₂ hα hα',
    lam_zb hA hB hD hD' l mu α Ω s L hL e⟩

open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin in

/- English proof (translation)
Introduce `C _ _ v R _ _ hv A _ L hA hL ha`. Use `isLocalRing_integers hv` as an intermediate fact. Establish `hΛ : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Take `⟨a₁, a₂⟩` from `GlobalTheory.CubeDual.isAdditive_lam hC hA hL hΛ`. Take `⟨B, _, P, hB, hdim, h₁, h₂⟩` from `hD _ A hA`.

Take `⟨x, hx, -⟩` from `h₁.univ A (abelian₂ A L) hΛ a₁`. Establish `hm` using `isMonHom_of_classifying _ A A B (abelian₂ A L) P h₁ h₂.additive hΛ a₂ x hx`. Take `⟨g, hgA⟩` from `GlobalTheory.AbelianDim.exists_relDim R A hA`. Establish `hpol` using `isPolarisation_of_relAmple h₁.isLB hm hL ha hx`. Take `⟨c, hc⟩` from `principal_of_quasiInverse A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol (hQ C v R hv A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol)`.

Establish `hAB` using `AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB`. Establish `h4 : IsAbelianScheme (G4 (A ⊗ B))` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))`. Take `⟨M, hM, m₁, m₂, m₃, m₄, -⟩` from `SymB.symmetricBundle hD hC C v R hv _ h4 c hc`. Take `⟨g', hg'⟩` from `GlobalTheory.AbelianDim.exists_relDim R _ h4`. Use `hA.comm` as an intermediate fact.

Use `hB.comm` as an intermediate fact. Use `⟨⟨G4 (A ⊗ B), h4, g', hg', M, hM, m₁, m₂, m₃, m₄⟩, lift (lift (𝟙 A) 1) 1, fst _ _ ≫ fst _ _, inferInstance, inferInstance, by simp⟩` and prove the remaining obligations.
-/
theorem zarhinStatement_of_dual_cube_qiR (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem)
    (hQ : QuasiInverseR) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement := by
  intro C _ _ v R _ _ hv A _ L hA hL ha
  have := isLocalRing_integers hv
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeDual.isAdditive_lam hC hA hL hΛ
  obtain ⟨B, _, P, hB, hdim, h₁, h₂⟩ := hD _ A hA
  obtain ⟨x, hx, -⟩ := h₁.univ A (abelian₂ A L) hΛ a₁
  have hm := isMonHom_of_classifying _ A A B (abelian₂ A L) P h₁ h₂.additive hΛ a₂ x hx
  obtain ⟨g, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim R A hA
  have hpol := isPolarisation_of_relAmple h₁.isLB hm hL ha hx
  obtain ⟨c, hc⟩ := principal_of_quasiInverse A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol
    (hQ C v R hv A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol)
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4 : IsAbelianScheme (G4 (A ⊗ B)) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  obtain ⟨M, hM, m₁, m₂, m₃, m₄, -⟩ := SymB.symmetricBundle hD hC C v R hv _ h4 c hc
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim R _ h4
  have := hA.comm
  have := hB.comm
  refine ⟨⟨G4 (A ⊗ B), h4, g', hg', M, hM, m₁, m₂, m₃, m₄⟩, lift (lift (𝟙 A) 1) 1, fst _ _ ≫ fst _ _,
    inferInstance, inferInstance, by simp⟩

/- English proof (translation)
The claim follows from `zarhinStatement_of_dual_cube_qiR hD hC quasiInverseR`.
-/
theorem zarhinStatement_of_dual_cube (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem) :
    GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement :=
  zarhinStatement_of_dual_cube_qiR hD hC quasiInverseR

end PositivityTheory.PrwZar
