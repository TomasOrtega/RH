import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSquare
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPreUOfFibres
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSectionStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifEven

open GlobalTheory.UU GlobalTheory.LN

/- English proof (translation)
Use `⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩` and prove the remaining obligations. Use `letI := Ideal.Quotient.field (maximalIdeal R)`. Use `infer_instance`.
-/
theorem isAdmissible_maximalIdeal_of_completeNormalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) : admitted R (maximalIdeal R) := by
  refine ⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩
  letI := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨hL, -, -, -, -⟩` from `GlobalTheory.lawsAndExpansions.1`. Take `⟨X, _, _, _, Q₀, P₀, ⟨wl, hl⟩, hev⟩` from `hE`. Use `hS.smooth` as an intermediate fact. Use `hS.geomConnected` as an intermediate fact. Use `GlobalTheory.PreUnifLocal.isLocalRing_quot (maximalIdeal.isMaximal R).ne_top 0` as an intermediate fact.

Establish `hsm : Smooth (thickObj R (maximalIdeal R) 0 G).hom` using `by show Smooth (pullback.snd _ _); infer_instance`. Establish `hgc : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom` using `by show GeometricallyConnected (pullback.snd _ _); infer_instance`. Take `⟨D₀⟩` from `TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev`. Set `G' : Over (Sp V)` to `(Over.pullback (spMap g)).obj G`. Establish `hS' : IsSemiAbelian G'` using `IsSemiAbelian.pullback _ G hS`.

Take `⟨P', wP, hP', H⟩` from `exists_cp_pull _ _ (spMap g) G G' _ _ (toBase_mul_pullback G (spMap g)) P`. Take `⟨ψ, sq'⟩` from `ClosedPol.exists_generic_square g hg`. Take `⟨A', gen', hgen', hA'⟩` from `ClosedPol.exists_fibre_pull hL sq' P.L.isLB A gen hA`. Rewrite `hA'` using `[← hP']`. Take `⟨wA, hwA⟩` from `hA'`.

Establish `le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap g`. Rewrite using `[zero_add, pow_one, pow_one, hc]`. Set `b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1)` to `Ideal.quotientMap (maximalIdeal V ^ (0 + 1)) g le`. Establish `sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap g`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]`.

Take `⟨P₁, w₁, H₁⟩` from `exists_isLevelCP (maximalIdeal V) 0 P'`. Take `⟨F, pF, w₃, k₃⟩` from `ClosedPol.exists_fourth (G := G) (G' := G') (H := thickObj R (maximalIdeal R) 0 G) (H' := thickObj V (maximalIdeal V) 0 G') (P := P) (P' := P') (N := P₀) (N' := P₁) sq (isGrpPullback_pullback G (spMap g)) (isGrpPullback_pullback G (thick R (maximalIdeal R) 0)) (isGrpPullback_pull …`. Take `⟨Q₁, D₁, -, -, -⟩` from `ClosedPol.exists_desc_pull pF Q₀ D₀ k₃`. Establish `ev` using `GlobalTheory.UniformizationSetting.exists_even_of_desc D₁`. Conclude with `⟨A', ⟨hV, hS', gen', hgen', P', wA, hwA, X, Q₁, P₁, ⟨w₁, H₁⟩, ev⟩, wP, H⟩`.
-/
theorem exists_setting {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G)
    (hE : EvenOn P) (A : PolAV (Sp (FractionRing R)))
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (g : R →+* V) (hg : Function.Injective g)
    (hc : (maximalIdeal V).comap g = maximalIdeal R) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap g)).obj G)) (w : _),
      IsCPMap s.P P (spMap g) (pullback.fst G.hom (spMap g)) pullback.condition w := by
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.lawsAndExpansions.1
  obtain ⟨X, _, _, _, Q₀, P₀, ⟨wl, hl⟩, hev⟩ := hE
  have := hS.smooth
  have := hS.geomConnected
  have := GlobalTheory.PreUnifLocal.isLocalRing_quot (maximalIdeal.isMaximal R).ne_top 0
  have hsm : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have hgc : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  let G' : Over (Sp V) := (Over.pullback (spMap g)).obj G
  have hS' : IsSemiAbelian G' := IsSemiAbelian.pullback _ G hS
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap g) G G' _ _ (toBase_mul_pullback G (spMap g)) P

  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square g hg
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull hL sq' P.L.isLB A gen hA
  rw [← hP'] at hA'
  obtain ⟨wA, hwA⟩ := hA'

  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap g := by
    rw [zero_add, pow_one, pow_one, hc]
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) :=
    Ideal.quotientMap (maximalIdeal V ^ (0 + 1)) g le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨P₁, w₁, H₁⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := G') (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 G') (P := P) (P' := P') (N := P₀) (N' := P₁) sq
    (isGrpPullback_pullback G (spMap g)) (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₁
  obtain ⟨Q₁, D₁, -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := GlobalTheory.UniformizationSetting.exists_even_of_desc D₁
  exact ⟨A', ⟨hV, hS', gen', hgen', P', wA, hwA, X, Q₁, P₁, ⟨w₁, H₁⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.UnifEven

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `R _ _ _ hB G _ _ P hS hEv A gen hgen hA`. Take `⟨⟨hL, hL2, hL3, -, -⟩, -⟩` from `GlobalTheory.lawsAndExpansions`. Establish `hE` using `GlobalTheory.LN.ega_holds`. Establish `hU` using `GlobalTheory.uniformisation_dvr_unconditional`. Establish `hR` using `GlobalTheory.Mum.UnifEven.isAdmissible_maximalIdeal_of_completeNormalCharZero hB`.

Use `hR.1.1` as an intermediate fact. Use `hR.2.2.1` as an intermediate fact. Establish `hI` using `hR.2.2.2.1`. Take `⟨V, _, _, _, φ, hV, hφ, hc⟩` from `GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)`. Use `hV.1` as an intermediate fact.

Establish `hB' : AdmBase V (maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩`. Establish `hle : (maximalIdeal R).map φ ≤ maximalIdeal V` using `Ideal.map_le_iff_le_comap.2 hc.ge`. Take `⟨D, U, rfl, rfl⟩` from `GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal R hB G P hS hEv A gen hgen hA`. Establish `hθ` using `GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section R hB D A G U hEv`. Use `haveI := hgen`.

Take `⟨A', s, w, hw⟩` from `GlobalTheory.Mum.UnifEven.exists_setting U.P hS hEv A U.gen hA hV φ hφ hc`. Take `⟨D', U₀, hLG, -, -⟩` from `hU V A' _ s`. Take `⟨U', hU'⟩` from `(GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre`. Use `s.semi.smooth` as an intermediate fact. Take `⟨w', hw'⟩` from `GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw`.

Take `⟨C, -⟩` from `GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' (maximalIdeal.isMaximal V).ne_top φ hle D _ A A' G _ U U' _ (isGrpPullback_pullback G _) w' hw'`. Take `⟨psi, h, Dd, hD, e, h₁, h₂, h₃⟩` from `GlobalTheory.T.exists_degData_psi_of_section_nonzero_fibres hL hL2 hE R (maximalIdeal R) hR V hV φ hφ hc D D' A A' G _ U U' U₀ _ C hU' hθ`. Take `⟨U₂, C₂, hD₂, eP, eg, k₁, k₂, k₃⟩` from `GlobalTheory.PrimeUnif.exists_move psi h C hD Dd.toPre e h₁ h₂ h₃`. Take `⟨U₁, -, hU₁, -⟩` from `GlobalTheory.UnifDescent.exists_unif_of_cmp hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' hI.ne_top φ hφ hle Dd D' A A' G _ U₂ U' U₀ _ C₂ hD₂ hU' k₁ k₂ k₃`. Conclude with `⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg GlobalTheory.UU.CP.L eP), hU₁.1.symm.trans eg⟩`.
-/
theorem GlobalTheory.Mum.exists_unif_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R (maximalIdeal R)) (U : Unif (maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  intro R _ _ _ hB G _ _ P hS hEv A gen hgen hA
  obtain ⟨⟨hL, hL2, hL3, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have hR := GlobalTheory.Mum.UnifEven.isAdmissible_maximalIdeal_of_completeNormalCharZero hB
  have := hR.1.1
  have := hR.2.2.1
  have hI := hR.2.2.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have := hV.1
  have hB' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨D, U, rfl, rfl⟩ := GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal R hB G P hS hEv A gen hgen hA
  have hθ := GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section R hB D A G U hEv
  haveI := hgen
  obtain ⟨A', s, w, hw⟩ := GlobalTheory.Mum.UnifEven.exists_setting U.P hS hEv A U.gen hA hV φ hφ hc
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' (maximalIdeal.isMaximal V).ne_top φ hle D _
    A A' G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  obtain ⟨psi, h, Dd, hD, e, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_degData_psi_of_section_nonzero_fibres hL hL2 hE R (maximalIdeal R) hR V hV φ hφ hc D D' A A' G _
    U U' U₀ _ C hU' hθ
  obtain ⟨U₂, C₂, hD₂, eP, eg, k₁, k₂, k₃⟩ := GlobalTheory.PrimeUnif.exists_move psi h C hD Dd.toPre e h₁ h₂ h₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' hI.ne_top φ hφ
    hle Dd D' A A' G _ U₂ U' U₀ _ C₂ hD₂ hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg GlobalTheory.UU.CP.L eP), hU₁.1.symm.trans eg⟩

end
