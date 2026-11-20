import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8PowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpEvenOn
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `hL _ _ V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW`. Set `P₁ : GlobalTheory.UU.CP G₀` to `GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.globalFns`. Take `⟨Pc, hPc⟩` from `GlobalTheory.T.cubical_structure_e8_power _ G₀ P₁ W`. Use `⟨Pc, hPc, ?_⟩` and prove the remaining obligations. Establish `hS8 : IsSemiAbelian (powObj G₀ 8)` using `GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS`.

Take `⟨D', ⟨pD⟩⟩` from `GlobalTheory.PowDegData.main hL.globalFns V₁ _ D₀ 8`. Take `⟨A', pA, -⟩` from `GlobalTheory.exists_powPolAV _ A₀ 8`. Take `⟨U', -⟩` from `GlobalTheory.PowUnif.main hL.globalFns V₁ _ 8 D₀ D' A₀ A' G₀ (powObj G₀ 8) pD pA (powIsPowGrp G₀ 8) U₀.toUnifPre`. Establish `hp : IsProper (pullback.snd (powObj G₀ 8).hom (jK V₁))`. Use `A'.isAb.proper` as an intermediate fact.

Establish `e : pullback.snd (powObj G₀ 8).hom (jK V₁) = U'.gen.hom.left ≫ A'.A.hom` using `(Over.w U'.gen.hom).symm`. Establish `: IsIso U'.gen.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))`. Conclude with `e ▸ MorphismProperty.comp_mem @IsProper U'.gen.hom.left A'.A.hom inferInstance A'.isAb.proper`. Establish `h3` using `GlobalTheory.EvenTriv.surjective_cube_of_generic (powObj G₀ 8) hS8 hp`. Take `⟨w, -, hw, -, -, hwL, -⟩` from `GlobalTheory.PowE8.hypW_e8LB _ G₀ P₁ W hW`.

Establish `hwL' : LBIso Pc.L.L (cubeLB (powObj G₀ 8) ![𝟙 _, w] Pc.L.L)` using `by rw [hPc]; exact hwL`. Take `⟨P₀, v, hv⟩` from `GlobalTheory.UU.exists_isLevelCP (maximalIdeal V₁) 0 Pc`. Establish `hB' : IsAbelianScheme (thickObj V₁ (maximalIdeal V₁) 0 D'.toPre.P.A)` using `GlobalTheory.isAbelianScheme_pullback_obj _ _ D'.toPre.P.isAb`. Set `Q₀` to `GlobalTheory.Mum.tqOfGtCoord (U'.gt 0) hB'`. Establish `hm : (maximalIdeal V₁ ^ (0 + 1)).IsMaximal`.

Rewrite using `[zero_add, pow_one]`. Use `infer_instance`. Use `letI : Field (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) := Ideal.Quotient.field _`. Establish `hS0` using `IsSemiAbelian.pullback (thick V₁ (maximalIdeal V₁) 0) (powObj G₀ 8) hS8`. Use `hS0.smooth` as an intermediate fact.

Use `hS0.geomConnected` as an intermediate fact. Use `Q₀.i_hom` as an intermediate fact. Use `letI := D'.toPre.addX`. Use `haveI := D'.toPre.freeX`. Use `haveI := D'.toPre.finX`.

Take `⟨s⟩` from `GlobalTheory.BiextTriv.main (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) D'.toPre.X (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)) P₀.L P₀.c Q₀.i Q₀.i_hom`. Use `haveI := hw`. Take `⟨σ, hσ⟩` from `GlobalTheory.EvenTriv.exists_even_of_surjective h3 Pc w hwL' P₀ (IsPullback.of_hasPullback (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0)) hv Q₀.i s`. Conclude with `⟨D'.toPre.X, D'.toPre.addX, D'.toPre.freeX, D'.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩`.
-/
theorem exists_cp_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  intro hL _ _ V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  let P₁ : GlobalTheory.UU.CP G₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₁ W
  refine ⟨Pc, hPc, ?_⟩
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D', ⟨pD⟩⟩ := GlobalTheory.PowDegData.main hL.globalFns V₁ _ D₀ 8
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ A₀ 8
  obtain ⟨U', -⟩ := GlobalTheory.PowUnif.main hL.globalFns V₁ _ 8 D₀ D' A₀ A' G₀ (powObj G₀ 8) pD pA (powIsPowGrp G₀ 8)
    U₀.toUnifPre
  have hp : IsProper (pullback.snd (powObj G₀ 8).hom (jK V₁)) := by
    have := A'.isAb.proper
    have e : pullback.snd (powObj G₀ 8).hom (jK V₁) = U'.gen.hom.left ≫ A'.A.hom := (Over.w U'.gen.hom).symm
    have : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U'.gen.hom.left A'.A.hom inferInstance A'.isAb.proper
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic (powObj G₀ 8) hS8 hp
  obtain ⟨w, -, hw, -, -, hwL, -⟩ := GlobalTheory.PowE8.hypW_e8LB _ G₀ P₁ W hW
  have hwL' : LBIso Pc.L.L (cubeLB (powObj G₀ 8) ![𝟙 _, w] Pc.L.L) := by rw [hPc]; exact hwL
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V₁) 0 Pc
  have hB' : IsAbelianScheme (thickObj V₁ (maximalIdeal V₁) 0 D'.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D'.toPre.P.isAb
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U'.gt 0) hB'
  have hm : (maximalIdeal V₁ ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) := Ideal.Quotient.field _
  have hS0 := IsSemiAbelian.pullback (thick V₁ (maximalIdeal V₁) 0) (powObj G₀ 8) hS8
  have := hS0.smooth
  have := hS0.geomConnected
  have := Q₀.i_hom
  letI := D'.toPre.addX
  haveI := D'.toPre.freeX
  haveI := D'.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) D'.toPre.X
    (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)) P₀.L P₀.c Q₀.i Q₀.i_hom
  haveI := hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective h3 Pc w hwL' P₀
    (IsPullback.of_hasPullback (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0)) hv Q₀.i s
  exact ⟨D'.toPre.X, D'.toPre.addX, D'.toPre.freeX, D'.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

end GlobalTheory.PowE8
end
