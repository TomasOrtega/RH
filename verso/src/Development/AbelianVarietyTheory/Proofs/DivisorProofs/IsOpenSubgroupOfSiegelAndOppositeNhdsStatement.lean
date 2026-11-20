import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhds
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenSubgroupOfSiegelAndOppositeNhds.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U) → (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) → IsOpen (U : Set (UG c (stdJ ν E))) := by
  first | exact @GlobalTheory.KSp.isOpen_of_sieg_of_opp | exact GlobalTheory.KSp.isOpen_of_sieg_of_opp | (intros; apply GlobalTheory.KSp.isOpen_of_sieg_of_opp <;> assumption)
