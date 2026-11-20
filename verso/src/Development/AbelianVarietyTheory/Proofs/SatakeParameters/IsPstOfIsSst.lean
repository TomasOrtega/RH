import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRestStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BridgeJMemKwOfDecLe
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DRSstCrysPstJumpsDescend
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.WdRelOfFrobSS
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IwahoriSphericalTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrict
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut.IwaAll

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module

/- English proof (translation)
Establish `hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l]`. Use extensionality with `x`. Simplify using `[mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]`. Establish `e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ)`. Rewrite using `[hD, finrank_mul_finrank]`.

Both sides reduce to the same expression. Rewrite using `[IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

/- English proof (translation)
Rewrite using `[← GlobalTheory.PstCoeff.isPst_resQ_iff]`. Apply `GlobalTheory.PMon.isPst_of_isSst_resTo l P AI T K K le_rfl V` to reduce the goal to its premises. Establish `hD : Dst P (resTo (GlobalTheory.PstCoeff.resQ ρ) (le_refl K.1)) = Dst P (GlobalTheory.PstCoeff.resQ ρ)`. Use extensionality with `x`. Rewrite using `[mem_Dst_resTo, mem_Dst]`.

Conclude with `⟨fun H g => H g g.2, fun H g _ => H g⟩`. Use `isSst_resQ P ρ h` as an intermediate fact. Rewrite `this`, the goal using `[IsSst]`. Rewrite using `[hD]`. Conclude with `this`.
-/
theorem isPst_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) {K : FinExt l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsPst P ρ := by
  rw [← GlobalTheory.PstCoeff.isPst_resQ_iff]
  apply GlobalTheory.PMon.isPst_of_isSst_resTo l P AI T K K le_rfl V
  have hD : Dst P (resTo (GlobalTheory.PstCoeff.resQ ρ) (le_refl K.1)) = Dst P (GlobalTheory.PstCoeff.resQ ρ) := by
    ext x
    rw [mem_Dst_resTo, mem_Dst]
    exact ⟨fun H g => H g g.2, fun H g _ => H g⟩
  have := isSst_resQ P ρ h
  rw [IsSst] at this ⊢
  rw [hD]
  exact this

/- English proof (translation)
Introduce and unpack `⟨LL', r', hm, hs⟩`. Take `⟨T⟩` from `hT`. Use `haveI := LL'.2`. Conclude with `⟨LL', r', hm, isPst_of_isSst P AI T _ hs⟩`.
-/
theorem isPstAt_of_isSstAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* GL (Fin a) (Om l)) :
    IsSstAt P Bw r → IsPstAt P Bw r := by
  rintro ⟨LL', r', hm, hs⟩
  obtain ⟨T⟩ := hT
  haveI := LL'.2
  exact ⟨LL', r', hm, isPst_of_isSst P AI T _ hs⟩

end GlobalTheory.GalCut.IwaAll

end
