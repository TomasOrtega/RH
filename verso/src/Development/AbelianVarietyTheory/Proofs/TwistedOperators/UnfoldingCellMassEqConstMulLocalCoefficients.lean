import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubiniStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHaarVolumeOfConjugateLatticeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `GlobalTheory.RowReal.big_mono ?_ (Big.and GlobalTheory.T.finitePoints_rowPeriod_conjLevel_fubini (Big.and GlobalTheory.T.doubleCosetProjection_volume_const_mul GlobalTheory.T.exists_haar_volume_of_conjugate_lattice))` and prove the remaining obligations. Introduce `D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH j hj`. Take `⟨hA, hB, hC⟩` from `h`. Take `⟨κ, la, ν, hκ, hla, hν, hAeq⟩` from `hA j hj (ρ j) (hH j hj).1`. Take `⟨κ', hκ', hBeq⟩` from `hB s j hj ν hν`.

Take `⟨V₀, hV₀, hCeq⟩` from `hC s j hj la hla`. Establish `hjm : j ≤ D.R.m` using `by rw [idx, List.mem_range'_1] at hj; omega`. Use `⟨(((μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) : ℝ) : ℂ), fun t Φ β b hb M M' hM hM' x hx hbj => ?_⟩` and prove the remaining obligations. Establish `e1` using `hAeq ⟨b j, hbj⟩`. Establish `e2` using `hBeq t Φ β b hb M M' hM hM' x hx hbj`.

Establish `e3` using `hCeq t β b hb hbj`. Establish `hx0 : (x : ℝ) ≠ 0`. Introduce `h0`. Establish `hH'` using `(hM.vtx (.top j) hjm).haar_fund.1`. Establish `hz : M.ν (.top j) = 0`.

Rewrite using `[hx, show x = 0 from NNReal.coe_eq_zero.1 h0, zero_smul]`. Establish `hpos` using `Measure.IsOpenPosMeasure.open_pos (μ := M.ν (.top j)) Set.univ isOpen_univ Set.univ_nonempty`. Rewrite `hpos` using `[hz]`. Conclude with `hpos rfl`. Use `set lv := la.real {n | (⟨b j, hbj⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hbj⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} with hlv`.

Use `set cc : ℝ := (GlobalTheory.RowWt.colCoef ch t β j : ℝ) with hcc`. Establish `hlv0 : lv ≠ 0` using `fun h0 => by rw [h0, zero_mul] at e3; exact hV₀.ne' e3.symm`. Unfold `cellWt`. Rewrite using `[e1, e2]`. Establish `key : (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * lv * (κ' * x)) * x = (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) * cc`.

Establish `hcc0 : cc ≠ 0` using `fun h0 => by rw [h0, mul_zero] at e3; exact hV₀.ne' e3.symm`. Establish `hk1` using `hκ.ne'`. Establish `hk2` using `hκ'.ne'`. Rewrite using `[← e3]`. Clear the denominators using the available nonvanishing facts.

Use `congrArg (fun r : ℝ => (r : ℂ)) key` as an intermediate fact. Simplify using `only [hcc] at this`. Move the coercions through the operations in `at this ⊢`. Conclude with `this`.
-/
theorem cell_mass : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ)
    (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ j ∈ idx D, ∃ c : ℂ, ∀ t Φ β b, IsRep t ch.S.B s β b →
      ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' → ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) →
        ∀ hb : b j ∈ GfC _, cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, hb⟩ * ((x : ℝ) : ℂ) =
          c * (GlobalTheory.RowWt.colCoef ch t β j : ℂ) := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and GlobalTheory.T.finitePoints_rowPeriod_conjLevel_fubini (Big.and GlobalTheory.T.doubleCosetProjection_volume_const_mul GlobalTheory.T.exists_haar_volume_of_conjugate_lattice))
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH j hj
  obtain ⟨hA, hB, hC⟩ := h
  obtain ⟨κ, la, ν, hκ, hla, hν, hAeq⟩ := hA j hj (ρ j) (hH j hj).1
  obtain ⟨κ', hκ', hBeq⟩ := hB s j hj ν hν
  obtain ⟨V₀, hV₀, hCeq⟩ := hC s j hj la hla
  have hjm : j ≤ D.R.m := by rw [idx, List.mem_range'_1] at hj; omega
  refine ⟨(((μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) : ℝ) : ℂ),
    fun t Φ β b hb M M' hM hM' x hx hbj => ?_⟩
  have e1 := hAeq ⟨b j, hbj⟩
  have e2 := hBeq t Φ β b hb M M' hM hM' x hx hbj
  have e3 := hCeq t β b hb hbj
  have hx0 : (x : ℝ) ≠ 0 := by
    intro h0
    have hH' := (hM.vtx (.top j) hjm).haar_fund.1
    have hz : M.ν (.top j) = 0 := by
      rw [hx, show x = 0 from NNReal.coe_eq_zero.1 h0, zero_smul]
    have hpos := Measure.IsOpenPosMeasure.open_pos (μ := M.ν (.top j)) Set.univ isOpen_univ Set.univ_nonempty
    rw [hz] at hpos
    exact hpos rfl
  set lv := la.real {n | (⟨b j, hbj⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hbj⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} with hlv
  set cc : ℝ := (GlobalTheory.RowWt.colCoef ch t β j : ℝ) with hcc
  have hlv0 : lv ≠ 0 := fun h0 => by rw [h0, zero_mul] at e3; exact hV₀.ne' e3.symm
  unfold cellWt
  rw [e1, e2]
  have key : (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * lv * (κ' * x)) * x =
      (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) * cc := by
    have hcc0 : cc ≠ 0 := fun h0 => by rw [h0, mul_zero] at e3; exact hV₀.ne' e3.symm
    have hk1 := hκ.ne'
    have hk2 := hκ'.ne'
    rw [← e3]
    field_simp
  have := congrArg (fun r : ℝ => (r : ℂ)) key
  simp only [hcc] at this
  push_cast at this ⊢
  exact this

end GlobalTheory.CellMass
