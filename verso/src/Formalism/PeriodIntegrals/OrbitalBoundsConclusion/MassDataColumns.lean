import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ColsDimStepOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.UnitaryLevelClosureSubgroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.OpenCompact
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ClassCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Transfer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Unfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HinfCpt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxAsm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HModelAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelClauseAdaptedBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassUnfoldGenHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsHermNDOfSetting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA

noncomputable section

namespace PIW.MassDataColumns

/- English proof (translation)
Use `haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)`. Use `set S : K ⧸ K'.subgroupOf K → Set G := fun q => (fun h => ((q.out : K) : G)⁻¹ * h) ⁻¹' (K' : Set G) with hS`. Establish `hunion : (K : Set G) = ⋃ q, S q`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `Set.mem_iUnion.2 ⟨QuotientGroup.mk (⟨x, hx⟩ : K), ?_⟩` and prove the remaining obligations. Establish `e` using `QuotientGroup.out_eq' (QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ K'.subgroupOf K)`. Rewrite `e` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv] at e`.

Rewrite using `[hS, Set.mem_preimage]`. Conclude with `e`. Introduce `hx`. Take `⟨q, hq⟩` from `Set.mem_iUnion.1 hx`. Rewrite `hq` using `[hS, Set.mem_preimage]`.

Establish `h1 : ((q.out : K) : G) * (((q.out : K) : G)⁻¹ * x) ∈ K` using `K.mul_mem (q.out).2 (hle hq)`. Simplify using `using h1`. Establish `hdisj : Pairwise (Function.onFun Disjoint S)`. Introduce `q q' hqq'`. Use `Set.disjoint_left.2 fun x hx hx' => hqq' ?_` and prove the remaining obligations.

Rewrite `hx`, `hx'` using `[hS, Set.mem_preimage]`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Establish `h2 : ((q.out : K) : G)⁻¹ * ((q'.out : K) : G) = (((q.out : K) : G)⁻¹ * x) * (((q'.out : K) : G)⁻¹ * x)⁻¹` using `by group`. Rewrite using `[h2]`.

Conclude with `K'.mul_mem hx (K'.inv_mem hx')`. Establish `hmeas : ∀ q, MeasurableSet (S q)` using `fun q => (hK'.preimage (continuous_const.mul continuous_id)).measurableSet`. Rewrite using `[hunion, MeasureTheory.measure_iUnion hdisj hmeas, tsum_fintype]`. Establish `hS' : ∀ q, μ (S q) = μ K'` using `fun q => MeasureTheory.measure_preimage_mul μ _ _`. Simplify using `only [hS', Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`.
-/
private theorem haar_subgroup_eq_index_mul_of_open_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant]
    (K K' : Subgroup G) (hle : K' ≤ K) (hK' : IsOpen (K' : Set G)) [Finite (K ⧸ K'.subgroupOf K)] :
    μ K = (Nat.card (K ⧸ K'.subgroupOf K) : ENNReal) * μ K' := by
  classical
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  set S : K ⧸ K'.subgroupOf K → Set G := fun q => (fun h => ((q.out : K) : G)⁻¹ * h) ⁻¹' (K' : Set G) with hS
  have hunion : (K : Set G) = ⋃ q, S q := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.2 ⟨QuotientGroup.mk (⟨x, hx⟩ : K), ?_⟩
      have e := QuotientGroup.out_eq' (QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ K'.subgroupOf K)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
      rw [hS, Set.mem_preimage]
      exact e
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
      rw [hS, Set.mem_preimage] at hq
      have h1 : ((q.out : K) : G) * (((q.out : K) : G)⁻¹ * x) ∈ K := K.mul_mem (q.out).2 (hle hq)
      simpa using h1
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 fun x hx hx' => hqq' ?_
    rw [hS, Set.mem_preimage] at hx hx'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h2 : ((q.out : K) : G)⁻¹ * ((q'.out : K) : G) =
        (((q.out : K) : G)⁻¹ * x) * (((q'.out : K) : G)⁻¹ * x)⁻¹ := by group
    rw [h2]
    exact K'.mul_mem hx (K'.inv_mem hx')
  have hmeas : ∀ q, MeasurableSet (S q) := fun q => (hK'.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hunion, MeasureTheory.measure_iUnion hdisj hmeas, tsum_fintype]
  have hS' : ∀ q, μ (S q) = μ K' := fun q => MeasureTheory.measure_preimage_mul μ _ _
  simp only [hS', Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ K K' hle hK' hK`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Use `haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen (K'.subgroupOf K) (hK'.preimage continuous_subtype_val)`. Rewrite using `[haar_subgroup_eq_index_mul_of_open_le μ K K' hle hK']`. Establish `hpos : μ K' ≠ 0` using `(hK'.measure_pos μ ⟨1, K'.one_mem⟩).ne'`.

Establish `hfin : μ K' ≠ ⊤` using `((MeasureTheory.measure_mono (show (K' : Set G) ⊆ K from hle)).trans_lt hK.measure_lt_top).ne`. Rewrite using `[ENNReal.toReal_mul, mul_div_assoc, div_self (ENNReal.toReal_pos hpos hfin).ne', mul_one]`. Simplify using `[Subgroup.relIndex, Subgroup.index]`.
-/
theorem haar_ratio_eq_relIndex : HaarRatio := by
  intro G _ _ _ _ _ μ _ K K' hle hK' hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : Finite (K ⧸ K'.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen (K'.subgroupOf K) (hK'.preimage continuous_subtype_val)
  rw [haar_subgroup_eq_index_mul_of_open_le μ K K' hle hK']
  have hpos : μ K' ≠ 0 := (hK'.measure_pos μ ⟨1, K'.one_mem⟩).ne'
  have hfin : μ K' ≠ ⊤ :=
    ((MeasureTheory.measure_mono (show (K' : Set G) ⊆ K from hle)).trans_lt hK.measure_lt_top).ne
  rw [ENNReal.toReal_mul, mul_div_assoc, div_self (ENNReal.toReal_pos hpos hfin).ne', mul_one]
  simp [Subgroup.relIndex, Subgroup.index]

end PIW.MassDataColumns

open PIW.MassDataColumns in
/- English proof (translation)
Establish `hO : OpenCompactStep` using `openCompactStep_of hE hK2 hKc`. Establish `hG : IdxGroupStep` using `idxGroupStep_of (kfBridgeStep_of_adBridgeK hAK)`. Establish `hU : UnfoldGenStep` using `unfoldGenStep_of MassDataMassesW.massUnfoldGen_holds (hinfCompact_of hAI hInf hHS hHC) MassDataMassesW.fdExistsH_holds MassDataMassesW.volHTie_holds`. Establish `hC : ClassCountStep'` using `classCountStep_of class_sets_equal_card stabilizers_trivial_of_neat hU hG hO`. Establish `hCount : IdxCountStep` using `idxCountStep_of_modelAll (hModelAll_of (hAdaptAll_of adapted_basis_every_place) level_clause_adapted_basis)`.

Introduce `D X hb hK FdN FdN' u u' X0 L A`. Conclude with `massDataColumns_of (colsDimStep_of' hGF hN hF hC) (colsIdxStep_of haar_ratio_eq_relIndex hG (idxTopStep_of hO) hCount) X hb hK FdN FdN' u u' X0 L A`.
-/
theorem massDataColumns_of' (hAI : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeIso I)
    (hGF : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I)
    (hAK : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeK I) (hN : NeatKuStep) (hF : ClassFinStep)
    (hE : FinHAHomeo) (hK2 : LevelOpenCompact) (hKc : KsetCompactAll) (hInf : InfHAHomeo) (hHS : HStepInf)
    (hHC : HinfCompactBundle) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X)) (A : Formalism.L2.SG.TypedSets.AnIn),
      Formalism.L2.SG.TypedSets.InColumnsAt X hb hK FdN FdN' u u' X0 L A := by
  have hO : OpenCompactStep := openCompactStep_of hE hK2 hKc
  have hG : IdxGroupStep := idxGroupStep_of (kfBridgeStep_of_adBridgeK hAK)
  have hU : UnfoldGenStep :=
    unfoldGenStep_of MassDataMassesW.massUnfoldGen_holds (hinfCompact_of hAI hInf hHS hHC)
      MassDataMassesW.fdExistsH_holds MassDataMassesW.volHTie_holds
  have hC : ClassCountStep' := classCountStep_of class_sets_equal_card stabilizers_trivial_of_neat hU hG hO
  have hCount : IdxCountStep :=
    idxCountStep_of_modelAll (hModelAll_of (hAdaptAll_of adapted_basis_every_place) level_clause_adapted_basis)
  intro D X hb hK FdN FdN' u u' X0 L A
  exact massDataColumns_of (colsDimStep_of' hGF hN hF hC)
    (colsIdxStep_of haar_ratio_eq_relIndex hG (idxTopStep_of hO) hCount) X hb hK FdN FdN' u u' X0 L A
