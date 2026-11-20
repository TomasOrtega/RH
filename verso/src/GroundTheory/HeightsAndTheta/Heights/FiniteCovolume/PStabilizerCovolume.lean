import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerCovolume
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectCovering
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementForm
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchLatticeDiscrete

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

universe u

/- English proof (translation)
Establish `: (A.subgroupOf B).FiniteIndex` using `⟨hidx⟩`. Establish `: Finite (B ⧸ A.subgroupOf B)` using `Subgroup.finite_quotient_of_finiteIndex`. Set `` to `Fintype.ofFinite (B ⧸ A.subgroupOf B)`. Use `set bad := {l : G | ¬ ∃ γ : B.map f, γ • l ∈ FD} with hbad_def`. Establish `hbad : μ bad = 0` using `measure_eq_zero_iff_ae_notMem.2 (hFD.ae_covers.mono fun x hx hx' => hx' hx)`.

Use `⟨(⋃ k : B ⧸ A.subgroupOf B, (fun x => f ((Quotient.out k : B) : K) * x) ⁻¹' toMeasurable μ FD) ∪ toMeasurable μ bad, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(MeasurableSet.iUnion fun k => (measurableSet_toMeasurable μ FD).preimage (measurable_const_mul _)).union (measurableSet_toMeasurable μ bad)`. Use `lt_of_le_of_lt (measure_union_le _ _) ?_` and prove the remaining obligations. Rewrite using `[measure_toMeasurable, hbad, add_zero]`. Use `lt_of_le_of_lt (measure_iUnion_fintype_le μ _) ?_` and prove the remaining obligations.

Simplify using `only [measure_preimage_mul, measure_toMeasurable]`. Conclude with `ENNReal.sum_lt_top.2 fun _ _ => hfin`. Introduce `l`. Distinguish the cases in `hl : l ∈ bad`. Conclude with `⟨1, one_mem _, Or.inr (subset_toMeasurable μ bad (by simpa using hl))⟩`.

Rewrite `hl` using `[hbad_def, Set.mem_ofPred_eq, not_not]`. Take `⟨⟨γ, hγ⟩, hγl⟩` from `hl`. Take `⟨b, hb, rfl⟩` from `Subgroup.mem_map.1 hγ`. Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)`. Use `set k : B ⧸ A.subgroupOf B := QuotientGroup.mk (⟨b, hb⟩ : B)`.

Establish `hcA : (((c : B) : K)) ∈ A` using `c.2`. Use `⟨((c : B) : K)⁻¹, inv_mem hcA, Or.inl (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩` and prove the remaining obligations. Apply `subset_toMeasurable` to reduce the goal to its premises. Establish `e : ((Quotient.out k : B) : K) = b * ((c : B) : K)`. Rewrite using `[hc]`.

Both sides reduce to the same expression. Simplify using `only [e, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]`. Simplify `hγl` using `[Subgroup.smul_def]`.
-/
theorem exists_covering_of_relIndex_ne_zero {G K : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [Group K] (μ : Measure G) [μ.IsMulLeftInvariant] (f : K →* G)
    (A B : Subgroup K) (hidx : A.relIndex B ≠ 0) (FD : Set G)
    (hFD : IsFundamentalDomain (B.map f) FD μ) (hfin : μ FD < ⊤) :
    ∃ T : Set G, MeasurableSet T ∧ μ T < ⊤ ∧ ∀ l, ∃ a ∈ A, f a * l ∈ T := by
  classical
  have : (A.subgroupOf B).FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (B ⧸ A.subgroupOf B)
  set bad := {l : G | ¬ ∃ γ : B.map f, γ • l ∈ FD} with hbad_def
  have hbad : μ bad = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hFD.ae_covers.mono fun x hx hx' => hx' hx)
  refine ⟨(⋃ k : B ⧸ A.subgroupOf B, (fun x => f ((Quotient.out k : B) : K) * x) ⁻¹'
    toMeasurable μ FD) ∪ toMeasurable μ bad, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun k => (measurableSet_toMeasurable μ FD).preimage
      (measurable_const_mul _)).union (measurableSet_toMeasurable μ bad)
  · refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [measure_toMeasurable, hbad, add_zero]
    refine lt_of_le_of_lt (measure_iUnion_fintype_le μ _) ?_
    simp only [measure_preimage_mul, measure_toMeasurable]
    exact ENNReal.sum_lt_top.2 fun _ _ => hfin
  · intro l
    by_cases hl : l ∈ bad
    · exact ⟨1, one_mem _, Or.inr (subset_toMeasurable μ bad (by simpa using hl))⟩
    · rw [hbad_def, Set.mem_ofPred_eq, not_not] at hl
      obtain ⟨⟨γ, hγ⟩, hγl⟩ := hl
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hγ
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
      set k : B ⧸ A.subgroupOf B := QuotientGroup.mk (⟨b, hb⟩ : B)
      have hcA : (((c : B) : K)) ∈ A := c.2
      refine ⟨((c : B) : K)⁻¹, inv_mem hcA, Or.inl (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      apply subset_toMeasurable
      have e : ((Quotient.out k : B) : K) = b * ((c : B) : K) := by
        rw [hc]; rfl
      simp only [e, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      simpa [Subgroup.smul_def] using hγl

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `D La x₀ hLa hx₀ hne hiso ν hν`. Take `⟨w₀, hxw, hww⟩` from `WittPartner.proof h x₀ hne hiso`. Establish `hp : IsHyperbolicPair h x₀ w₀` using `⟨hiso, hww, hxw⟩`. Take `⟨h', hh'⟩` from `ComplementForm.proof h x₀ w₀ hp`. Set `v'` to `Module.finBasis E (hypComplement h x₀ w₀)`.

Establish `hlt : finrank E (hypComplement h x₀ w₀) < finrank E W`. Use `Submodule.finrank_lt fun htop => ?_` and prove the remaining obligations. Establish `hmem : w₀ ∈ hypComplement h x₀ w₀` using `htop ▸ Submodule.mem_top`. Rewrite `hmem` using `[mem_hypComplement, hxw]`. Conclude with `one_ne_zero hmem.1`.

Take `⟨i, q, hi, hq, hqi, hker, hiw, hcompat⟩` from `h₃ x₀ w₀ hp h' hh' _ v'`. Take `⟨D', La', G'', hLa', hG'', hidx, hlift⟩` from `h₆ D La x₀ w₀ hLa hx₀ hp h' hh'`. Set `μL : Measure (archUnitary h' v')` to `Measure.haar`. Take `⟨FD', hFD', hFD'fin⟩` from `h₁ (hypComplement h x₀ w₀) h' _ v' hlt μL D' La' hLa'`. Take `⟨T, hTm, hTfin, hT⟩` from `exists_covering_of_relIndex_ne_zero μL (archEmbed h' v') G'' (latticeStab h' La') hidx FD' hFD' hFD'fin`.

Use `set Γ := (vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀) with hΓ`. Establish `hcovL : ∀ l, ∃ γ ∈ Γ, q γ * l ∈ T`. Introduce `l`. Take `⟨m, hm, hml⟩` from `hT l`. Take `⟨γ₀, hγx, hγw, hγm⟩` from `ComplementExtension.proof h x₀ w₀ hp h' hh' m`.

Establish `hγ₀ : γ₀ ∈ latticeStab h La` using `hlift m hm γ₀ hγx hγw hγm`. Use `⟨i (archEmbed h' v' m), ?_, by rw [hqi]; exact hml⟩` and prove the remaining obligations. Rewrite using `[hΓ, Subgroup.mem_subgroupOf, hcompat γ₀ m hγx hγw hγm]`. Conclude with `⟨⟨γ₀, hγ₀⟩, hγx, rfl⟩`. Take `⟨C, hC, hcovN⟩` from `h₅ D La x₀ hLa hx₀ hne hiso`.

Set `j : unipRadical h v x₀ →* vecFixGroup h v x₀` to `Subgroup.inclusion (unipRadical_le_vecFixGroup h v x₀)`. Establish `hjc : Continuous j` using `(continuous_subtype_val.subtype_mk _)`. Establish `hj : IsClosedEmbedding j`. Use `⟨IsEmbedding.of_comp hjc continuous_subtype_val IsEmbedding.subtypeVal, ?_⟩` and prove the remaining obligations. Establish `: Set.range j = Subtype.val ⁻¹' (unipRadical h v x₀ : Set (archUnitary h v))`.

Use extensionality with `g`. Conclude with `⟨by rintro ⟨n, rfl⟩; exact n.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩`. Rewrite using `[this]`. Conclude with `(isClosed_unipRadical h v x₀).preimage continuous_subtype_val`. Establish `hjr : ∀ g, q g = 1 ↔ g ∈ j.range` using `fun g => (hker g).trans ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩`.

Set `μN : Measure (unipRadical h v x₀)` to `Measure.haar`. Establish `hemb : MeasurableEmbedding (Subtype.val : vecFixGroup h v x₀ → archUnitary h v)` using `(isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.measurableEmbedding`. Establish `hconj : ∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j`. Introduce `l`. Establish `key` using `h₄ x₀ w₀ hp μN ((i l : vecFixGroup h v x₀) : archUnitary h v) ⟨(i l).2, hiw l⟩`.

Establish `hf : Continuous fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹` using `(continuous_const.mul hjc).mul continuous_const`. Rewrite using `[← hemb.comap_map (μN.map _), ← hemb.comap_map (μN.map j), Measure.map_map hemb.measurable hf.measurable, Measure.map_map hemb.measurable hjc.measurable]`. Establish `e1 : (Subtype.val ∘ fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹) = fun n : unipRadical h v x₀ => ((i l : vecFixGroup h v x₀) : archUnitary h v) * (n : archUnitary h v) * ((i l : vecFixGroup h v x₀) : archUnitary h v)⁻¹`. Use function extensionality and compare the values at `n`. Simplify using `[j]`.

Establish `e2 : (Subtype.val ∘ j) = (Subtype.val : unipRadical h v x₀ → archUnitary h v)`. Use function extensionality and compare the values at `n`. Both sides reduce to the same expression. Rewrite using `[e1, e2, key]`. Establish `hcovN' : ∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C` using `fun n => by`.

Take `⟨δ, hδ, hδn⟩` from `hcovN n`. Conclude with `⟨δ, hδ, hδn⟩`. Take `⟨S, -, hSfin, hScov⟩` from `h₂ x₀ w₀ h' _ v' i q j hi hq hj hqi hjr μL μN hconj Γ C T hC hTm hTfin hcovN' hcovL ν`. Establish `hdG : DiscreteTopology (vecStabGroup h v La x₀)`. Use `ArchLatticeDiscrete.proof h v La hLa.isLattice` as an intermediate fact.

Establish `hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La`. Introduce and unpack `_ ⟨γ, -, rfl⟩`. Conclude with `⟨(γ : h.unitaryGroup), γ.2, rfl⟩`. Conclude with `DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle) (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)`. Establish `hdisc : DiscreteTopology Γ` using `DiscreteTopology.of_continuous_injective (f := fun x : Γ => (⟨((x : vecFixGroup h v x₀) : archUnitary h v), x.2⟩ : vecStabGroup h v La x₀)) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtyp …`.

Establish `: Countable Γ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Take `⟨FD, -, hFD⟩` from `DiscreteFundamentalDomain.proof (vecFixGroup h v x₀) ν Γ hdisc`. Establish `hle : ν FD ≤ ν S`. Rewrite using `[hFD.measure_eq_tsum S]`. Use `(measure_mono fun x hx => ?_).trans (measure_iUnion_le _)` and prove the remaining obligations.

Take `⟨γ, hγ, hγx⟩` from `hScov x`. Use `Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩` and prove the remaining obligations. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv]`. Conclude with `hγx`. Establish `hν0 : ν ≠ 0` using `fun h0 => (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) (by simp [h0])`.

Conclude with `⟨FD, hFD, pos_iff_ne_zero.2 (hFD.measure_ne_zero hν0), hle.trans_lt hSfin⟩`.
-/
theorem StabilizerCovolumeFinite.proof [FiniteDimensional E W] (h : HermitianForm F E W)
    (v : Basis ι E W) (h₁ : CovolumeFiniteBelow.{u} F E (finrank E W))
    (h₂ : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (h₃ : StabilizerLevi.Statement h v) (h₄ : UnipotentModulus.Statement h v)
    (h₅ : UnipotentCocompact.Statement h v) (h₆ : CongruenceLift.Statement h) :
    StabilizerCovolumeFinite.Statement h v := by
  classical
  intro D La x₀ hLa hx₀ hne hiso ν hν

  obtain ⟨w₀, hxw, hww⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨h', hh'⟩ := ComplementForm.proof h x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  have hlt : finrank E (hypComplement h x₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hmem : w₀ ∈ hypComplement h x₀ w₀ := htop ▸ Submodule.mem_top
    rw [mem_hypComplement, hxw] at hmem
    exact one_ne_zero hmem.1

  obtain ⟨i, q, hi, hq, hqi, hker, hiw, hcompat⟩ := h₃ x₀ w₀ hp h' hh' _ v'

  obtain ⟨D', La', G'', hLa', hG'', hidx, hlift⟩ := h₆ D La x₀ w₀ hLa hx₀ hp h' hh'
  let μL : Measure (archUnitary h' v') := Measure.haar
  obtain ⟨FD', hFD', hFD'fin⟩ :=
    h₁ (hypComplement h x₀ w₀) h' _ v' hlt μL D' La' hLa'
  obtain ⟨T, hTm, hTfin, hT⟩ := exists_covering_of_relIndex_ne_zero μL (archEmbed h' v') G''
    (latticeStab h' La') hidx FD' hFD' hFD'fin
  set Γ := (vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀) with hΓ
  have hcovL : ∀ l, ∃ γ ∈ Γ, q γ * l ∈ T := by
    intro l
    obtain ⟨m, hm, hml⟩ := hT l
    obtain ⟨γ₀, hγx, hγw, hγm⟩ := ComplementExtension.proof h x₀ w₀ hp h' hh' m
    have hγ₀ : γ₀ ∈ latticeStab h La := hlift m hm γ₀ hγx hγw hγm
    refine ⟨i (archEmbed h' v' m), ?_, by rw [hqi]; exact hml⟩
    rw [hΓ, Subgroup.mem_subgroupOf, hcompat γ₀ m hγx hγw hγm]
    exact ⟨⟨γ₀, hγ₀⟩, hγx, rfl⟩

  obtain ⟨C, hC, hcovN⟩ := h₅ D La x₀ hLa hx₀ hne hiso
  let j : unipRadical h v x₀ →* vecFixGroup h v x₀ :=
    Subgroup.inclusion (unipRadical_le_vecFixGroup h v x₀)
  have hjc : Continuous j := (continuous_subtype_val.subtype_mk _)
  have hj : IsClosedEmbedding j := by
    refine ⟨IsEmbedding.of_comp hjc continuous_subtype_val IsEmbedding.subtypeVal, ?_⟩
    have : Set.range j = Subtype.val ⁻¹' (unipRadical h v x₀ : Set (archUnitary h v)) := by
      ext g
      exact ⟨by rintro ⟨n, rfl⟩; exact n.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    rw [this]
    exact (isClosed_unipRadical h v x₀).preimage continuous_subtype_val
  have hjr : ∀ g, q g = 1 ↔ g ∈ j.range := fun g => (hker g).trans
    ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩
  let μN : Measure (unipRadical h v x₀) := Measure.haar
  have hemb : MeasurableEmbedding (Subtype.val : vecFixGroup h v x₀ → archUnitary h v) :=
    (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.measurableEmbedding
  have hconj : ∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j := by
    intro l
    have key := h₄ x₀ w₀ hp μN ((i l : vecFixGroup h v x₀) : archUnitary h v) ⟨(i l).2, hiw l⟩
    have hf : Continuous fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹ :=
      (continuous_const.mul hjc).mul continuous_const
    rw [← hemb.comap_map (μN.map _), ← hemb.comap_map (μN.map j),
      Measure.map_map hemb.measurable hf.measurable,
      Measure.map_map hemb.measurable hjc.measurable]
    have e1 : (Subtype.val ∘ fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹) =
        fun n : unipRadical h v x₀ =>
          ((i l : vecFixGroup h v x₀) : archUnitary h v) * (n : archUnitary h v) *
            ((i l : vecFixGroup h v x₀) : archUnitary h v)⁻¹ := by
      funext n
      simp [j]
    have e2 : (Subtype.val ∘ j) = (Subtype.val : unipRadical h v x₀ → archUnitary h v) := by
      funext n
      rfl
    rw [e1, e2, key]
  have hcovN' : ∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C := fun n => by
    obtain ⟨δ, hδ, hδn⟩ := hcovN n
    exact ⟨δ, hδ, hδn⟩

  obtain ⟨S, -, hSfin, hScov⟩ :=
    h₂ x₀ w₀ h' _ v' i q j hi hq hj hqi hjr μL μN hconj Γ C T hC hTm hTfin hcovN' hcovL ν

  have hdG : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨((x : vecFixGroup h v x₀) : archUnitary h v), x.2⟩ :
        vecStabGroup h v La x₀))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨FD, -, hFD⟩ := DiscreteFundamentalDomain.proof (vecFixGroup h v x₀) ν Γ hdisc

  have hle : ν FD ≤ ν S := by
    rw [hFD.measure_eq_tsum S]
    refine (measure_mono fun x hx => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, hγx⟩ := hScov x
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγx
  have hν0 : ν ≠ 0 := fun h0 => (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) (by simp [h0])
  exact ⟨FD, hFD, pos_iff_ne_zero.2 (hFD.measure_ne_zero hν0), hle.trans_lt hSfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
