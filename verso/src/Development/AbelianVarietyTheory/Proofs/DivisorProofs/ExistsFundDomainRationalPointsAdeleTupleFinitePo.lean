import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatVecDomain

/- English proof (translation)
Take `⟨U, hU, hx⟩` from `GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F`. Establish `hN : (Set.univ.pi fun _ : κ => U) ∈ nhds (0 : κ → AdeleRing (𝓞 F) F)` using `set_pi_mem_nhds Set.finite_univ fun _ _ => hU`. Use `discreteTopology_of_isOpen_singleton_zero ?_` and prove the remaining obligations. Rewrite using `[isOpen_singleton_iff_nhds_eq_pure]`. Use `le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)` and prove the remaining obligations.

Establish `hc : ContinuousAt (fun x : GlobalTheory.ThetaParseval.ratVec F κ => (x : κ → AdeleRing (𝓞 F) F)) 0` using `continuous_subtype_val.continuousAt`. Use `Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩ hyU`. Take `⟨ξ, rfl⟩` from `(GlobalTheory.ThetaParseval.mem_ratVec_iff y).1 hy`. Establish `hξ : ξ = 0` using `funext fun i => hx _ (hyU i (Set.mem_univ i))`.

Substitute `hξ` using the available equality. Use `Subtype.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem discrete_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    DiscreteTopology (GlobalTheory.ThetaParseval.ratVec F κ) := by
  obtain ⟨U, hU, hx⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hN : (Set.univ.pi fun _ : κ => U) ∈ nhds (0 : κ → AdeleRing (𝓞 F) F) :=
    set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
  have hc : ContinuousAt (fun x : GlobalTheory.ThetaParseval.ratVec F κ => (x : κ → AdeleRing (𝓞 F) F)) 0 :=
    continuous_subtype_val.continuousAt
  refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
  rintro ⟨y, hy⟩ hyU
  obtain ⟨ξ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y).1 hy
  have hξ : ξ = 0 := funext fun i => hx _ (hyU i (Set.mem_univ i))
  subst hξ
  refine Subtype.ext ?_
  funext i
  simp

/- English proof (translation)
Take `⟨K, hK, hx⟩` from `GlobalTheory.AdeleCocompact.exists_compact_adele F`. Use `choose c hc using hx`. Use `⟨Set.univ.pi fun _ : κ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩` and prove the remaining obligations. Use `⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (-c (x i)), (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨fun i => -c (x i), rfl⟩, fun i _ => ?_⟩` and prove the remaining obligations. Use `hc (x i)` as an intermediate fact.

Simplify `this` using `[map_neg, neg_add_eq_sub]`.
-/
theorem exists_compact_cover_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ K : Set (κ → AdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x, ∃ γ ∈ GlobalTheory.ThetaParseval.ratVec F κ, γ + x ∈ K := by
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  choose c hc using hx
  refine ⟨Set.univ.pi fun _ : κ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  refine ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (-c (x i)),
    (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨fun i => -c (x i), rfl⟩, fun i _ => ?_⟩
  have := hc (x i)
  simpa [map_neg, neg_add_eq_sub] using this

/- English proof (translation)
Introduce `F _ _ κ _ μ hμ`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _`.

Use `haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩`. Use `haveI := discrete_ratVec F κ`. Use `haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := GlobalTheory.countable_of_discrete_addSubgroup _`. Take `⟨K, hK, hcov⟩` from `exists_compact_cover_ratVec F κ`. Take `⟨D, -, -, hD⟩` from `GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (GlobalTheory.ThetaParseval.ratVec F κ)`.

Conclude with `⟨D, hD μ, (hD μ).measure_ne_zero (NeZero.ne μ), (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov μ (hD μ)).ne⟩`.
-/
theorem exists_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ 𝓕₁ : Set (κ → AF F), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ ∧ μ 𝓕₁ ≠ 0 ∧ μ 𝓕₁ ≠ ⊤ := by
  intro F _ _ κ _ μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := discrete_ratVec F κ
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) :=
    GlobalTheory.countable_of_discrete_addSubgroup _
  obtain ⟨K, hK, hcov⟩ := exists_compact_cover_ratVec F κ
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup
    (GlobalTheory.ThetaParseval.ratVec F κ)
  exact ⟨D, hD μ, (hD μ).measure_ne_zero (NeZero.ne μ),
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov μ (hD μ)).ne⟩

end GlobalTheory.RatVecDomain
