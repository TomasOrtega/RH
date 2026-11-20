import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.AdelicMatrixLatticeF

/- English proof (translation)
Introduce `F E _ _ _ _ _ nS nT`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `: LocallyCompactSpace (AF F)` using `GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _`. Establish `: SecondCountableTopology (AF F)` using `GlobalTheory.AdelicUnitaryTop.secondCountable_adele _`. Establish `: T2Space (AF F)` using `GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _`.

Establish `: IsModuleTopology (AF F) (AEF F E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AEF F E)` using `IsModuleTopology.isTopologicalRing (AF F) _`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Establish `: LocallyCompactSpace (AEF F E)` using `e.isClosedEmbedding.locallyCompactSpace`. Establish `: SecondCountableTopology (AEF F E)` using `e.secondCountableTopology`.

Establish `: T2Space (AEF F E)` using `e.isEmbedding.t2Space`. Establish `hg : IsTopologicalAddGroup (WOF F E nS nT)` using `inferInstanceAs (IsTopologicalAddGroup (Fin nT → Fin nS → AEF F E))`. Use `⟨hg, inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AEF F E)), inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AEF F E)), inferInstanceAs (T2Space (Fin nT → Fin nS → AEF F E)), ?_, ?_⟩` and prove the remaining obligations. Take `⟨U, hU, hx⟩` from `GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F) (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)`. Establish `hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈ nhds (0 : WOF F E nS nT)` using `set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU`.

Use `discreteTopology_of_isOpen_singleton_zero ?_` and prove the remaining obligations. Rewrite using `[isOpen_singleton_iff_nhds_eq_pure]`. Use `le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)` and prove the remaining obligations. Establish `hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0` using `continuous_subtype_val.continuousAt`. Use `Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_` and prove the remaining obligations.

Introduce and unpack `⟨_, y, rfl⟩ hy`. Establish `hy0 : y = 0`. Use function extensionality and compare the values at `i j`. Conclude with `hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))`. Substitute `hy0` using the available equality.

Conclude with `Subtype.ext (map_zero _)`. Take `⟨K, hK, hx⟩` from `GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F) (GlobalTheory.AdeleCocompact.exists_compact_adele F) choose c hc using hx`. Use `⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K, isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩` and prove the remaining obligations. Conclude with `⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩`.
-/
theorem lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  intro F E _ _ _ _ _ nS nT
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  have : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AEF F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AEF F E) := e.secondCountableTopology
  have : T2Space (AEF F E) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WOF F E nS nT) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin nT → Fin nS → AEF F E))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (T2Space (Fin nT → Fin nS → AEF F E)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLatticeF
