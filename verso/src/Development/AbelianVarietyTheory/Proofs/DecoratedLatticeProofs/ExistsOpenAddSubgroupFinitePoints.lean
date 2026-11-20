import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

namespace GlobalTheory.FinSubgroup

/- English proof (translation)
Introduce `D V hV`. Take `⟨e, he, hc, hcs⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Use `letI : TopologicalSpace (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := moduleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)`. Use `letI : TopologicalSpace (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) := moduleTopology (InfiniteAdeleRing D.host.F) (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E)`. Establish `h0 : e.symm 0 = 0` using `map_zero _`.

Establish `hV' : (e.symm : _ → AE D) ⁻¹' V ∈ 𝓝 ((0 : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E), (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))`. Apply `hcs.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Establish `: (e.symm : _ → AE D) (0, 0) = 0` using `h0`. Rewrite using `[this]`. Conclude with `hV`.

Take `⟨A, hA, B, hB, hAB⟩` from `mem_nhds_prod_iff.1 hV'`. Take `⟨N, hN, hNB⟩` from `(GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (Subsingleton.elim _ _)).2 B hB`. Set `W : AddSubgroup (GlobalTheory.AdLat.RA D.host.F D.host.E)` to `(GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))).map (nsmulAddMonoidHom N)`. Establish `hW : IsOpen (W : Set (GlobalTheory.AdLat.RA D.host.F D.host.E))`. Use `GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using `only [W, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, nsmulAddMonoidHom_apply, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨y, hy, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Set `f : AE D →+ GlobalTheory.AdLat.RA D.host.F D.host.E` to `(AddMonoidHom.snd _ _).comp e.toAddMonoidHom`. Establish `hf : Continuous f` using `continuous_snd.comp hc`.

Use `⟨W.comap f, hW.preimage hf, fun a ha hinf => ?_⟩` and prove the remaining obligations. Establish `h1 : (e a).1 = 0` using `by rw [(he a).1]; exact hinf`. Establish `h2 : (e a).2 ∈ B`. Take `⟨y, hy, hya⟩` from `AddSubgroup.mem_map.1 (AddSubgroup.mem_comap.1 ha)`. Establish `: f a = (e a).2` using `rfl`.

Rewrite using `[← this, ← hya]`. Conclude with `hNB y hy`. Establish `h3 : e a ∈ A ×ˢ B` using `⟨by rw [h1]; exact mem_of_mem_nhds hA, h2⟩`. Use `hAB h3` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_openAddSubgroup_finite_points :
    ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) →
      ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  intro D V hV
  obtain ⟨e, he, hc, hcs⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)
  letI : TopologicalSpace (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (InfiniteAdeleRing D.host.F) (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E)
  have h0 : e.symm 0 = 0 := map_zero _
  have hV' : (e.symm : _ → AE D) ⁻¹' V ∈ 𝓝 ((0 : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E),
      (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) := by
    apply hcs.continuousAt.preimage_mem_nhds
    have : (e.symm : _ → AE D) (0, 0) = 0 := h0
    rw [this]
    exact hV
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hV'
  obtain ⟨N, hN, hNB⟩ := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (Subsingleton.elim _ _)).2 B hB
  let W : AddSubgroup (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    (GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))).map (nsmulAddMonoidHom N)
  have hW : IsOpen (W : Set (GlobalTheory.AdLat.RA D.host.F D.host.E)) := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    convert this using 1
    ext z
    simp only [W, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, nsmulAddMonoidHom_apply, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  let f : AE D →+ GlobalTheory.AdLat.RA D.host.F D.host.E := (AddMonoidHom.snd _ _).comp e.toAddMonoidHom
  have hf : Continuous f := continuous_snd.comp hc
  refine ⟨W.comap f, hW.preimage hf, fun a ha hinf => ?_⟩
  have h1 : (e a).1 = 0 := by rw [(he a).1]; exact hinf
  have h2 : (e a).2 ∈ B := by
    obtain ⟨y, hy, hya⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_comap.1 ha)
    have : f a = (e a).2 := rfl
    rw [← this, ← hya]
    exact hNB y hy
  have h3 : e a ∈ A ×ˢ B := ⟨by rw [h1]; exact mem_of_mem_nhds hA, h2⟩
  have := hAB h3
  simpa using this

end GlobalTheory.FinSubgroup
