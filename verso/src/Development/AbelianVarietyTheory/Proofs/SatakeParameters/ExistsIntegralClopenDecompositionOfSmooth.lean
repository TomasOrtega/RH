import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

/- English proof (translation)
The claim follows from `hdom x C = closure {Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))} := by haveI := hdom x set ξ := Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x))) have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC have hgen : IsGenericPoint hC.1.generi …`.
-/
theorem irreducibleComponent_eq_closure (Z : Scheme.{0})
    (hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) {C : Set Z} (hC : C ∈ irreducibleComponents Z)
    {x : Z} (hx : x ∈ C) :
    haveI := hdom x
    C = closure {Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))} := by
  haveI := hdom x
  set ξ := Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hgen : IsGenericPoint hC.1.genericPoint C := by
    simpa [hCc.closure_eq] using hC.1.isGenericPoint_genericPoint_closure
  have hηx : hC.1.genericPoint ⤳ x := hgen.specializes hx
  have hmem : hC.1.genericPoint ∈ Set.range (Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hηx
  obtain ⟨p, hp⟩ := hmem
  have hξη : ξ ⤳ hC.1.genericPoint := by
    rw [← hp]
    exact ((genericPoint_spec (Spec (Z.presheaf.stalk x))).specializes trivial).map
      (Z.fromSpecStalk x).continuous
  have hsub : C ⊆ closure {ξ} := by
    rw [← hgen.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hξη) isClosed_closure
  have hirr : IsIrreducible (closure {ξ}) := isIrreducible_singleton.closure
  exact le_antisymm hsub (hC.2 hirr hsub)

end GlobalTheory.SmoothComponents

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

/- English proof (translation)
Introduce `Z s d _ _`. Establish `hs : Smooth s` using `SmoothOfRelativeDimension.smooth d s`. Take `⟨hred, -, hln⟩` from `isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Z s hs`. Establish `hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x)` using `fun x ↦ (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s (isDomain_and_isIntegrallyClosed_stalk_Sp ℂ) x).1`. Use `haveI : IsNoetherian Z := ⟨⟩`.

Establish `hfin : (irreducibleComponents Z).Finite` using `finite_irreducibleComponents_of_isNoetherian`. Establish `disj : ∀ C ∈ irreducibleComponents Z, ∀ D ∈ irreducibleComponents Z, C ≠ D → Disjoint C D`. Introduce `C hC D hD hne`. Rewrite using `[Set.disjoint_left]`. Introduce `x hxC hxD`.

Conclude with `hne ((irreducibleComponent_eq_closure Z hdom hC hxC).trans (irreducibleComponent_eq_closure Z hdom hD hxD).symm)`. Establish `cover : ∀ x : Z, ∃ C ∈ irreducibleComponents Z, x ∈ C` using `fun x ↦ ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, mem_irreducibleComponent⟩`. Establish `hopen : ∀ C ∈ irreducibleComponents Z, IsOpen C`. Introduce `C hC`. Establish `hc : Cᶜ = ⋃ D ∈ irreducibleComponents Z \ {C}, D`.

Use extensionality with `x`. Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨D, hD, hxD⟩` from `cover x`.

Conclude with `⟨D, ⟨hD, fun h ↦ hx (h ▸ hxD)⟩, hxD⟩`. Introduce and unpack `⟨D, ⟨hD, hne⟩, hxD⟩ hxC`. Conclude with `Set.disjoint_left.mp (disj D hD C hC hne) hxD hxC`. Rewrite using `[← isClosed_compl_iff, hc]`. Conclude with `(hfin.subset Set.diff_subset).isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1`.

Use `letI : Fintype (irreducibleComponents Z) := hfin.fintype`. Use `⟨irreducibleComponents Z, inferInstance, fun C ↦ ⟨C.1, hopen C.1 C.2⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Apply `Opens.ext` to reduce the goal to its premises. Simplify using `only [Opens.coe_inf, Opens.coe_bot]`.

Conclude with `Set.disjoint_iff_inter_eq_empty.mp (disj i.1 i.2 j.1 j.2 fun h ↦ hij (Subtype.ext h))`. Use `eq_top_iff.mpr fun x _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Opens.mem_iSup]`. Take `⟨C, hC, hxC⟩` from `cover x`. Conclude with `⟨⟨C, hC⟩, hxC⟩`.

Introduce `C`. Establish `hirr : IsIrreducible C.1` using `C.2.1`. Use `haveI : IrreducibleSpace (C.1 : Set Z) := Subtype.irreducibleSpace hirr`. Set `U : Z.Opens` to `⟨C.1, hopen C.1 C.2⟩`. Express the relevant statement in the definitionally equal form `IsIntegral U.toScheme`.

Use `haveI : IrreducibleSpace U.toScheme := this`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced _`.
-/
theorem main : ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]
    [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens),
      (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  intro Z s d _ _
  have hs : Smooth s := SmoothOfRelativeDimension.smooth d s
  obtain ⟨hred, -, hln⟩ :=
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Z s hs
  have hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x ↦
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (isDomain_and_isIntegrallyClosed_stalk_Sp ℂ) x).1
  haveI : IsNoetherian Z := ⟨⟩
  have hfin : (irreducibleComponents Z).Finite := finite_irreducibleComponents_of_isNoetherian
  have disj : ∀ C ∈ irreducibleComponents Z, ∀ D ∈ irreducibleComponents Z, C ≠ D →
      Disjoint C D := by
    intro C hC D hD hne
    rw [Set.disjoint_left]
    intro x hxC hxD
    exact hne ((irreducibleComponent_eq_closure Z hdom hC hxC).trans
      (irreducibleComponent_eq_closure Z hdom hD hxD).symm)
  have cover : ∀ x : Z, ∃ C ∈ irreducibleComponents Z, x ∈ C := fun x ↦
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      mem_irreducibleComponent⟩
  have hopen : ∀ C ∈ irreducibleComponents Z, IsOpen C := by
    intro C hC
    have hc : Cᶜ = ⋃ D ∈ irreducibleComponents Z \ {C}, D := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro hx
        obtain ⟨D, hD, hxD⟩ := cover x
        exact ⟨D, ⟨hD, fun h ↦ hx (h ▸ hxD)⟩, hxD⟩
      · rintro ⟨D, ⟨hD, hne⟩, hxD⟩ hxC
        exact Set.disjoint_left.mp (disj D hD C hC hne) hxD hxC
    rw [← isClosed_compl_iff, hc]
    exact (hfin.subset Set.diff_subset).isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1
  letI : Fintype (irreducibleComponents Z) := hfin.fintype
  refine ⟨irreducibleComponents Z, inferInstance, fun C ↦ ⟨C.1, hopen C.1 C.2⟩, ?_, ?_, ?_⟩
  · intro i j hij
    apply Opens.ext
    simp only [Opens.coe_inf, Opens.coe_bot]
    exact Set.disjoint_iff_inter_eq_empty.mp (disj i.1 i.2 j.1 j.2 fun h ↦ hij (Subtype.ext h))
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    rw [Opens.mem_iSup]
    obtain ⟨C, hC, hxC⟩ := cover x
    exact ⟨⟨C, hC⟩, hxC⟩
  · intro C
    have hirr : IsIrreducible C.1 := C.2.1
    haveI : IrreducibleSpace (C.1 : Set Z) := Subtype.irreducibleSpace hirr
    let U : Z.Opens := ⟨C.1, hopen C.1 C.2⟩
    change IsIntegral U.toScheme
    haveI : IrreducibleSpace U.toScheme := this
    exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.SmoothComponents
