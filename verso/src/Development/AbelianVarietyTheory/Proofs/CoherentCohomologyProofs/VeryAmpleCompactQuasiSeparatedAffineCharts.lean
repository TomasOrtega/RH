import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.VeryAmpleCharts

variable {Y : Scheme.{0}} {H : LB Y}

/- English proof (translation)
Introduce `V hV hVo`. Use `isAffineHom_nonzeroLocus_ι hH s` as an intermediate fact. Establish `h` using `(QuasiCompact.isCompact_preimage (f := (nonzeroLocus s).ι) V hVo hV).image (nonzeroLocus s).ι.continuous`. Rewrite `h` using `[Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι]`. Then use the resulting hypothesis.
-/
theorem isRetrocompact_nonzeroLocus (hH : H.IsLB) (s : LB.Sec H) :
    IsRetrocompact (X := Y) (nonzeroLocus s) := by
  intro V hV hVo
  have := isAffineHom_nonzeroLocus_ι hH s
  have h := (QuasiCompact.isCompact_preimage (f := (nonzeroLocus s).ι) V hVo hV).image
    (nonzeroLocus s).ι.continuous
  rwa [Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι] at h

/- English proof (translation)
Proceed by induction on `hI using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => simpa using ha a`. Consider the case `cons a t h _ ih`. Rewrite using `[Finset.cons_eq_insert, Finset.iInf_insert]`. Conclude with `isAffineOpen_nonzeroLocus_inf hH _ ih`.
-/
theorem isAffineOpen_biInf_nonzeroLocus {κ : Type} (hH : H.IsLB) (s : κ → LB.Sec H)
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) (I : Finset κ) (hI : I.Nonempty) :
    IsAffineOpen (⨅ i ∈ I, nonzeroLocus (s i)) := by
  classical
  induction hI using Finset.Nonempty.cons_induction with
  | singleton a => simpa using ha a
  | cons a t h _ ih =>
    rw [Finset.cons_eq_insert, Finset.iInf_insert]
    exact isAffineOpen_nonzeroLocus_inf hH _ ih

/- English proof (translation)
The claim follows from `QuasiSeparatedSpace.of_isOpenCover (U := fun i => nonzeroLocus (s i)) hc (fun i => isRetrocompact_nonzeroLocus hH (s i)) fun i => (ha i).isQuasiSeparated`.
-/
theorem quasiSeparatedSpace_of_cover {κ : Type} (hH : H.IsLB) (s : κ → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    QuasiSeparatedSpace Y :=
  QuasiSeparatedSpace.of_isOpenCover (U := fun i => nonzeroLocus (s i)) hc
    (fun i => isRetrocompact_nonzeroLocus hH (s i)) fun i => (ha i).isQuasiSeparated

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `h` using `isCompact_iUnion fun i => (ha i).isCompact`. Rewrite `h` using `[← TopologicalSpace.Opens.coe_iSup, hc]`. Then use the resulting hypothesis.
-/
theorem compactSpace_of_finite_cover {κ : Type} [Finite κ] (D : κ → Y.Opens)
    (hc : ⨆ i, D i = ⊤) (ha : ∀ i, IsAffineOpen (D i)) : CompactSpace Y := by
  refine ⟨?_⟩
  have h := isCompact_iUnion fun i => (ha i).isCompact
  rwa [← TopologicalSpace.Opens.coe_iSup, hc] at h

/- English proof (translation)
Introduce `_ _ _ _ _ _ s hH hs` and use `⟨compactSpace_of_finite_cover _ hs.1 fun i => (hs.2 i).1, quasiSeparatedSpace_of_cover hH s hs.1 fun i => (hs.2 i).1, isAffineOpen_biInf_nonzeroLocus hH s fun i => (hs.2 i).1⟩`.
-/
theorem compact_quasiSeparated_isAffineOpen : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ ∀ I : Finset (Fin (m + 1)), I.Nonempty → IsAffineOpen (⨅ i ∈ I, nonzeroLocus (s i)) :=
  fun _ _ _ _ _ _ s hH hs =>
    ⟨compactSpace_of_finite_cover _ hs.1 fun i => (hs.2 i).1,
      quasiSeparatedSpace_of_cover hH s hs.1 fun i => (hs.2 i).1,
      isAffineOpen_biInf_nonzeroLocus hH s fun i => (hs.2 i).1⟩

end GlobalTheory.VeryAmpleCharts
