import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `e : stalkOf (closedPoint W) = (stalkClosedPointIso (CommRingCat.of W)).inv.hom`. Unfold `stalkOf`. Rewrite using `[← ΓSpecIso_hom_stalkClosedPointIso_inv]`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite `h` using `[e]`. Conclude with `(isUnit_map_iff (stalkClosedPointIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv v).1 h`.
-/
theorem stalkOf_closedPoint_isUnit {W : Type} [CommRing W] [IsLocalRing W] (v : W)
    (h : IsUnit (stalkOf (closedPoint W) v)) : IsUnit v := by
  have e : stalkOf (closedPoint W) = (stalkClosedPointIso (CommRingCat.of W)).inv.hom := by
    unfold stalkOf
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    ext x
    simp
  rw [e] at h
  exact (isUnit_map_iff (stalkClosedPointIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv v).1 h

/- English proof (translation)
Introduce `R _ _ _ D k α b v hv hmem`. Establish `hmem' : ∃ j, eSec D.P.A (closedPoint R) ∈ D.P.A.left.basicOpen (b.f j)`. Unfold `nonzeroLocus at hmem`. Simplify `hmem` using `[TopologicalSpace.Opens.mem_iSup]`. Take `⟨j, hj⟩` from `hmem'`.

Establish `hjU` using `D.P.A.left.basicOpen_le (b.f j) hj`. Establish `hu` using `(Scheme.mem_basicOpen _ _ _ hjU).1 hj`. Take `⟨J, hJ, -⟩` from `exists_good (Z := Sp R) D.P.L D.P.isLB (closedPoint R) (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)`. Establish `hsv` using `hv (closedPoint R) J hJ`. Establish `e1` using `sec_trans b (unitW D.P.A) (closedPoint R) (hJ.mem (D.famφB α) (unitW D.P.A)) hjU`.

Establish `hg : IsUnit (gs (unitW D.P.A) (closedPoint R) _ (b.f j))`. Rewrite using `[gs_eq _ _ _ hjU]`. Establish `e2` using `Scheme.Hom.germ_stalkMap_apply (eSec D.P.A) _ (closedPoint R) hjU (b.f j)`. Conclude with `e2 ▸ hu.map ((eSec D.P.A).stalkMap (closedPoint R)).hom`. Establish `hs : IsUnit (sval b (unitW D.P.A) (closedPoint R) J)` using `by show IsUnit (gs _ _ _ _)`.

Rewrite using `[e1]`. Conclude with `(Units.isUnit _).mul hg`. Rewrite `hs` using `[hsv]`. Conclude with `stalkOf_closedPoint_isUnit v (isUnit_of_mul_isUnit_left hs)`.
-/
theorem isUnit_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R), OrigVal D b v → eSec D.P.A (closedPoint R) ∈ nonzeroLocus b → IsUnit v := by
  intro R _ _ _ D k α b v hv hmem
  have hmem' : ∃ j, eSec D.P.A (closedPoint R) ∈ D.P.A.left.basicOpen (b.f j) := by
    unfold nonzeroLocus at hmem
    simpa [TopologicalSpace.Opens.mem_iSup] using hmem
  obtain ⟨j, hj⟩ := hmem'
  have hjU := D.P.A.left.basicOpen_le (b.f j) hj
  have hu := (Scheme.mem_basicOpen _ _ _ hjU).1 hj
  obtain ⟨J, hJ, -⟩ := exists_good (Z := Sp R) D.P.L D.P.isLB (closedPoint R) (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hsv := hv (closedPoint R) J hJ
  have e1 := sec_trans b (unitW D.P.A) (closedPoint R) (hJ.mem (D.famφB α) (unitW D.P.A)) hjU
  have hg : IsUnit (gs (unitW D.P.A) (closedPoint R) _ (b.f j)) := by
    rw [gs_eq _ _ _ hjU]
    have e2 := Scheme.Hom.germ_stalkMap_apply (eSec D.P.A) _ (closedPoint R) hjU (b.f j)
    exact e2 ▸ hu.map ((eSec D.P.A).stalkMap (closedPoint R)).hom
  have hs : IsUnit (sval b (unitW D.P.A) (closedPoint R) J) := by
    show IsUnit (gs _ _ _ _)
    rw [e1]
    exact (Units.isUnit _).mul hg
  rw [hsv] at hs
  exact stalkOf_closedPoint_isUnit v (isUnit_of_mul_isUnit_left hs)

end GlobalTheory.Mum
