import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.TupleCoords

/- English proof (translation)
Simplify using `only [valR, dif_pos h, GlobalTheory.Points.valMap, CommRingCat.hom_comp, RingHom.comp_apply]`.
-/
private theorem valR_eq_valMap {A : Type} [CommRing A] {X : Scheme} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ (TopologicalSpace.Opens.map x.base).obj U) (f : X.presheaf.obj (op U)) :
    valR x U f = (GlobalTheory.Points.valMap x U h).hom f := by
  simp only [valR, dif_pos h, GlobalTheory.Points.valMap, CommRingCat.hom_comp, RingHom.comp_apply]

/- English proof (translation)
Introduce `Ω _ _ r p`. Set `y0 : Sp Ω` to `(default : PrimeSpectrum Ω)`. Take `⟨i, hi0⟩` from `GlobalTheory.ProjSpace.exists_mem_chart ℚ r (p.base y0)`. Establish `hi : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj (GlobalTheory.ProjSpace.chart ℚ r i)`. Introduce `y _`.

Establish `hy : y = y0` using `Subsingleton.elim (α := PrimeSpectrum Ω) y y0`. Substitute `hy` using the available equality. Conclude with `hi0`. Use `set t : Fin (r + 1) → Ω := fun j => valR p (GlobalTheory.ProjSpace.chart ℚ r i) (GlobalTheory.ProjSpace.ratio ℚ r i j) with ht_def`. Establish `hti : t i = 1`.

Simplify using `only [ht_def, valR_eq_valMap p _ hi]`. Rewrite using `[show GlobalTheory.ProjSpace.ratio ℚ r i i = 1 from GlobalTheory.ProjSpace.ratioOn_self]`. Conclude with `map_one _`. Establish `hti0 : t i ≠ 0` using `by rw [hti]; exact one_ne_zero`. Establish `htne : t ≠ 0` using `fun h => hti0 (congr_fun h i)`.

Use `⟨t, htne, ?_⟩` and prove the remaining obligations. Establish `hq : ⊤ ≤ (TopologicalSpace.Opens.map (point ℚ t htne).base).obj (GlobalTheory.ProjSpace.chart ℚ r i)` using `(GlobalTheory.TuplePoint.le_point_preimage_iff i).2 hti0`. Use `GlobalTheory.Points.ext_of_valR (GlobalTheory.ProjSpace.isAffineOpen_chart ℚ r i) hi hq ?_` and prove the remaining obligations. Introduce `f`. Take `⟨P, rfl⟩` from `GlobalTheory.ProjSpace.aeval_ratio_surjective ℚ r i f`.

Rewrite using `[valR_eq_valMap p _ hi, valR_eq_valMap _ _ hq]`. Establish `key : (GlobalTheory.Points.valMap p _ hi).hom.comp (MvPolynomial.aeval (R` using `ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom = (GlobalTheory.Points.valMap (point ℚ t htne) _ hq).hom.comp (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom := by`. Use `MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_` and prove the remaining obligations. Introduce `j`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]`.

Rewrite using `[← valR_eq_valMap p _ hi, ← valR_eq_valMap _ _ hq, GlobalTheory.TuplePoint.valR_point_ratio hti0 j, hti, div_one]`. Conclude with `RingHom.congr_fun key P`.
-/
theorem exists_tuple_eq_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r),
    ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  intro Ω _ _ r p
  let y0 : Sp Ω := (default : PrimeSpectrum Ω)
  obtain ⟨i, hi0⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℚ r (p.base y0)
  have hi : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj (GlobalTheory.ProjSpace.chart ℚ r i) := by
    intro y _
    have hy : y = y0 := Subsingleton.elim (α := PrimeSpectrum Ω) y y0
    subst hy
    exact hi0
  set t : Fin (r + 1) → Ω := fun j => valR p (GlobalTheory.ProjSpace.chart ℚ r i) (GlobalTheory.ProjSpace.ratio ℚ r i j)
    with ht_def
  have hti : t i = 1 := by
    simp only [ht_def, valR_eq_valMap p _ hi]
    rw [show GlobalTheory.ProjSpace.ratio ℚ r i i = 1 from GlobalTheory.ProjSpace.ratioOn_self]
    exact map_one _
  have hti0 : t i ≠ 0 := by rw [hti]; exact one_ne_zero
  have htne : t ≠ 0 := fun h => hti0 (congr_fun h i)
  refine ⟨t, htne, ?_⟩
  have hq : ⊤ ≤ (TopologicalSpace.Opens.map (point ℚ t htne).base).obj (GlobalTheory.ProjSpace.chart ℚ r i) :=
    (GlobalTheory.TuplePoint.le_point_preimage_iff i).2 hti0
  refine GlobalTheory.Points.ext_of_valR (GlobalTheory.ProjSpace.isAffineOpen_chart ℚ r i) hi hq ?_
  intro f
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℚ r i f
  rw [valR_eq_valMap p _ hi, valR_eq_valMap _ _ hq]
  have key : (GlobalTheory.Points.valMap p _ hi).hom.comp (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom
      = (GlobalTheory.Points.valMap (point ℚ t htne) _ hq).hom.comp
          (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
    rw [← valR_eq_valMap p _ hi, ← valR_eq_valMap _ _ hq,
      GlobalTheory.TuplePoint.valR_point_ratio hti0 j, hti, div_one]
  exact RingHom.congr_fun key P

end GlobalTheory.CompanionTheory.Ar.TupleCoords
