import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

namespace GlobalTheory.ZH.ImmProj

/- English proof (translation)
Introduce `k _ X p H J s m e ⟨hc, hi⟩`. Establish `hs : ⨆ i, nonzeroLocus (s (e i)) = ⊤`. Rewrite using `[e.iSup_comp (g := fun j => nonzeroLocus (s j))]`. Simplify `hc` using `only [Set.mem_univ, iSup_pos]`. Use `⟨ProjSpace.toProj p (fun i => s (e i)) hs, ?_, ProjSpace.toProj_str _ _ _, ?_⟩` and prove the remaining obligations.

Use `(ProjSpace.isClosedImmersion_toProj_iff p _ hs).2 fun i => ⟨(hi (e i) trivial).1, ?_⟩` and prove the remaining obligations. Take `⟨r, hr, hcl⟩` from `(hi (e i) trivial).2`. Choose the witnesses or unpack the hypotheses as in `rfl : r = fun j => ProjSpace.secRatio (s (e i)) (s j) :=`. Use function extensionality and compare the values at `fun j => ProjSpace.eq_secRatio _ _ (hr j)`. Rewrite using `[← SpanImm.closure_eq_top_iff, ← hcl]`.

Use `congr 2`. Conclude with `e.surjective.range_comp (fun j => ProjSpace.secRatio (s (e i)) (s j))`. Introduce `K _ x v hv`. Take `⟨i, hx⟩` from `Points.exists_le_preimage_of_iSup_eq_top x hs`. Establish `hu` using `(CrdCalc.crd_isUnit_iff (e i) hv).2 hx`.

Establish `hle` using `(ProjSpace.toProj_preimage_chart p (fun i => s (e i)) hs i).ge`. Use `⟨i, hu.unit, hx.trans (x.preimage_mono hle), fun j => ?_⟩` and prove the remaining obligations. Establish `h1` using `CrdCalc.crd_ratio (i := e i) (j := e j) hv (ProjSpace.secRatio_spec (s (e i)) (s (e j))) hx`. Use `beta_reduce`. Rewrite using `[h1, IsUnit.unit_spec, mul_comm, ← ProjSpace.pullRatio_toProj p (fun i => s (e i)) hs i j]`.

Conclude with `congrArg _ (Points.valR_appLE x _ hle hx _)`.
-/
theorem exists_closedImmersion_of_immBy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (m : ℕ) (e : Fin (m + 1) ≃ J), ImmBy p H s Set.univ → ∃ φ : X ⟶ PSpace k m, IsClosedImmersion φ ∧ φ ≫ PSpace.str k m = p ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd (ProjSpace.O1 k m) (ProjSpace.coord k m) (x ≫ φ) (fun i => v (e i)) := by
  intro k _ X p H J s m e ⟨hc, hi⟩
  have hs : ⨆ i, nonzeroLocus (s (e i)) = ⊤ := by
    rw [e.iSup_comp (g := fun j => nonzeroLocus (s j))]
    simpa only [Set.mem_univ, iSup_pos] using hc
  refine ⟨ProjSpace.toProj p (fun i => s (e i)) hs, ?_, ProjSpace.toProj_str _ _ _, ?_⟩
  · refine (ProjSpace.isClosedImmersion_toProj_iff p _ hs).2 fun i => ⟨(hi (e i) trivial).1, ?_⟩
    obtain ⟨r, hr, hcl⟩ := (hi (e i) trivial).2
    obtain rfl : r = fun j => ProjSpace.secRatio (s (e i)) (s j) :=
      funext fun j => ProjSpace.eq_secRatio _ _ (hr j)
    rw [← SpanImm.closure_eq_top_iff, ← hcl]
    congr 2
    exact e.surjective.range_comp (fun j => ProjSpace.secRatio (s (e i)) (s j))
  · intro K _ x v hv
    obtain ⟨i, hx⟩ := Points.exists_le_preimage_of_iSup_eq_top x hs
    have hu := (CrdCalc.crd_isUnit_iff (e i) hv).2 hx
    have hle := (ProjSpace.toProj_preimage_chart p (fun i => s (e i)) hs i).ge
    refine ⟨i, hu.unit, hx.trans (x.preimage_mono hle), fun j => ?_⟩
    have h1 := CrdCalc.crd_ratio (i := e i) (j := e j) hv (ProjSpace.secRatio_spec (s (e i)) (s (e j))) hx
    beta_reduce
    rw [h1, IsUnit.unit_spec, mul_comm, ← ProjSpace.pullRatio_toProj p (fun i => s (e i)) hs i j]
    exact congrArg _ (Points.valR_appLE x _ hle hx _)

end GlobalTheory.ZH.ImmProj
