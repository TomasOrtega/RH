import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points GlobalTheory.CxPts
open scoped LinearAlgebra.Projectivization

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ X p σ N i _ hi`. Establish `hm : Function.Injective (PtsOver.map i hi (spMap σ))` using `(PtsOver.isClosedEmbedding_map i hi (spMap σ)).injective`. Use `choose v hv using fun y : CxPts p σ => projPt_surjective σ (PtsOver.map i hi (spMap σ) y)`. Establish `hv1 : ∀ y : CxPts p σ, y.1 ≫ i = GlobalTheory.ProjSpace.pt σ (v y).1 (v y).2` using `fun y => (congrArg Subtype.val (hv y)).symm`. Use `⟨fun y => Projectivization.mk ℂ (v y).1 (GlobalTheory.ProjSpace.span_range_eq_top_iff_ne_zero.1 (v y).2), ?_, ?_⟩` and prove the remaining obligations.

Introduce `y y' h`. Take `⟨c, hc⟩` from `(Projectivization.mk_eq_mk_iff ℂ _ _ _ _).1 h`. Apply `hm` to reduce the goal to its premises. Rewrite using `[← hv y, ← hv y']`. Conclude with `((projPt_eq_iff σ _ _).2 ⟨c, hc.symm⟩).symm`.

Introduce `a y hy`. Establish `hy' : ⊤ ≤ GlobalTheory.ProjSpace.pt σ (v y).1 (v y).2 ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a`. Rewrite using `[← hv1 y]`. Conclude with `hy`. Establish `hu : IsUnit ((v y).1 a)` using `(le_pt_preimage_chart_iff σ _ _ a).1 hy'`.

Establish `hval : ∀ j, ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y = (v y).1 j * Ring.inverse ((v y).1 a)`. Introduce `j`. Express the relevant statement in the definitionally equal form `valR y.1 _ _ = _`. Rewrite using `[GlobalTheory.ZH.LinFrame.valR_pullRatio y.1 i le_rfl hy j, hv1 y]`. Conclude with `valR_pt_ratio σ _ _ hu j`.

Establish `hw : (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) = Ring.inverse ((v y).1 a) • (v y).1`. Use function extensionality and compare the values at `j`. Rewrite using `[hval, Pi.smul_apply, smul_eq_mul, mul_comm]`. Establish `h0 : (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) ≠ 0`. Introduce `h0`.

Use `congrFun h0 a` as an intermediate fact. Rewrite `this` using `[hval, Ring.mul_inverse_cancel _ hu]`. Conclude with `one_ne_zero this`. Use `⟨h0, ?_⟩` and prove the remaining obligations. Use `(Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨(v y).1 a, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw, smul_smul, Ring.mul_inverse_cancel _ hu, one_smul]`.
-/
theorem complexPts_proj_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (N : ℕ) (i : X ⟶ PSpace k N) [IsClosedImmersion i], i ≫ PSpace.str k N = p → ∃ F : CxPts p σ → ℙ ℂ (Fin (N + 1) → ℂ), Function.Injective F ∧ ∀ (a : Fin (N + 1)) (y : CxPts p σ), y ∈ ptsIn p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) → ∃ h : (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) ≠ 0, F y = Projectivization.mk ℂ _ h := by
  intro k _ X p σ N i _ hi
  classical
  have hm : Function.Injective (PtsOver.map i hi (spMap σ)) :=
    (PtsOver.isClosedEmbedding_map i hi (spMap σ)).injective
  choose v hv using fun y : CxPts p σ => projPt_surjective σ (PtsOver.map i hi (spMap σ) y)
  have hv1 : ∀ y : CxPts p σ, y.1 ≫ i = GlobalTheory.ProjSpace.pt σ (v y).1 (v y).2 := fun y =>
    (congrArg Subtype.val (hv y)).symm
  refine ⟨fun y => Projectivization.mk ℂ (v y).1
    (GlobalTheory.ProjSpace.span_range_eq_top_iff_ne_zero.1 (v y).2), ?_, ?_⟩
  · intro y y' h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).1 h
    apply hm
    rw [← hv y, ← hv y']
    exact ((projPt_eq_iff σ _ _).2 ⟨c, hc.symm⟩).symm
  · intro a y hy
    have hy' : ⊤ ≤ GlobalTheory.ProjSpace.pt σ (v y).1 (v y).2 ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a := by
      rw [← hv1 y]; exact hy
    have hu : IsUnit ((v y).1 a) := (le_pt_preimage_chart_iff σ _ _ a).1 hy'
    have hval : ∀ j, ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a)
        (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y = (v y).1 j * Ring.inverse ((v y).1 a) := by
      intro j
      change valR y.1 _ _ = _
      rw [GlobalTheory.ZH.LinFrame.valR_pullRatio y.1 i le_rfl hy j, hv1 y]
      exact valR_pt_ratio σ _ _ hu j
    have hw : (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a)
        (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) = Ring.inverse ((v y).1 a) • (v y).1 := by
      funext j; rw [hval, Pi.smul_apply, smul_eq_mul, mul_comm]
    have h0 : (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a)
        (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) ≠ 0 := by
      intro h0
      have := congrFun h0 a
      rw [hval, Ring.mul_inverse_cancel _ hu] at this
      exact one_ne_zero this
    refine ⟨h0, ?_⟩
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨(v y).1 a, ?_⟩
    rw [hw, smul_smul, Ring.mul_inverse_cancel _ hu, one_smul]

end GlobalTheory
