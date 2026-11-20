import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd`. Use `haveI := hji`. Establish `hU' : Formalism.L2.Pj.IsUnf U.toPj` using `(Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU`. Distinguish the cases in `hne : ((U.X k).dom).Nonempty`. Take `⟨x₀, hx₀⟩` from `hne`.

Set `sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom` to `fun x => if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩`. Establish `hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩` using `fun x h => dif_pos h`. Establish `h1` using `BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]`. Establish `h2` using `LocLift.isHolTo_comp_hom h1 T.Z.jQ`. Establish `hψ : DifferentiableOn ℂ ψ W` using `differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b`.

Establish `h3` using `LocLift.isHolTo_comp h2 hW hψ hψW`. Set `P : V n → CxPts (genStr T.Z) σ` to `fun w => cxPt T.Z (U.un k (sf (ψ w)))`. Establish `h4 : IsHolTo W fun w => (P w).1` using `h3`. Establish `hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w` using `fun w h => by`. Simplify using `only [P, hsf _ h]`.

Establish `hc : ContinuousOn P W` using `GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4`. Establish `hκ : Topology.IsOpenEmbedding (cxOf e σ hj)` using `isOpenEmbedding_cxOf e σ hj`. Establish `hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source)`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hw, h, y', hy', he⟩`. Conclude with `⟨hw, y', hy', he.trans (hP w h)⟩`. Introduce and unpack `⟨hw, y', hy', he⟩`. Conclude with `⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩`. Set `q : V n → CxPts X.str (σ.comp e.toRingHom)` to `fun w => if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0`.

Establish `hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w` using `fun w h => by`. Simplify using `only [q, dif_pos h]`. Conclude with `h.choose_spec`. Use `⟨q, ?_, fun w _ h hex => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hS]`.

Conclude with `hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)`. Rewrite `hex`, the goal using `[hP w h]`. Conclude with `hq w hex`. Rewrite using `[hS, differentiableOn_euclidean]`. Introduce `a`.

Establish `hd` using `(h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2`. Use `(hd.mono fun w hw => ⟨hw.1, ?_⟩).congr fun w hw => ?_` and prove the remaining obligations. Take `⟨hq1, hq2⟩` from `hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩) show ⊤ ≤ (P w).1 ⁻¹ᵁ _`. Rewrite using `[← hq2]`. Conclude with `le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)`.

Take `⟨hq1, hq2⟩` from `hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩) show c'.e (q w) a = valAt' (P w).1 _ _`. Rewrite using `[c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]`. Establish `hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅` using `Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩`. Use `⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩` and prove the remaining obligations. Rewrite using `[hS]`.

Conclude with `isOpen_empty`. Rewrite using `[hS]`. Conclude with `differentiableOn_empty`.
-/
theorem isHol_chart_framePt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd
  classical
  haveI := hji
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  by_cases hne : ((U.X k).dom).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
      if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩
    have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
    have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
    have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
    have hψ : DifferentiableOn ℂ ψ W :=
      differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
    have h3 := LocLift.isHolTo_comp h2 hW hψ hψW
    let P : V n → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
    have h4 : IsHolTo W fun w => (P w).1 := h3
    have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
      simp only [P, hsf _ h]
    have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
    have hκ : Topology.IsOpenEmbedding (cxOf e σ hj) := isOpenEmbedding_cxOf e σ hj
    have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source) := by
      ext w
      constructor
      · rintro ⟨hw, h, y', hy', he⟩
        exact ⟨hw, y', hy', he.trans (hP w h)⟩
      · rintro ⟨hw, y', hy', he⟩
        exact ⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩
    let q : V n → CxPts X.str (σ.comp e.toRingHom) := fun w =>
      if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0
    have hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) →
        q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w := fun w h => by
      simp only [q, dif_pos h]
      exact h.choose_spec
    refine ⟨q, ?_, fun w _ h hex => ?_, ?_⟩
    · rw [hS]
      exact hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)
    · rw [hP w h] at hex ⊢
      exact hq w hex
    · rw [hS, differentiableOn_euclidean]
      intro a
      have hd := (h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2
      refine (hd.mono fun w hw => ⟨hw.1, ?_⟩).congr fun w hw => ?_
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show ⊤ ≤ (P w).1 ⁻¹ᵁ _
        rw [← hq2]
        exact le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show c'.e (q w) a = valAt' (P w).1 _ _
        rw [c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]
  · have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩
    refine ⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩
    · rw [hS]
      exact isOpen_empty
    · rw [hS]
      exact differentiableOn_empty

end GlobalTheory.LieBase
