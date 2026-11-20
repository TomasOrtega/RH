import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicOfRegularFunctionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.IrrAn

noncomputable section

namespace GlobalTheory.IrrAn

/- English proof (translation)
Set `O : Y.Opens` to `⟨Tᶜ, hT.isOpen_compl⟩`. Establish `hc : IsCompact ((U : Set Y) ∩ Tᶜ)`. Establish `h1 : IsCompact ((O.ι ⁻¹ᵁ U : (O : Scheme.{0}).Opens) : Set (O : Scheme.{0}))` using `QuasiCompact.isCompact_preimage (f := O.ι) _ U.isOpen hU.isCompact`. Establish `h2` using `h1.image O.ι.continuous`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, h'⟩`. Conclude with `⟨⟨z, h'⟩, h, rfl⟩`. Introduce and unpack `⟨w, h, rfl⟩`.

Conclude with `⟨h, w.2⟩`. Take `⟨s, hs⟩` from `hc.elim_finite_subcover (fun g : {g : Γ(Y, U) // Y.basicOpen g ≤ O} => (Y.basicOpen g.1 : Set Y)) (fun g => (Y.basicOpen g.1).isOpen) (fun z hz => by`. Take `⟨g, hg, hz'⟩` from `hU.exists_basicOpen_le (V := O) ⟨z, hz.2⟩ hz.1`. Conclude with `Set.mem_iUnion.2 ⟨⟨g, hg⟩, hz'⟩)`. Use `⟨s.card, fun i => (s.equivFin.symm i).1.1, fun z hz => ⟨fun h i hi => ?_, fun h => ?_⟩⟩` and prove the remaining obligations.

Conclude with `(s.equivFin.symm i).1.2 hi h`. Assume the negation of the conclusion as `hzT`. Take `⟨g, hg, hz'⟩` from `Set.mem_iUnion₂.1 (hs ⟨hz, hzT⟩)`. Use `h (s.equivFin ⟨g, hg⟩) ?_` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`.

Conclude with `hz'`.
-/
theorem exists_fin_basicOpen {Y : Scheme.{0}} [IsLocallyNoetherian Y] {U : Y.Opens}
    (hU : IsAffineOpen U) {T : Set Y} (hT : IsClosed T) :
    ∃ (r : ℕ) (f : Fin r → Γ(Y, U)), ∀ z ∈ U, (z ∈ T ↔ ∀ i, z ∉ Y.basicOpen (f i)) := by
  let O : Y.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  have hc : IsCompact ((U : Set Y) ∩ Tᶜ) := by
    have h1 : IsCompact ((O.ι ⁻¹ᵁ U : (O : Scheme.{0}).Opens) : Set (O : Scheme.{0})) :=
      QuasiCompact.isCompact_preimage (f := O.ι) _ U.isOpen hU.isCompact
    have h2 := h1.image O.ι.continuous
    convert h2 using 1
    ext z
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨⟨z, h'⟩, h, rfl⟩
    · rintro ⟨w, h, rfl⟩
      exact ⟨h, w.2⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun g : {g : Γ(Y, U) // Y.basicOpen g ≤ O} => (Y.basicOpen g.1 : Set Y))
    (fun g => (Y.basicOpen g.1).isOpen) (fun z hz => by
      obtain ⟨g, hg, hz'⟩ := hU.exists_basicOpen_le (V := O) ⟨z, hz.2⟩ hz.1
      exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, hz'⟩)
  refine ⟨s.card, fun i => (s.equivFin.symm i).1.1, fun z hz => ⟨fun h i hi => ?_, fun h => ?_⟩⟩
  · exact (s.equivFin.symm i).1.2 hi h
  · by_contra hzT
    obtain ⟨g, hg, hz'⟩ := Set.mem_iUnion₂.1 (hs ⟨hz, hzT⟩)
    refine h (s.equivFin ⟨g, hg⟩) ?_
    simp only [Equiv.symm_apply_apply]
    exact hz'

/- English proof (translation)
Set `e` to `PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback p (spMap σ))`. Use `(continuous_subtype_val.comp e.symm.continuous).congr fun y => ?_` and prove the remaining obligations. Use `Limits.pullback.hom_ext ?_ ?_` and prove the remaining obligations. Use `PtsOver.baseChangeHomeomorph_val (IsPullback.of_hasPullback p (spMap σ)) (e.symm y)` as an intermediate fact. Rewrite using `[pt, Limits.pullback.lift_fst]`.

Conclude with `this.symm.trans (congrArg Subtype.val (e.apply_symm_apply y))`. Rewrite using `[pt, Limits.pullback.lift_snd]`. Conclude with `(e.symm y).2`.
-/
theorem continuous_pt_baseChange {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)
    (σ : k →+* ℂ) : Continuous (pt p σ) := by
  let e := PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback p (spMap σ))
  refine (continuous_subtype_val.comp e.symm.continuous).congr fun y => ?_
  refine Limits.pullback.hom_ext ?_ ?_
  · have := PtsOver.baseChangeHomeomorph_val (IsPullback.of_hasPullback p (spMap σ)) (e.symm y)
    rw [pt, Limits.pullback.lift_fst]
    exact this.symm.trans (congrArg Subtype.val (e.apply_symm_apply y))
  · rw [pt, Limits.pullback.lift_snd]
    exact (e.symm y).2

/- English proof (translation)
Use `(isOpen_setOf_le_preimage (C := ℂ) U).preimage (continuous_pt_baseChange p σ)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Conclude with `(GlobalTheory.Points.le_preimage_iff _ _).symm`.
-/
theorem isOpen_ptsOf_opens {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)
    (σ : k →+* ℂ) (U : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens) :
    IsOpen (ptsOf p σ (U : Set (Limits.pullback p (spMap σ) : Scheme.{0}))) := by
  have := (isOpen_setOf_le_preimage (C := ℂ) U).preimage (continuous_pt_baseChange p σ)
  convert this using 1
  ext y
  exact (GlobalTheory.Points.le_preimage_iff _ _).symm

/- English proof (translation)
Introduce `x`. Establish `: IsLocallyNoetherian (Limits.pullback p (spMap σ) : Scheme.{0})` using `LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.snd p (spMap σ))`. Take `⟨U, hU, hx, -⟩` from `Opens.isBasis_iff_nbhd.1 (Limits.pullback p (spMap σ) : Scheme.{0}).isBasis_affineOpens (Opens.mem_top (pt p σ x (IsLocalRing.closedPoint ℂ)))`. Take `⟨r, f, hf⟩` from `exists_fin_basicOpen hU hT`. Establish `ho` using `isOpen_ptsOf_opens p σ U`.

Use `⟨_, ho, hx, r, fun i y => valR (pt p σ y) U (f i), fun i => (R.finAtlas_holoOn_iff ho).2 (GlobalTheory.T.holomorphic_of_regular_function k X p σ d R U (f i)), ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[Set.inter_comm]`. Use `and_congr_right fun hy => (hf _ hy).trans (forall_congr' fun i => ?_)` and prove the remaining obligations. Rewrite using `[← GlobalTheory.Points.le_preimage_iff, le_preimage_basicOpen_iff _ ((GlobalTheory.Points.le_preimage_iff _ _).2 hy), isUnit_iff_ne_zero, not_not]`.
-/
theorem isAnalyticSubset_ptsOf (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) [CompactSpace (CxPts p σ)]
    (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})) (hT : IsClosed T) :
    R.finAtlas.IsAnalyticSubset (GlobalTheory.IrrAn.ptsOf p σ T) := by
  intro x
  have : IsLocallyNoetherian (Limits.pullback p (spMap σ) : Scheme.{0}) :=
    LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.snd p (spMap σ))
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1
    (Limits.pullback p (spMap σ) : Scheme.{0}).isBasis_affineOpens
    (Opens.mem_top (pt p σ x (IsLocalRing.closedPoint ℂ)))
  obtain ⟨r, f, hf⟩ := exists_fin_basicOpen hU hT
  have ho := isOpen_ptsOf_opens p σ U
  refine ⟨_, ho, hx, r, fun i y => valR (pt p σ y) U (f i),
    fun i => (R.finAtlas_holoOn_iff ho).2 (GlobalTheory.T.holomorphic_of_regular_function k X p σ d R U (f i)), ?_⟩
  ext y
  rw [Set.inter_comm]
  refine and_congr_right fun hy => (hf _ hy).trans (forall_congr' fun i => ?_)
  rw [← GlobalTheory.Points.le_preimage_iff,
    le_preimage_basicOpen_iff _ ((GlobalTheory.Points.le_preimage_iff _ _).2 hy), isUnit_iff_ne_zero, not_not]

end GlobalTheory.IrrAn

end
