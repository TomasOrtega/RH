import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
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

open CategoryTheory AlgebraicGeometry Limits Topology
open scoped CommRingCat.HomTopology GlobalTheory.AffinePoints

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Ideal.comap φ.hom (IsLocalRing.maximalIdeal ℂ) = _`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]`.
-/
theorem specMap_closedPoint_asIdeal {A : CommRingCat.{0}} (φ : A ⟶ CommRingCat.of ℂ) :
    ((Spec.map φ).base (IsLocalRing.closedPoint ℂ) : PrimeSpectrum A).asIdeal = RingHom.ker φ.hom := by
  change Ideal.comap φ.hom (IsLocalRing.maximalIdeal ℂ) = _
  rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]

/- English proof (translation)
Take `⟨V, hV, hzV, -⟩` from `exists_isAffineOpen_le z.1 (V := ⊤) le_top`. Use `set F := hV.fromSpec with hF`. Use `set Z : Set (PrimeSpectrum Γ(Y, V)) := F.base ⁻¹' T with hZ`. Establish `hFo : IsOpenEmbedding F.base` using `F.isOpenEmbedding`. Use `set ψ₀ := valMap z.1 V hzV with hψ₀`.

Establish `hz₀ : Spec.map ψ₀ ≫ F = z.1` using `specMap_valMap_fromSpec hV z.1 hzV`. Use `set x₀ : PrimeSpectrum Γ(Y, V) := (Spec.map ψ₀).base (IsLocalRing.closedPoint ℂ) with hx₀`. Establish `hx₀Z : x₀ ∈ Z`. Express the relevant statement in the definitionally equal form `F.base x₀ ∈ T`. Establish `: F.base x₀ = z.1.base (IsLocalRing.closedPoint ℂ)`.

Rewrite using `[← hz₀]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hz`. Establish `hZc : IsClosed Z` using `hT.preimage F.base.hom.continuous`.

Establish `hZi : IsIrreducible Z` using `⟨⟨x₀, hx₀Z⟩, hTi.2.preimage hFo⟩`. Use `set Q := PrimeSpectrum.vanishingIdeal Z with hQ`. Use `haveI hQp : Q.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hZi`. Establish `hZQ : ∀ x : PrimeSpectrum Γ(Y, V), x ∈ Z ↔ Q ≤ x.asIdeal`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx f hf`. Conclude with `(PrimeSpectrum.mem_vanishingIdeal _ _).1 hf x hx`. Introduce `h`. Establish `: x ∈ closure Z`.

Rewrite using `[← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]`. Conclude with `(PrimeSpectrum.mem_zeroLocus _ _).2 h`. Conclude with `hZc.closure_subset this`. Take `⟨t, htT, htW, htV⟩ : (T ∩ ((W : Set Y) ∩ (V : Set Y))).Nonempty` from `hTi.2 _ _ W.2 V.2 hTW ⟨_, hz, (le_preimage_iff z.1 V).1 hzV⟩`. Take `⟨x₁, rfl⟩ : t ∈ Set.range F.base` from `by show t ∈ Set.range hV.fromSpec`.

Rewrite using `[hV.range_fromSpec]`. Conclude with `htV`. Take `⟨_, ⟨g, rfl⟩, hx₁g, hgW⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := x₁) (u := F.base ⁻¹' (W : Set Y)) htW (W.2.preimage F.base.hom.continuous)`. Establish `hgQ : g ∉ Q` using `fun h => hx₁g ((hZQ x₁).1 htT h)`. Use `letI : Algebra ℂ Γ(Y, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V).toAlgebra`.

Use `haveI : Algebra.FiniteType ℂ Γ(Y, V) := (HasRingHomProperty.appLE @LocallyOfFiniteType q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top).comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)`. Use `haveI : Algebra.FiniteType ℂ (Γ(Y, V) ⧸ Q) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q) (Ideal.Quotient.mkₐ_surjective ℂ Q)`. Establish `hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ)`. Simplify using `only [spMap]`. Conclude with `Spec.map_id _`.

Set `φ : (Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ) → (Γ(Y, V) →+* ℂ)` to `fun χ => χ.toRingHom.comp (Ideal.Quotient.mk Q)`. Establish `hφ : ∀ χ a, φ χ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V a) = RingHom.id ℂ a` using `fun χ a => χ.commutes a`. Set `ι : (Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ) → Pts q` to `fun χ => ⟨(CxPts.ofHom (p := q) (σ := RingHom.id ℂ) hV (φ χ) (hφ χ)).1, (CxPts.ofHom (p := q) (σ := RingHom.id ℂ) hV (φ χ) (hφ χ)).2.trans hid⟩`. Establish `hιc : Continuous ι`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations.

Use `(continuous_comp hV.fromSpec).comp ((continuous_specMap (C := ℂ) _).comp ?_)` and prove the remaining obligations. Conclude with `continuous_induced_rng.2 (continuous_pi fun a => GlobalTheory.AffinePoints.continuous_eval (Ideal.Quotient.mk Q a))`. Establish `hιpt : ∀ χ, (ι χ).1 (IsLocalRing.closedPoint ℂ) = F.base ((Spec.map (CommRingCat.ofHom (φ χ))).base (IsLocalRing.closedPoint ℂ))` using `fun χ => rfl`. Establish `hιmem : ∀ χ ∈ {χ : Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ | χ (Ideal.Quotient.mk Q g) ≠ 0}, ι χ ∈ {z' : Pts q | z'.1 (IsLocalRing.closedPoint ℂ) ∈ T ∩ (W : Set Y)}`. Introduce `χ hχ`.

Establish `hk` using `specMap_closedPoint_asIdeal (CommRingCat.ofHom (φ χ))`. Express the relevant statement in the definitionally equal form `_ ∈ T ∩ (W : Set Y)`. Rewrite using `[hιpt]`. Use `⟨(hZQ _).2 ?_, hgW ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`.

Introduce `f hf`. Express the relevant statement in the definitionally equal form `χ (Ideal.Quotient.mk Q f) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]`. Express the relevant statement in the definitionally equal form `g ∉ _`. Rewrite using `[hk]`.

Conclude with `hχ`. Set `ψ₁ : Γ(Y, V) →ₐ[ℂ] ℂ` to `{ ψ₀.hom with commutes' := fun a => (valR_eq _ _ hzV _).symm.trans (valR_constFn_of_section q z.1 z.2 V hzV a) }`. Establish `hker : ∀ a ∈ Q, ψ₁ a = 0`. Introduce `a ha`. Establish `h1 : a ∈ x₀.asIdeal` using `(hZQ x₀).1 hx₀Z ha`.

Rewrite `h1` using `[hx₀, specMap_closedPoint_asIdeal]`. Conclude with `h1`. Set `χ₀ : Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ` to `Ideal.Quotient.liftₐ Q ψ₁ hker`. Establish `hι₀ : ι χ₀ = z`. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (φ χ₀)) ≫ F = z.1`. Rewrite using `[← hz₀]`. Use `congr 2`. Establish `hd` using `GlobalTheory.AffinePoints.dense_nonvanishing (A := Γ(Y, V) ⧸ Q) (f := Ideal.Quotient.mk Q g) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Rewrite using `[← hι₀]`.

Conclude with `map_mem_closure hιc (hd χ₀) hιmem`.
-/
theorem mem_closure_pts_inter {Y : Scheme.{0}} (q : Y ⟶ Sp ℂ) [LocallyOfFiniteType q] (T : Set Y)
    (W : Y.Opens) (hT : IsClosed T) (hTi : IsIrreducible T) (hTW : (T ∩ (W : Set Y)).Nonempty)
    (z : Pts q) (hz : z.1 (IsLocalRing.closedPoint ℂ) ∈ T) :
    z ∈ closure {z' : Pts q | z'.1 (IsLocalRing.closedPoint ℂ) ∈ T ∩ (W : Set Y)} := by
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_le z.1 (V := ⊤) le_top
  set F := hV.fromSpec with hF
  set Z : Set (PrimeSpectrum Γ(Y, V)) := F.base ⁻¹' T with hZ
  have hFo : IsOpenEmbedding F.base := F.isOpenEmbedding

  set ψ₀ := valMap z.1 V hzV with hψ₀
  have hz₀ : Spec.map ψ₀ ≫ F = z.1 := specMap_valMap_fromSpec hV z.1 hzV
  set x₀ : PrimeSpectrum Γ(Y, V) := (Spec.map ψ₀).base (IsLocalRing.closedPoint ℂ) with hx₀
  have hx₀Z : x₀ ∈ Z := by
    change F.base x₀ ∈ T
    have : F.base x₀ = z.1.base (IsLocalRing.closedPoint ℂ) := by
      rw [← hz₀]; rfl
    rw [this]; exact hz
  have hZc : IsClosed Z := hT.preimage F.base.hom.continuous
  have hZi : IsIrreducible Z := ⟨⟨x₀, hx₀Z⟩, hTi.2.preimage hFo⟩
  set Q := PrimeSpectrum.vanishingIdeal Z with hQ
  haveI hQp : Q.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hZi
  have hZQ : ∀ x : PrimeSpectrum Γ(Y, V), x ∈ Z ↔ Q ≤ x.asIdeal := by
    intro x
    constructor
    · intro hx f hf
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf x hx
    · intro h
      have : x ∈ closure Z := by
        rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
        exact (PrimeSpectrum.mem_zeroLocus _ _).2 h
      exact hZc.closure_subset this

  obtain ⟨t, htT, htW, htV⟩ : (T ∩ ((W : Set Y) ∩ (V : Set Y))).Nonempty :=
    hTi.2 _ _ W.2 V.2 hTW ⟨_, hz, (le_preimage_iff z.1 V).1 hzV⟩
  obtain ⟨x₁, rfl⟩ : t ∈ Set.range F.base := by
    show t ∈ Set.range hV.fromSpec
    rw [hV.range_fromSpec]; exact htV
  obtain ⟨_, ⟨g, rfl⟩, hx₁g, hgW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := x₁) (u := F.base ⁻¹' (W : Set Y)) htW (W.2.preimage F.base.hom.continuous)
  have hgQ : g ∉ Q := fun h => hx₁g ((hZQ x₁).1 htT h)
  letI : Algebra ℂ Γ(Y, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  haveI : Algebra.FiniteType ℂ (Γ(Y, V) ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q) (Ideal.Quotient.mkₐ_surjective ℂ Q)
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp only [spMap]
    exact Spec.map_id _
  let φ : (Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ) → (Γ(Y, V) →+* ℂ) := fun χ => χ.toRingHom.comp (Ideal.Quotient.mk Q)
  have hφ : ∀ χ a, φ χ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V a) = RingHom.id ℂ a := fun χ a => χ.commutes a
  let ι : (Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ) → Pts q := fun χ =>
    ⟨(CxPts.ofHom (p := q) (σ := RingHom.id ℂ) hV (φ χ) (hφ χ)).1,
      (CxPts.ofHom (p := q) (σ := RingHom.id ℂ) hV (φ χ) (hφ χ)).2.trans hid⟩
  have hιc : Continuous ι := by
    refine Continuous.subtype_mk ?_ _
    refine (continuous_comp hV.fromSpec).comp ((continuous_specMap (C := ℂ) _).comp ?_)
    exact continuous_induced_rng.2 (continuous_pi fun a => GlobalTheory.AffinePoints.continuous_eval (Ideal.Quotient.mk Q a))
  have hιpt : ∀ χ, (ι χ).1 (IsLocalRing.closedPoint ℂ) =
      F.base ((Spec.map (CommRingCat.ofHom (φ χ))).base (IsLocalRing.closedPoint ℂ)) := fun χ => rfl
  have hιmem : ∀ χ ∈ {χ : Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ | χ (Ideal.Quotient.mk Q g) ≠ 0},
      ι χ ∈ {z' : Pts q | z'.1 (IsLocalRing.closedPoint ℂ) ∈ T ∩ (W : Set Y)} := by
    intro χ hχ
    have hk := specMap_closedPoint_asIdeal (CommRingCat.ofHom (φ χ))
    change _ ∈ T ∩ (W : Set Y)
    rw [hιpt]
    refine ⟨(hZQ _).2 ?_, hgW ?_⟩
    · rw [hk]
      intro f hf
      change χ (Ideal.Quotient.mk Q f) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    · change g ∉ _
      rw [hk]
      exact hχ
  let ψ₁ : Γ(Y, V) →ₐ[ℂ] ℂ :=
    { ψ₀.hom with
      commutes' := fun a => (valR_eq _ _ hzV _).symm.trans (valR_constFn_of_section q z.1 z.2 V hzV a) }
  have hker : ∀ a ∈ Q, ψ₁ a = 0 := by
    intro a ha
    have h1 : a ∈ x₀.asIdeal := (hZQ x₀).1 hx₀Z ha
    rw [hx₀, specMap_closedPoint_asIdeal] at h1
    exact h1
  let χ₀ : Γ(Y, V) ⧸ Q →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q ψ₁ hker
  have hι₀ : ι χ₀ = z := by
    refine Subtype.ext ?_
    change Spec.map (CommRingCat.ofHom (φ χ₀)) ≫ F = z.1
    rw [← hz₀]
    congr 2
  have hd := GlobalTheory.AffinePoints.dense_nonvanishing (A := Γ(Y, V) ⧸ Q) (f := Ideal.Quotient.mk Q g)
    (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  rw [← hι₀]
  exact map_mem_closure hιc (hd χ₀) hιmem

end GlobalTheory.IrrAn

namespace GlobalTheory.IrrAn

open CategoryTheory AlgebraicGeometry Limits Topology

/- English proof (translation)
Introduce `k _ X p _ σ T W hT hTi hTW y hy`. Set `e` to `PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback p (spMap σ))`. Establish `hpt : ∀ z : Pts (pullback.snd p (spMap σ)), pt p σ (e z) = z.1` using `fun z => pullback.hom_ext (pullback.lift_fst _ _ _) (by simp only [pt, pullback.lift_snd]; exact z.2.symm)`. Use `set z := e.symm y with hzdef`. Establish `hz : z.1 (IsLocalRing.closedPoint ℂ) ∈ T`.

Rewrite using `[← hpt, hzdef, e.apply_symm_apply]`. Conclude with `hy`. Rewrite using `[← e.apply_symm_apply y, ← hzdef]`. Use `map_mem_closure e.continuous (mem_closure_pts_inter _ T W hT hTi hTW z hz) fun z' hz' => ?_` and prove the remaining obligations. Unfold `ptsOf`.

Rewrite using `[Set.mem_setOf_eq, hpt]`. Conclude with `hz'`.
-/
theorem ptsOf_subset_closure_inter : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [LocallyOfFiniteType p] (σ : k →+* ℂ) (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})) (W : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens), IsClosed T → IsIrreducible T → (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0}))).Nonempty → GlobalTheory.IrrAn.ptsOf p σ T ⊆ closure (GlobalTheory.IrrAn.ptsOf p σ (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0})))) := by
  intro k _ X p _ σ T W hT hTi hTW y hy
  let e := PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback p (spMap σ))
  have hpt : ∀ z : Pts (pullback.snd p (spMap σ)), pt p σ (e z) = z.1 := fun z =>
    pullback.hom_ext (pullback.lift_fst _ _ _) (by simp only [pt, pullback.lift_snd]; exact z.2.symm)
  set z := e.symm y with hzdef
  have hz : z.1 (IsLocalRing.closedPoint ℂ) ∈ T := by
    rw [← hpt, hzdef, e.apply_symm_apply]; exact hy
  rw [← e.apply_symm_apply y, ← hzdef]
  refine map_mem_closure e.continuous (mem_closure_pts_inter _ T W hT hTi hTW z hz) fun z' hz' => ?_
  unfold ptsOf
  rw [Set.mem_setOf_eq, hpt]
  exact hz'

end GlobalTheory.IrrAn

end
