import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.IntegralClosedSubscheme

/- English proof (translation)
Establish `hU : ∀ U : S.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(S, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U)))`. Introduce `U`. Establish `h : ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).IsRadical`. Rewrite using `[Scheme.IdealSheafData.vanishingIdeal_ideal]`. Conclude with `PrimeSpectrum.isRadical_vanishingIdeal _`.

Use `haveI : _root_.IsReduced (Γ(S, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) := (Ideal.isRadical_iff_quotient_reduced _).mp h`. Use `infer_instance`. Use `haveI : ∀ i, IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X i) := hU`. Conclude with `IsReduced.of_openCover _ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover`.
-/
theorem reduced_sub {S : Scheme.{0}} (Z : TopologicalSpace.Closeds S) :
    AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have hU : ∀ U : S.affineOpens, IsReduced
      (Spec (CommRingCat.of (Γ(S, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U))) := by
    intro U
    have h : ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    haveI : _root_.IsReduced (Γ(S, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp h
    infer_instance
  haveI : ∀ i, IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X i) := hU
  exact IsReduced.of_openCover _ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

/- English proof (translation)
Establish `h1 : g.ker.support ≤ Z`. Introduce `x hx`. Establish `hx' : x ∈ (g.ker.support : Set S)` using `hx`. Rewrite `hx'` using `[Scheme.Hom.support_ker]`. Conclude with `closure_minimal h Z.isClosed hx'`.

Use `(Scheme.IdealSheafData.vanishingIdeal_antimono h1).trans ?_` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.vanishingIdeal_support]`. Introduce `U s hs`. Rewrite `hs` using `[Scheme.IdealSheafData.radical_ideal]`. Rewrite `hs`, the goal using `[Scheme.Hom.ker_apply]`.

Take `⟨n, hn⟩` from `hs`. Rewrite `hn`, the goal using `[RingHom.mem_ker]`. Rewrite `hn` using `[map_pow]`. Conclude with `IsNilpotent.eq_zero ⟨n, hn⟩`.
-/
theorem le_ker {S Y : Scheme.{0}} (Z : TopologicalSpace.Closeds S) (g : Y ⟶ S) [QuasiCompact g]
    [AlgebraicGeometry.IsReduced Y] (h : Set.range g ⊆ Z) :
    Scheme.IdealSheafData.vanishingIdeal Z ≤ g.ker := by
  have h1 : g.ker.support ≤ Z := by
    intro x hx
    have hx' : x ∈ (g.ker.support : Set S) := hx
    rw [Scheme.Hom.support_ker] at hx'
    exact closure_minimal h Z.isClosed hx'
  refine (Scheme.IdealSheafData.vanishingIdeal_antimono h1).trans ?_
  rw [Scheme.IdealSheafData.vanishingIdeal_support]
  intro U s hs
  rw [Scheme.IdealSheafData.radical_ideal] at hs
  rw [Scheme.Hom.ker_apply] at hs ⊢
  obtain ⟨n, hn⟩ := hs
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩

end PositivityTheory.Xgn.IntegralClosedSubscheme

/- English proof (translation)
Introduce `S F hF hirr`. Set `Zc : TopologicalSpace.Closeds S` to `⟨F, hF⟩`. Set `I` to `Scheme.IdealSheafData.vanishingIdeal Zc`. Establish `hrange : Set.range I.subschemeι = F`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`.

Both sides reduce to the same expression. Use `haveI : IsReduced I.subscheme := IntegralClosedSubscheme.reduced_sub Zc`. Use `haveI : IrreducibleSpace I.subscheme := by haveI : IrreducibleSpace (Set.range I.subschemeι) := by`. Rewrite using `[← isIrreducible_iff_irreducibleSpace, hrange]`. Conclude with `hirr`.

Conclude with `I.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this`. Use `haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _`. Use `⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, hrange, ?_⟩` and prove the remaining obligations. Introduce `k _ x hx`. Establish `hsub : Set.range x ⊆ Zc`.

Introduce and unpack `_ ⟨y, rfl⟩`. Establish `hy : y = IsLocalRing.closedPoint k` using `Subsingleton.elim _ _`. Rewrite using `[hy]`. Conclude with `hx`. Use `⟨IsClosedImmersion.lift I.subschemeι x ?_, IsClosedImmersion.lift_fac _ _ _⟩` and prove the remaining obligations.

Rewrite using `[Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `IntegralClosedSubscheme.le_ker Zc x hsub`.
-/
theorem PositivityTheory.Xgn.exists_integral_closed_subscheme_of_irreducible : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x := by
  intro S F hF hirr
  let Zc : TopologicalSpace.Closeds S := ⟨F, hF⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Zc
  have hrange : Set.range I.subschemeι = F := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  haveI : IsReduced I.subscheme := IntegralClosedSubscheme.reduced_sub Zc
  haveI : IrreducibleSpace I.subscheme := by
    haveI : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [← isIrreducible_iff_irreducibleSpace, hrange]
      exact hirr
    exact I.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, hrange, ?_⟩
  intro k _ x hx
  have hsub : Set.range x ⊆ Zc := by
    rintro _ ⟨y, rfl⟩
    have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hy]
    exact hx
  refine ⟨IsClosedImmersion.lift I.subschemeι x ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact IntegralClosedSubscheme.le_ker Zc x hsub
