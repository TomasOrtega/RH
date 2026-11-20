import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyOfHomsStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsDomainAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart

abbrev cst {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) (V : X.Opens) : K →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)).hom

/- English proof (translation)
Use `hV.isLocalization_basicOpen g` as an intermediate fact. Establish `h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen g)).IsStandardSmoothOfRelativeDimension 0` using `RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g`. Establish `h3` using `h1.comp h`. Rewrite `h3` using `[zero_add]`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `c`. Conclude with `congr($(Scheme.Hom.appLE_map s (U := ⊤) (V := V) le_top (homOfLE (X.basicOpen_le g)).op) ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)).symm`.
-/
theorem cst_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {V : X.Opens}
    (hV : IsAffineOpen V) {d : ℕ} (h : (cst s V).IsStandardSmoothOfRelativeDimension d)
    (g : Γ(X, V)) : (cst s (X.basicOpen g)).IsStandardSmoothOfRelativeDimension d := by
  have := hV.isLocalization_basicOpen g
  have h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
  have h3 := h1.comp h
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact congr($(Scheme.Hom.appLE_map s (U := ⊤) (V := V) le_top (homOfLE (X.basicOpen_le g)).op)
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)).symm

/- English proof (translation)
Take `⟨W, -, V, hV, hxV, e, hf⟩` from `hs.exists_isStandardSmoothOfRelativeDimension x`. Choose the witnesses or unpack the hypotheses as in `rfl : W = ⊤ := by`. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Establish `: y = s x` using `Subsingleton.elim (α := PrimeSpectrum K) _ _`. Rewrite using `[this]`.

Conclude with `e hxV`. Take `⟨g, hgU, hxg⟩` from `hV.exists_basicOpen_le ⟨x, hx⟩ hxV`. Use `⟨X.basicOpen g, hV.basicOpen g, hgU, hxg, cst_basicOpen s hV ?_ g⟩` and prove the remaining obligations. Conclude with `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv hf`.
-/
theorem exists_std {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {d : ℕ}
    (hs : SmoothOfRelativeDimension d s) (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ V ≤ U ∧ x ∈ V ∧
      (cst s V).IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨W, -, V, hV, hxV, e, hf⟩ := hs.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : W = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = s x := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact e hxV
  obtain ⟨g, hgU, hxg⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨X.basicOpen g, hV.basicOpen g, hgU, hxg, cst_basicOpen s hV ?_ g⟩
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv hf

/- English proof (translation)
Establish `h` using `IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Sp K)) hV (fun _ _ => trivial)`. Rewrite using `[← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem fromSpec_comp {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {V : X.Opens}
    (hV : IsAffineOpen V) : hV.fromSpec ≫ s = spMap (cst s V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Sp K)) hV (fun _ _ => trivial)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYde8.main hV ξ hξ`.
-/
theorem exists_domain {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(X, V)] (ξ : X) (hξ : ξ ∈ V) [IsDomain (X.presheaf.stalk ξ)] :
    ∃ f : Γ(X, V), ξ ∈ X.basicOpen f ∧ IsDomain Γ(X, X.basicOpen f) :=
  _root_.UpperTheory.Reformulated.B.DYde8.main hV ξ hξ

end GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart

open GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart in

/- English proof (translation)
Introduce `K _ σ X s d hsm x W₀ hxs hW hdom`. Establish `hξW : centre x ∈ W₀` using `hW (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)`. Take `⟨V₁, hV₁, hV₁W, hξ₁, hstd₁⟩` from `exists_std s hsm W₀ (centre x) hξW`. Establish `hnoeth : IsNoetherianRing Γ(X, V₁)`. Use `letI := (cst s V₁).toAlgebra`.

Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, V₁) := hstd₁`. Use `haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := Γ(X, V₁)) d`. Conclude with `Algebra.FiniteType.isNoetherianRing K _`. Take `⟨f, hξ, hdomV⟩` from `exists_domain hV₁ (centre x) hξ₁`. Establish `hV : IsAffineOpen (X.basicOpen f)` using `hV₁.basicOpen f`.

Establish `hstd` using `cst_basicOpen s hV₁ hstd₁ f`. Use `letI := (cst s (X.basicOpen f)).toAlgebra`. Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, X.basicOpen f) := hstd`. Establish `hrange : Set.range x ⊆ Set.range hV.fromSpec`. Rewrite using `[hV.range_fromSpec]`.

Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Subsingleton.elim p (IsLocalRing.closedPoint ℂ)]`. Conclude with `hξ`. Set `y` to `IsOpenImmersion.lift hV.fromSpec x hrange`. Establish `hy : y ≫ hV.fromSpec = x` using `IsOpenImmersion.lift_fac _ _ _`.

Set `ψ₀ : Γ(X, X.basicOpen f) →+* ℂ` to `(Spec.preimage y).hom`. Establish `hψ₀ : spMap ψ₀ ≫ hV.fromSpec = x`. Rewrite using `[← hy]`. Use `congr 1`. Conclude with `Spec.map_preimage y`.

Establish `hcomp : ∀ ψ : Γ(X, X.basicOpen f) →+* ℂ, (spMap ψ ≫ hV.fromSpec) ≫ s = spMap (ψ.comp (cst s (X.basicOpen f)))`. Introduce `ψ`. Rewrite using `[Category.assoc, fromSpec_comp s hV, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hσ : ψ₀.comp (algebraMap K Γ(X, X.basicOpen f)) = σ`.

Establish `h` using `hcomp ψ₀`. Rewrite `h` using `[hψ₀, hxs]`. Establish `h'` using `Spec.map_injective h`. Conclude with `(congrArg CommRingCat.Hom.hom h').symm`. Take `⟨Ψ, hol, h0, hbase, hvan⟩` from `GlobalTheory.T.holomorphic_family_of_homs K Γ(X, X.basicOpen f) d σ ψ₀ hσ`.

Use `⟨X.basicOpen f, hV, Ψ, (X.basicOpen_le f).trans hV₁W, hol, ?_, ?_, hvan⟩` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `hψ₀`. Introduce `z hz`. Rewrite using `[hcomp, ← hbase z hz]`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart.exists_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (x : Sp ℂ ⟶ X) (W₀ : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W₀ → IsDomain (X.presheaf.stalk (centre x)) → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W₀ ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, (spMap (ψ z) ≫ hV.fromSpec) ≫ s = spMap σ) ∧ ∀ g : Γ(X, V), (∀ z ∈ ball (0 : Fin d → ℂ) 1, ψ z g = 0) → g = 0 := by
  intro K _ σ X s d hsm x W₀ hxs hW hdom
  have hξW : centre x ∈ W₀ := hW (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨V₁, hV₁, hV₁W, hξ₁, hstd₁⟩ := exists_std s hsm W₀ (centre x) hξW
  have hnoeth : IsNoetherianRing Γ(X, V₁) := by
    letI := (cst s V₁).toAlgebra
    haveI : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, V₁) := hstd₁
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := Γ(X, V₁)) d
    exact Algebra.FiniteType.isNoetherianRing K _
  obtain ⟨f, hξ, hdomV⟩ := exists_domain hV₁ (centre x) hξ₁
  have hV : IsAffineOpen (X.basicOpen f) := hV₁.basicOpen f
  have hstd := cst_basicOpen s hV₁ hstd₁ f
  letI := (cst s (X.basicOpen f)).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, X.basicOpen f) := hstd
  have hrange : Set.range x ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint ℂ)]
    exact hξ
  let y := IsOpenImmersion.lift hV.fromSpec x hrange
  have hy : y ≫ hV.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  let ψ₀ : Γ(X, X.basicOpen f) →+* ℂ := (Spec.preimage y).hom
  have hψ₀ : spMap ψ₀ ≫ hV.fromSpec = x := by
    rw [← hy]
    congr 1
    exact Spec.map_preimage y
  have hcomp : ∀ ψ : Γ(X, X.basicOpen f) →+* ℂ,
      (spMap ψ ≫ hV.fromSpec) ≫ s = spMap (ψ.comp (cst s (X.basicOpen f))) := by
    intro ψ
    rw [Category.assoc, fromSpec_comp s hV, ← Spec.map_comp]
    rfl
  have hσ : ψ₀.comp (algebraMap K Γ(X, X.basicOpen f)) = σ := by
    have h := hcomp ψ₀
    rw [hψ₀, hxs] at h
    have h' := Spec.map_injective h
    exact (congrArg CommRingCat.Hom.hom h').symm
  obtain ⟨Ψ, hol, h0, hbase, hvan⟩ := GlobalTheory.T.holomorphic_family_of_homs K Γ(X, X.basicOpen f) d σ ψ₀ hσ
  refine ⟨X.basicOpen f, hV, Ψ, (X.basicOpen_le f).trans hV₁W, hol, ?_, ?_, hvan⟩
  · rw [h0]; exact hψ₀
  · intro z hz
    rw [hcomp, ← hbase z hz]
