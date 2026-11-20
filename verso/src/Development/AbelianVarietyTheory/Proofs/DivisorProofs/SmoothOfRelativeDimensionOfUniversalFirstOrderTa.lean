import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKaehlerEqOfUniversalTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothDimTangent

/- English proof (translation)
Introduce `B _ X s d hs H`. Establish `loc : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧ SmoothOfRelativeDimension d (W.ι ≫ s)`. Introduce `p`. Take `⟨U, hU, V, hV, hx, e, h⟩` from `Smooth.exists_isStandardSmooth s p`. Set `_` to `(s.appLE U V e).hom.toAlgebra`.

Establish `: Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V)` using `h`. Take `⟨_, _, _, _, ⟨P⟩⟩` from `this`. Establish `hP : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp B, U) Γ(X, V)` using `⟨_, _, _, ‹_›, P, rfl⟩`. Set `k` to `AlgebraicClosure (X.residueField p)`. Set `x : Sp k ⟶ X` to `spMap (algebraMap (X.residueField p) k) ≫ X.fromSpecResidueField p`.

Establish `hr : Set.range x.base ⊆ (V : Set X)`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `: x.base y ∈ Set.range (X.fromSpecResidueField p).base` using `⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩`. Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Rewrite using `[Set.mem_singleton_iff.1 this]`.

Conclude with `hx`. Take `⟨φ, ψ, h1, h2, h3⟩` from `GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections B X s U V hU hV e d k x hr (H k x)`. Establish `: Nontrivial Γ(X, V)` using `φ.domain_nontrivial`. Establish `: Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V)` using `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth P.dimension`. Establish `: Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Sp B, U)]` using `Algebra.IsStandardSmooth.free_kaehlerDifferential`.

Establish `hrank : Module.finrank Γ(X, V) (Ω[Γ(X, V)⁄Γ(Sp B, U)]) = P.dimension` using `Module.finrank_eq_of_rank_eq hP.rank_kaehlerDifferential`. Establish `hd : d = P.dimension` using `GlobalTheory.T.eq_of_universal_tangent_dualNumber _ _ k P.dimension d hrank φ ψ h1 h2 h3`. Establish `h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (s.appLE U V e).hom` using `hP`. Establish `: IsAffine U` using `hU`. Establish `: IsAffine V` using `hV`.

Establish `: SmoothOfRelativeDimension P.dimension (s.resLE U V e)` using `(HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2 (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso s U V e)).2 h'))`. Establish `: SmoothOfRelativeDimension (P.dimension + 0) (V.ι ≫ s)`. Rewrite using `[← Scheme.Hom.resLE_comp_ι s e]`. Use `infer_instance`. Use `⟨V, hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[hd]`. Conclude with `this`. Use `choose W hW hd using loc`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension d)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Conclude with `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd`.
-/
theorem smoothOfRelativeDimension_of_universal_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  intro B _ X s d hs H
  have loc : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧ SmoothOfRelativeDimension d (W.ι ≫ s) := by
    intro p
    obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth s p
    let _ := (s.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := h
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    have hP : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp B, U) Γ(X, V) := ⟨_, _, _, ‹_›, P, rfl⟩
    let k := AlgebraicClosure (X.residueField p)
    let x : Sp k ⟶ X := spMap (algebraMap (X.residueField p) k) ≫ X.fromSpecResidueField p
    have hr : Set.range x.base ⊆ (V : Set X) := by
      rintro _ ⟨y, rfl⟩
      have : x.base y ∈ Set.range (X.fromSpecResidueField p).base := ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
      rw [Scheme.range_fromSpecResidueField] at this
      rw [Set.mem_singleton_iff.1 this]
      exact hx
    obtain ⟨φ, ψ, h1, h2, h3⟩ := GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections B X s U V hU hV e d k x hr (H k x)
    have : Nontrivial Γ(X, V) := φ.domain_nontrivial
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth P.dimension
    have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Sp B, U)] := Algebra.IsStandardSmooth.free_kaehlerDifferential
    have hrank : Module.finrank Γ(X, V) (Ω[Γ(X, V)⁄Γ(Sp B, U)]) = P.dimension :=
      Module.finrank_eq_of_rank_eq hP.rank_kaehlerDifferential
    have hd : d = P.dimension := GlobalTheory.T.eq_of_universal_tangent_dualNumber _ _ k P.dimension d hrank φ ψ h1 h2 h3
    have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (s.appLE U V e).hom := hP
    have : IsAffine U := hU
    have : IsAffine V := hV
    have : SmoothOfRelativeDimension P.dimension (s.resLE U V e) :=
      (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
          ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso s U V e)).2 h'))
    have : SmoothOfRelativeDimension (P.dimension + 0) (V.ι ≫ s) := by
      rw [← Scheme.Hom.resLE_comp_ι s e]; infer_instance
    refine ⟨V, hx, ?_⟩
    rw [hd]; exact this
  choose W hW hd using loc
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd

end GlobalTheory.SmoothDimTangent
