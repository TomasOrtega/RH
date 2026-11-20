import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverForms

open KaehlerDifferential

/- English proof (translation)
Use `letI : Algebra C B := g.toRingHom.toAlgebra`. Use `haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)`. Establish `hL : ∀ β, L β = KaehlerDifferential.map R R C B β`. Introduce `β`. Establish `hβ : β ∈ Submodule.span C (Set.range (D R C))`.

Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hβ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, rfl⟩` from `hx`.

Rewrite using `[hD, KaehlerDifferential.map_D]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `smul c x _ hx`.

Rewrite using `[hs, hx, (KaehlerDifferential.map R R C B).map_smul]`. Conclude with `algebraMap_smul B c _`. Use `haveI := KaehlerDifferential.isLocalizedModule_map R C B (Submonoid.powers f)`. Establish `h' : KaehlerDifferential.map R R C B α = KaehlerDifferential.map R R C B 0`. Rewrite using `[← hL, h, map_zero]`.

Take `⟨⟨c, hc⟩, hc0⟩` from `IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'`. Take `⟨m, rfl⟩` from `hc`. Use `⟨m, ?_⟩` and prove the remaining obligations. Simplify `hc0` using `[Submonoid.smul_def]`.
-/
theorem exists_pow_smul_eq_zero {R C B : Type} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (g : C →ₐ[R] B) (f : C)
    (hloc : @IsLocalization.Away C _ f B _ g.toRingHom.toAlgebra)
    (L : Ω[C⁄R] →ₗ[R] Ω[B⁄R]) (hD : ∀ c, L (D R C c) = D R B (g c))
    (hs : ∀ (c : C) (α : Ω[C⁄R]), L (c • α) = g c • L α)
    (α : Ω[C⁄R]) (h : L α = 0) : ∃ m : ℕ, f ^ m • α = 0 := by
  letI : Algebra C B := g.toRingHom.toAlgebra
  haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have hL : ∀ β, L β = KaehlerDifferential.map R R C B β := by
    intro β
    have hβ : β ∈ Submodule.span C (Set.range (D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hβ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hD, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx =>
      rw [hs, hx, (KaehlerDifferential.map R R C B).map_smul]
      exact algebraMap_smul B c _
  haveI := KaehlerDifferential.isLocalizedModule_map R C B (Submonoid.powers f)
  have h' : KaehlerDifferential.map R R C B α = KaehlerDifferential.map R R C B 0 := by
    rw [← hL, h, map_zero]
  obtain ⟨⟨c, hc⟩, hc0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
  obtain ⟨m, rfl⟩ := hc
  refine ⟨m, ?_⟩
  simpa [Submonoid.smul_def] using hc0

/- English proof (translation)
Introduce `R _ X s hX`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen) (fun x _ => by`. Take `⟨U, hU, hxU, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)`. Conclude with `Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)`. Use `⟨t.card, fun k => Opposite.op (t.equivFin.symm k).1, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `hcov : ∀ x : X, ∃ U ∈ t, x ∈ (U.1 : Set X)` using `fun x => by`. Simplify using `using ht (Set.mem_univ x)`. Establish `hV0 : ∀ U ∈ t, w.1 (Opposite.op U) = 0` using `fun U hU => by`. Establish `: evForm s (Opposite.op (t.equivFin.symm (t.equivFin ⟨U, hU⟩)).1) w = 0` using `hw _`. Establish `e : t.equivFin.symm (t.equivFin ⟨U, hU⟩) = ⟨U, hU⟩` using `Equiv.symm_apply_apply _ _`.

Rewrite `this` using `[e]`. Conclude with `this`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `W`. Take `⟨W₀⟩` from `W`.

Establish `hW : IsAffineOpen W₀.1` using `W₀.2`. Set `S : Set Γ(X, W₀.1)` to `{f | ∃ U ∈ t, X.basicOpen f ≤ U.1}`. Establish `hS : Ideal.span S = ⊤`. Rewrite using `[← hW.iSup_basicOpen_eq_self_iff]`. Use `le_antisymm (iSup_le fun f => X.basicOpen_le _) ?_` and prove the remaining obligations.

Introduce `x hx`. Take `⟨U, hU, hxU⟩` from `hcov x`. Take `⟨f, hf, hxf⟩` from `hW.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, U, hU, hf⟩, hxf⟩`. Set `α : Ω[Sec s W₀.1⁄R]` to `w.1 (Opposite.op W₀)`.

Set `I : Ideal (Sec s W₀.1)` to `LinearMap.ker (LinearMap.toSpanSingleton (Sec s W₀.1) _ α)`. Establish `hrad : ∀ f ∈ S, f ∈ I.radical`. Introduce and unpack `f ⟨U, hU, hf⟩`. Set `D' : X.affineOpens` to `⟨X.basicOpen f, hW.basicOpen f⟩`. Set `φ : (Opposite.op W₀ : AffOp X) ⟶ Opposite.op D'` to `(homOfLE (X.basicOpen_le f)).op`.

Set `ψ : (Opposite.op U : AffOp X) ⟶ Opposite.op D'` to `(homOfLE hf).op`. Establish `h0 : p1 (OAff s) φ α = 0`. Establish `e1` using `w.2 φ`. Establish `e2` using `w.2 ψ`. Rewrite `e2` using `[hV0 U hU, map_zero]`.

Conclude with `e1.symm.trans e2`. Take `⟨m, hm⟩` from `exists_pow_smul_eq_zero (mp (OAff s) φ) f (hW.isLocalization_basicOpen f) (p1 (OAff s) φ) (p1_D (OAff s) φ) (oneFormsMapOfFunctorMorphism_smul (OAff s) φ) α h0`. Conclude with `⟨m, by simpa [I] using hm⟩`. Establish `hI : I = ⊤`. Rewrite using `[← Ideal.radical_eq_top, eq_top_iff]`.

Establish `h2` using `Ideal.span_le.2 hrad`. Conclude with `(show (⊤ : Ideal (Sec s W₀.1)) ≤ Ideal.span S from hS.ge).trans h2`. Establish `h1 : (1 : Sec s W₀.1) ∈ I` using `hI ▸ Submodule.mem_top`. Simplify `h1` using `[I]`.
-/
theorem eq_zero_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  intro R _ X s hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.card, fun k => Opposite.op (t.equivFin.symm k).1, fun w hw => ?_⟩
  have hcov : ∀ x : X, ∃ U ∈ t, x ∈ (U.1 : Set X) := fun x => by
    simpa using ht (Set.mem_univ x)
  have hV0 : ∀ U ∈ t, w.1 (Opposite.op U) = 0 := fun U hU => by
    have : evForm s (Opposite.op (t.equivFin.symm (t.equivFin ⟨U, hU⟩)).1) w = 0 := hw _
    have e : t.equivFin.symm (t.equivFin ⟨U, hU⟩) = ⟨U, hU⟩ := Equiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  apply Subtype.ext
  funext W
  obtain ⟨W₀⟩ := W
  have hW : IsAffineOpen W₀.1 := W₀.2
  let S : Set Γ(X, W₀.1) := {f | ∃ U ∈ t, X.basicOpen f ≤ U.1}
  have hS : Ideal.span S = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) ?_
    intro x hx
    obtain ⟨U, hU, hxU⟩ := hcov x
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, U, hU, hf⟩, hxf⟩
  let α : Ω[Sec s W₀.1⁄R] := w.1 (Opposite.op W₀)
  let I : Ideal (Sec s W₀.1) := LinearMap.ker (LinearMap.toSpanSingleton (Sec s W₀.1) _ α)
  have hrad : ∀ f ∈ S, f ∈ I.radical := by
    rintro f ⟨U, hU, hf⟩
    let D' : X.affineOpens := ⟨X.basicOpen f, hW.basicOpen f⟩
    let φ : (Opposite.op W₀ : AffOp X) ⟶ Opposite.op D' := (homOfLE (X.basicOpen_le f)).op
    let ψ : (Opposite.op U : AffOp X) ⟶ Opposite.op D' := (homOfLE hf).op
    have h0 : p1 (OAff s) φ α = 0 := by
      have e1 := w.2 φ
      have e2 := w.2 ψ
      rw [hV0 U hU, map_zero] at e2
      exact e1.symm.trans e2
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero (mp (OAff s) φ) f
      (hW.isLocalization_basicOpen f) (p1 (OAff s) φ) (p1_D (OAff s) φ) (oneFormsMapOfFunctorMorphism_smul (OAff s) φ) α h0
    exact ⟨m, by simpa [I] using hm⟩
  have hI : I = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff]
    have h2 := Ideal.span_le.2 hrad
    exact (show (⊤ : Ideal (Sec s W₀.1)) ≤ Ideal.span S from hS.ge).trans h2
  have h1 : (1 : Sec s W₀.1) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end GlobalTheory.CoverForms
