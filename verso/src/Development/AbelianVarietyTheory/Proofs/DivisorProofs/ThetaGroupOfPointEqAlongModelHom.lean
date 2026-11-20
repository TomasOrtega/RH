import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.HHFibre

open GlobalTheory.ZH GlobalTheory.ZH.RatModel

/- English proof (translation)
Use `show Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt`. Rewrite using `[hq]`. Establish `: spMap (AlgHom.id o Ω).toRingHom = 𝟙 _` using `by show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _`. Rewrite using `[← Spec.map_id]`. Both sides reduce to the same expression.

Rewrite using `[this, Category.id_comp]`.
-/
theorem isHom_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {q : Y.Z ⟶ M.Z}
    (hq : Y.pt ≫ q = M.pt) : M.IsHom Y (AlgHom.id o Ω) q := by
  show Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt
  rw [hq]
  have : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _
    rw [← Spec.map_id]; rfl
  rw [this, Category.id_comp]

/- English proof (translation)
Assemble the required witnesses or components as `⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply _ _⟩`.
-/
theorem exists_pt (X : Scheme.{0}) (w : X) : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X),
    y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply _ _⟩

/- English proof (translation)
Take `⟨K, _, y, hy0⟩` from `exists_pt Y.Z w`. Establish `hy : Set.range y = {w}` using `hy0 ▸ range_eq_singleton y (IsLocalRing.closedPoint K)`. Establish `hyq : Set.range (y ≫ q) = {q w}`. Use `range_eq_singleton (y ≫ q) (IsLocalRing.closedPoint K)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Rewrite using `[← hy0]`. Both sides reduce to the same expression. Rewrite using `[← val_ne_zero_iff hyq]`. Rewrite `hu` using `[← val_ne_zero_iff hy]`. Establish `ha2 : a ∈ M.O (q (y (IsLocalRing.closedPoint K)))` using `by rw [hy0]; exact ha`.

Establish `e` using `hq.val_comp y (IsLocalRing.closedPoint K) ha2`. Simplify using `only [AlgHom.id_apply] at e`. Use `show M.val (y ≫ q) a ≠ 0`. Rewrite using `[e]`. Conclude with `hu`.
-/
theorem isUnit_of_isUnit_comap {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω}
    {q : Y.Z ⟶ M.Z} (hq : M.IsHom Y (AlgHom.id o Ω) q) (w : Y.Z) {a : Ω} (ha : a ∈ M.O (q w))
    (ha' : a ∈ Y.O w) (hu : IsUnit (⟨a, ha'⟩ : Y.O w)) : IsUnit (⟨a, ha⟩ : M.O (q w)) := by
  obtain ⟨K, _, y, hy0⟩ := exists_pt Y.Z w
  have hy : Set.range y = {w} := hy0 ▸ range_eq_singleton y (IsLocalRing.closedPoint K)
  have hyq : Set.range (y ≫ q) = {q w} := by
    have := range_eq_singleton (y ≫ q) (IsLocalRing.closedPoint K)
    refine this.trans ?_
    rw [← hy0]
    rfl
  rw [← val_ne_zero_iff hyq]
  rw [← val_ne_zero_iff hy] at hu
  have ha2 : a ∈ M.O (q (y (IsLocalRing.closedPoint K))) := by rw [hy0]; exact ha
  have e := hq.val_comp y (IsLocalRing.closedPoint K) ha2
  simp only [AlgHom.id_apply] at e
  show M.val (y ≫ q) a ≠ 0
  rw [e]
  exact hu

/- English proof (translation)
Introduce `o Ω _ _ _ S M Y q hq hdiv w`. Establish `hh` using `isHom_of_pt hq`. Unfold `ThetaSys.HH`. Use `congr 1`. Use extensionality with `x`.

Simplify using `only [ThetaSys.supI, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨x₀, h₀⟩` from `hdiv (q w)`. Establish `h₀' : Y.Div S.th x₀ w` using `by simpa using hh.div h₀`.

Rewrite using `[h₀.div_iff_isUnit]`. Conclude with `isUnit_of_isUnit_comap hh w _ _ ((h₀'.div_iff_isUnit x).1 hx)`. Introduce `hx`. Simplify using `using hh.div hx`.
-/
theorem HH_eq_of_hom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M Y : RatModel o Ω)
    (q : Y.Z ⟶ M.Z), Y.pt ≫ q = M.pt → M.HasDiv S.th → ∀ w : Y.Z, S.HH Y w = S.HH M (q w) := by
  intro o Ω _ _ _ S M Y q hq hdiv w
  have hh := isHom_of_pt hq
  unfold ThetaSys.HH
  congr 1
  ext x
  simp only [ThetaSys.supI, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨x₀, h₀⟩ := hdiv (q w)
    have h₀' : Y.Div S.th x₀ w := by simpa using hh.div h₀
    rw [h₀.div_iff_isUnit]
    exact isUnit_of_isUnit_comap hh w _ _ ((h₀'.div_iff_isUnit x).1 hx)
  · intro hx
    simpa using hh.div hx

end GlobalTheory.Poinc.HHFibre
