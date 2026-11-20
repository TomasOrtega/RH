import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FramesEig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open LieTangent

section Germ

variable {X : Scheme.{0}} {O : Type} [CommRing O]

def germ (s : X ⟶ Sp O) (p : X) : O →+* X.presheaf.stalk p :=
  (Spec.preimage (X.fromSpecStalk p ≫ s)).hom

/- English proof (translation)
Simplify using `only [germ, CommRingCat.ofHom_hom, Spec.map_preimage]`.
-/
theorem spec_germ (s : X ⟶ Sp O) (p : X) :
    Spec.map (CommRingCat.ofHom (germ s p)) = X.fromSpecStalk p ≫ s := by
  simp only [germ, CommRingCat.ofHom_hom, Spec.map_preimage]

/- English proof (translation)
Establish `h3 : Spec.map (CommRingCat.ofHom (φ.comp (germ s p))) = Spec.map (CommRingCat.ofHom i)`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, spec_germ]`. Conclude with `h`. Establish `h4` using `Spec.map_injective h3`. Conclude with `congrArg (fun g => g.hom n) h4`.
-/
theorem map_germ (s : X ⟶ Sp O) (p : X) {K : Type} [CommRing K] (φ : X.presheaf.stalk p →+* K) (i : O →+* K)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p ≫ s = spMap i) (n : O) :
    φ (germ s p n) = i n := by
  have h3 : Spec.map (CommRingCat.ofHom (φ.comp (germ s p))) = Spec.map (CommRingCat.ofHom i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_germ]
    exact h
  have h4 := Spec.map_injective h3
  exact congrArg (fun g => g.hom n) h4

end Germ

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

/- English proof (translation)
Rewrite `*` using `[LieModel.valAt_iff]`. Take `⟨h1, v, hv, rfl⟩` from `h`. Use `⟨h1, v ≫ f, ?_, by rw [Category.assoc]⟩` and prove the remaining obligations. Rewrite `*` using `[LieModel.extends_iff]`. Use `⟨?_, by rw [he, hv.2, Category.assoc]⟩` and prove the remaining obligations.

Use `(isTanAt_iff v).1 hv.1` as an intermediate fact. Rewrite using `[isTanAt_iff, ← Category.assoc, this, one_comp]`.
-/
theorem valAt_comp (M : LieModel G ξ V) {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (f : G ⟶ G) [IsMonHom f] {e e' : V} (he : M.pt e' = M.pt e ≫ f)
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z e' (w ≫ f) := by
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨h1, v ≫ f, ?_, by rw [Category.assoc]⟩
  rw [LieModel.extends_iff] at *
  refine ⟨?_, by rw [he, hv.2, Category.assoc]⟩
  have := (isTanAt_iff v).1 hv.1
  rw [isTanAt_iff, ← Category.assoc, this, one_comp]

end Val

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y U Z σ y EC _ _ N ρ t e w hfr hy hN he hv`. Establish `mem : ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (r : 𝓞 E →+* Module.End R V) (τ : 𝓞 E →+* R) (u : V), u ∈ eigSp r τ ↔ ∀ a, r a u = τ a • u`. Introduce `R V _ _ _ r τ u`. Simplify using `[eigSp, Submodule.mem_iInf, sub_eq_zero]`. Rewrite `he`, the goal using `[mem]`.

Establish `h1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap β` using `by show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`. Establish `hh` using `hv`. Rewrite `hh` using `[LieModel.valAt_iff]`. Take `⟨h0, -⟩` from `hh`.

Establish `hgen : ∀ n, genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h0⟩ (germ Y.s (centre (y ≫ Y.j)) n) = Z.inc (β n)`. Introduce `n`. Use `map_germ Y.s _ _ (Z.inc.comp β) ?_ n` and prove the remaining obligations. Rewrite using `[← Category.assoc, spec_genMap, Category.assoc, h1, ← Category.assoc, Z.over_inc]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Establish `hcl : ∀ n, (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (germ Y.s (centre (y ≫ Y.j)) n) = σ (β n)`. Introduce `n`. Use `map_germ Y.s _ _ (σ.comp β) ?_ n` and prove the remaining obligations. Use `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.s) (spec_centre (y ≫ Y.j))).trans ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(y ≫ Y.j) ≫ Y.s = _`.

Rewrite using `[Category.assoc, h1, ← Category.assoc, hy]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Introduce `a`. Take `⟨n, d, hd, hnd⟩` from `hfr (t a)`. Establish `hva : Z.M.ValAt (y ≫ Y.j) (Z.ρ a e) (N.pt (ρ a w))`.

Use `Y.t.act.hom a` as an intermediate fact. Rewrite using `[hN a w]`. Conclude with `valAt_comp Z.M (Y.t.act.act a) (Z.act a e) hv`. Establish `v1` using `hva.smul h0 (germ Y.s (centre (y ≫ Y.j)) d)`. Establish `v2` using `hv.smul h0 (germ Y.s (centre (y ≫ Y.j)) n)`.

Rewrite `v1`, `v2` using `[hgen, hcl, ← LieModel.pt_smul]`. Establish `e1 : Z.inc (β d) • Z.ρ a e = Z.inc (β n) • e`. Rewrite using `[he a, smul_smul, ← hnd]`. Simplify using `[mul_comm]`. Rewrite `v1` using `[e1]`.

Establish `e2` using `N.inj (v1.unique Z.gen v2)`. Rewrite `e2` using `[← hnd, map_mul, mul_comm, mul_smul]`. Establish `hσ : σ (β d) ≠ 0` using `(map_ne_zero σ).2 hd`. Conclude with `smul_right_injective EC hσ e2`.
-/
theorem mem_eigSp_of_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (EC : Type) [AddCommGroup EC] [Module ℂ EC] (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC) (t : 𝓞 E →+* c.F) (e : Z.V) (w : EC), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap σ → N.IsActOf Y.t.act.act ρ → e ∈ eigSp Z.ρ (Z.inc.comp t) → Z.M.ValAt (y ≫ Y.j) e (N.pt w) → w ∈ eigSp ρ (σ.comp t) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z σ y EC _ _ N ρ t e w hfr hy hN he hv
  have mem : ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (r : 𝓞 E →+* Module.End R V)
      (τ : 𝓞 E →+* R) (u : V), u ∈ eigSp r τ ↔ ∀ a, r a u = τ a • u := by
    intro R V _ _ _ r τ u
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [mem] at he ⊢
  have h1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hh := hv
  rw [LieModel.valAt_iff] at hh
  obtain ⟨h0, -⟩ := hh
  have hgen : ∀ n, genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h0⟩ (germ Y.s (centre (y ≫ Y.j)) n) = Z.inc (β n) := by
    intro n
    refine map_germ Y.s _ _ (Z.inc.comp β) ?_ n
    rw [← Category.assoc, spec_genMap, Category.assoc, h1, ← Category.assoc, Z.over_inc]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcl : ∀ n, (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (germ Y.s (centre (y ≫ Y.j)) n) = σ (β n) := by
    intro n
    refine map_germ Y.s _ _ (σ.comp β) ?_ n
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.s) (spec_centre (y ≫ Y.j))).trans ?_)
    change (y ≫ Y.j) ≫ Y.s = _
    rw [Category.assoc, h1, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  intro a
  obtain ⟨n, d, hd, hnd⟩ := hfr (t a)
  have hva : Z.M.ValAt (y ≫ Y.j) (Z.ρ a e) (N.pt (ρ a w)) := by
    have := Y.t.act.hom a
    rw [hN a w]
    exact valAt_comp Z.M (Y.t.act.act a) (Z.act a e) hv
  have v1 := hva.smul h0 (germ Y.s (centre (y ≫ Y.j)) d)
  have v2 := hv.smul h0 (germ Y.s (centre (y ≫ Y.j)) n)
  rw [hgen, hcl, ← LieModel.pt_smul] at v1 v2
  have e1 : Z.inc (β d) • Z.ρ a e = Z.inc (β n) • e := by
    rw [he a, smul_smul, ← hnd]
    simp [mul_comm]
  rw [e1] at v1
  have e2 := N.inj (v1.unique Z.gen v2)
  rw [← hnd, map_mul, mul_comm, mul_smul] at e2
  have hσ : σ (β d) ≠ 0 := (map_ne_zero σ).2 hd
  exact smul_right_injective EC hσ e2

end GlobalTheory.CompanionTheory.Ar.FramesEig
