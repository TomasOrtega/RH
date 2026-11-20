import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

open scoped ComplexOrder in

/- English proof (translation)
Use `letI : NormedAddCommGroup V := core.toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore`. Establish `hp` using `(Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv).det_pos`. Establish `hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b)`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite `hp` using `[hG]`. Conclude with `hp.ne'`.
-/
theorem core_gram_det_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).det ≠ 0 := by
  letI : NormedAddCommGroup V := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := (Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv).det_pos
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp.ne'

/- English proof (translation)
Take `⟨hz, v, ⟨hv, -⟩, hw⟩` from `h`. Establish `e1 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) = Spec.map (Scheme.stalkClosedPointTo z) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (centre z)) (X.preshe …`. Establish `a : CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom = CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z))).toRingHom ≫ Scheme.sta …`. Use `CommRingCat.hom_ext (RingHom.ext fun x => ?_)` and prove the remaining obligations. Use `show TrivSqZeroExt.fst (dualMap (Scheme.stalkClosedPointTo z).hom x) = (Scheme.stalkClosedPointTo z).hom (TrivSqZeroExt.fst x)`.

Simplify using `[dualMap]`. Conclude with `(Spec.map_comp _ _).symm.trans ((congrArg Spec.map a).trans (Spec.map_comp _ _))`. Set `f : Over.mk z ⟶ Over.mk (X.fromSpecStalk (centre z))` to `Over.homMk (Spec.map (Scheme.stalkClosedPointTo z)) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)`. Establish `e2 : f ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) = 1` using `MonObj.comp_one f`. Unfold `IsTanAt at hv ⊢`.

Rewrite using `[hw]`. Use `(Category.assoc _ _ _).symm.trans ((e1 =≫ v.left).trans ((Category.assoc _ _ _).trans ?_))` and prove the remaining obligations. Use `(congrArg (fun k => Spec.map (Scheme.stalkClosedPointTo z) ≫ k) hv).trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun k => k.left) e2`.
-/
theorem isTanAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {e : Li} {w : epsAt z ⟶ G} (h : M.ValAt z e w) : IsTanAt G z w := by
  obtain ⟨hz, v, ⟨hv, -⟩, hw⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) =
      Spec.map (Scheme.stalkClosedPointTo z) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z))).toRingHom) := by
    have a : CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z))).toRingHom ≫
          Scheme.stalkClosedPointTo z := by
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      show TrivSqZeroExt.fst (dualMap (Scheme.stalkClosedPointTo z).hom x) = (Scheme.stalkClosedPointTo z).hom (TrivSqZeroExt.fst x)
      simp [dualMap]
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map a).trans (Spec.map_comp _ _))
  let f : Over.mk z ⟶ Over.mk (X.fromSpecStalk (centre z)) :=
    Over.homMk (Spec.map (Scheme.stalkClosedPointTo z)) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)
  have e2 : f ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) = 1 := MonObj.comp_one f
  unfold IsTanAt at hv ⊢
  rw [hw]
  refine (Category.assoc _ _ _).symm.trans ((e1 =≫ v.left).trans ((Category.assoc _ _ _).trans ?_))
  refine (congrArg (fun k => Spec.map (Scheme.stalkClosedPointTo z) ≫ k) hv).trans ?_
  exact congrArg (fun k => k.left) e2

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB in

/- English proof (translation)
Introduce `X Ω _ ξ K J y G _ _ _ Li _ _ M h z hz r b π B hξ hπ hreg hB n ix hix`. Take `⟨Vz, _, _, ⟨MR⟩⟩` from `lieModel_exists X G ℂ z`. Establish `htan : ∀ j, IsTanAt G z (B j)` using `fun j => isTanAt_of_valAt (hB j)`. Use `choose β hβ using fun j => MR.onto (B j) (htan j)`. Use `choose g hg using fun j => GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M ℂ z hz Vz MR (π j) hξ (hreg j)`.

Establish `hd : ∀ j l, g j (β l) = if j = l then 1 else 0`. Introduce `j l`. Use `hg j (b l) (β l) _ (by rw [hβ]; exact hB l) ?_` and prove the remaining obligations. Rewrite using `[hπ j l]`. Use `split_ifs`.

Conclude with `val_one hz`. Conclude with `val_zero hz`. Establish `hli : LinearIndependent ℂ β`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc j`.

Use `congrArg (g j) hc` as an intermediate fact. Simplify `this` using `[map_sum, hd]`. Take `⟨core, hcore⟩` from `h.herm z Vz MR`. Establish `key` using `core_gram_det_ne_zero core (β ∘ ix) (hli.comp ix hix)`. Establish `hm : (gramAt h z fun l => B (ix l)) = Matrix.of fun a b => core.inner ((β ∘ ix) a) ((β ∘ ix) b)`.

Use extensionality with `a c`. Simplify using `[gramAt, hcore, hβ]`. Rewrite using `[hm]`. Conclude with `key`.
-/
theorem GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (n : ℕ) (ix : Fin n → Fin r), Function.Injective ix → (gramAt h z fun l => B (ix l)).det ≠ 0 := by
  intro X Ω _ ξ K J y G _ _ _ Li _ _ M h z hz r b π B hξ hπ hreg hB n ix hix
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ z
  have htan : ∀ j, IsTanAt G z (B j) := fun j => isTanAt_of_valAt (hB j)
  choose β hβ using fun j => MR.onto (B j) (htan j)
  choose g hg using fun j => GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M ℂ z hz Vz MR (π j) hξ (hreg j)
  have hd : ∀ j l, g j (β l) = if j = l then 1 else 0 := by
    intro j l
    refine hg j (b l) (β l) _ (by rw [hβ]; exact hB l) ?_
    rw [hπ j l]
    split_ifs
    · exact val_one hz
    · exact val_zero hz
  have hli : LinearIndependent ℂ β := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := congrArg (g j) hc
    simpa [map_sum, hd] using this
  obtain ⟨core, hcore⟩ := h.herm z Vz MR
  have key := core_gram_det_ne_zero core (β ∘ ix) (hli.comp ix hix)
  have hm : (gramAt h z fun l => B (ix l)) = Matrix.of fun a b => core.inner ((β ∘ ix) a) ((β ∘ ix) b) := by
    ext a c
    simp [gramAt, hcore, hβ]
  rw [hm]
  exact key
