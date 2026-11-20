import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAbPullApp
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

namespace GlobalTheory

/- English proof (translation)
Introduce `T T' f ι κ _ _ _ _ V U V' U' τ hτ hc hc' hV F G φ hF hG x y hy`. Take `⟨s, hs⟩` from `(cechAbHZeroEquiv F.property hc).symm.surjective (cechClass _ 0 x)`. Rewrite `hs` using `[cechAbHZeroEquiv_symm_apply]`. Establish `h1 : cechClass (cechAbCube F.obj V U) 0 ⟨presheafCechAug (F.obj ⋙ abToIntModule) V U s, LinearMap.mem_ker.2 (d_presheafCechAug (F.obj ⋙ abToIntModule) V U s)⟩ = cechClass _ 0 x` using `(presheafToCechH_apply (F.obj ⋙ abToIntModule) V U s).symm.trans hs`. Establish `hx : x.1 = presheafCechAug (F.obj ⋙ abToIntModule) V U s` using `(congrArg Subtype.val ((cechClass_zero_bijective _).1 h1)).symm`.

Take `⟨s'', hs''⟩ : ∃ s'', s'' = G.obj.map (homOfLE hV).op (φ.hom.app (op V) s)` from `⟨_, rfl⟩`. Establish `hy' : y.1 = presheafCechAug (G.obj ⋙ abToIntModule) V' U' s''`. Use function extensionality and compare the values at `t`. Take `⟨t, ht⟩` from `t`. Take `⟨k, rfl⟩` from `Finset.card_eq_one.1 ht`.

Rewrite using `[hy, Cube.PullHom.term_apply_of_injOn _ _ _ (by simp)]`. Establish `hsg : PD.sortSign τ {k} = 1` using `by simp [PD.sortSign]`. Rewrite using `[hsg, one_smul]`. Use `show G.obj.map (homOfLE (hτ {k})).op (φ.hom.app (op (cechOpen V U (({k} : Finset κ).image τ))) (x.1 ⟨({k} : Finset κ).image τ, Cube.PullHom.card_image ⟨{k}, ht⟩ (by simp)⟩)) = G.obj.map (homOfLE (cechOpen_le V' U' {k})).op s''`. Rewrite using `[hx, hs'']`.

Establish `nat` using `ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op) s`. Express the relevant statement in the definitionally equal form `φ.hom.app _ (F.obj.map _ s) = G.obj.map _ (φ.hom.app _ s) at nat`. Express the relevant statement in the definitionally equal form `G.obj.map _ (φ.hom.app _ (F.obj.map (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op s)) = _`. Rewrite using `[nat]`. Use `(ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _))` and prove the remaining obligations.

Both sides reduce to the same expression. Establish `h2 : cechClass _ 0 y = toCechAbH G.obj V' U' s''` using `(congrArg (cechClass _ 0) (Subtype.ext hy')).trans (presheafToCechH_apply (G.obj ⋙ abToIntModule) V' U' s'').symm`. Rewrite using `[h2, ← hs, cechAbHEquivH'_toCechAbH, cechAbHEquivH'_toCechAbH]`. Apply `(SheafLES.equivZero G V').injective` to reduce the goal to its premises. Rewrite using `[AddEquiv.apply_symm_apply, SheafPull.equivZero_pull, AddEquiv.apply_symm_apply, hs'']`.
-/
theorem cechAbPull_degZero : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  intro T T' f ι κ _ _ _ _ V U V' U' τ hτ hc hc' hV F G φ hF hG x y hy
  obtain ⟨s, hs⟩ := (cechAbHZeroEquiv F.property hc).symm.surjective (cechClass _ 0 x)
  rw [cechAbHZeroEquiv_symm_apply] at hs
  have h1 : cechClass (cechAbCube F.obj V U) 0
      ⟨presheafCechAug (F.obj ⋙ abToIntModule) V U s,
        LinearMap.mem_ker.2 (d_presheafCechAug (F.obj ⋙ abToIntModule) V U s)⟩ =
      cechClass _ 0 x := (presheafToCechH_apply (F.obj ⋙ abToIntModule) V U s).symm.trans hs
  have hx : x.1 = presheafCechAug (F.obj ⋙ abToIntModule) V U s :=
    (congrArg Subtype.val ((cechClass_zero_bijective _).1 h1)).symm
  obtain ⟨s'', hs''⟩ : ∃ s'', s'' = G.obj.map (homOfLE hV).op (φ.hom.app (op V) s) := ⟨_, rfl⟩
  have hy' : y.1 = presheafCechAug (G.obj ⋙ abToIntModule) V' U' s'' := by
    funext t
    obtain ⟨t, ht⟩ := t
    obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 ht
    rw [hy, Cube.PullHom.term_apply_of_injOn _ _ _ (by simp)]
    have hsg : PD.sortSign τ {k} = 1 := by simp [PD.sortSign]
    rw [hsg, one_smul]
    show G.obj.map (homOfLE (hτ {k})).op (φ.hom.app (op (cechOpen V U (({k} : Finset κ).image τ)))
      (x.1 ⟨({k} : Finset κ).image τ, Cube.PullHom.card_image ⟨{k}, ht⟩ (by simp)⟩)) =
      G.obj.map (homOfLE (cechOpen_le V' U' {k})).op s''
    rw [hx, hs'']
    have nat := ConcreteCategory.congr_hom
      (φ.hom.naturality (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op) s
    change φ.hom.app _ (F.obj.map _ s) = G.obj.map _ (φ.hom.app _ s) at nat
    change G.obj.map _ (φ.hom.app _ (F.obj.map (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op s)) = _
    rw [nat]
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _))
    rfl
  have h2 : cechClass _ 0 y = toCechAbH G.obj V' U' s'' :=
    (congrArg (cechClass _ 0) (Subtype.ext hy')).trans
      (presheafToCechH_apply (G.obj ⋙ abToIntModule) V' U' s'').symm
  rw [h2, ← hs, cechAbHEquivH'_toCechAbH, cechAbHEquivH'_toCechAbH]
  apply (SheafLES.equivZero G V').injective
  rw [AddEquiv.apply_symm_apply, SheafPull.equivZero_pull, AddEquiv.apply_symm_apply, hs'']

end GlobalTheory
