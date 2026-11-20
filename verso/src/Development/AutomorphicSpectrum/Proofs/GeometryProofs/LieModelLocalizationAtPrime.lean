import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinLie

open LieTangent

section SlopeTestRemainingChoices

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp`.
-/
theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp

/- English proof (translation)
Rewrite using `[← dualMap_comp]`. Conclude with `spec_comp _ _`.
-/
theorem spec_dualMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) = spMap (dualMap (ψ.comp φ)) := by
  rw [← dualMap_comp]
  exact spec_comp _ _

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X} {E : Type}
  [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Substitute `hz` using the available equality. Take `⟨h1, v, hv, hw0⟩` from `h`. Establish `c` using `centre_specializes φ z`. Establish `h2` using `specializes_of_injective (p := ⟨_, h1⟩) (hξ.inj _) c`. Establish `hσ : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes c).hom) ≫ X.fromSpecStalk (centre z) = X.fromSpecStalk (centre (spMap φ ≫ z))` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk c`.

Use `⟨h2, epsBase (X.presheaf.stalkSpecializes c).hom hσ ≫ v, ⟨isTanAt_base _ hσ hv.1, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = _ ≫ spMap (dualMap (X.presheaf.stalkSpecializes c).hom) ≫ v.left`. Establish `e : (genMap ξ ⟨_, h2⟩).comp (X.presheaf.stalkSpecializes c).hom = genMap ξ ⟨_, h1⟩` using `RingHom.ext fun s => genMap_specializes ⟨_, h1⟩ h2 c s`. Rewrite using `[hv.2, ← Category.assoc, spec_dualMap, e]`. Express the relevant statement in the definitionally equal form `_ = _ ≫ spMap (dualMap (X.presheaf.stalkSpecializes c).hom) ≫ v.left`.

Establish `e : (Scheme.stalkClosedPointTo (spMap φ ≫ z)).hom.comp (X.presheaf.stalkSpecializes c).hom = φ.comp (Scheme.stalkClosedPointTo z).hom` using `RingHom.ext fun s => congrArg (fun g => g.hom s) (stalk_base φ z)`. Rewrite using `[hw, hw0, ← Category.assoc, ← Category.assoc, spec_dualMap, spec_dualMap, e]`.
-/
theorem lieValAt_base (M : LieModel G ξ E) (hξ : IsCptGen ξ) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R']
    [IsLocalRing R'] (φ : R →+* R') {z : Sp R ⟶ X} {z' : Sp R' ⟶ X} (hz : spMap φ ≫ z = z') {e : E}
    {w : epsAt z ⟶ G} {w' : epsAt z' ⟶ G} (h : M.ValAt z e w) (hw : w'.left = spMap (dualMap φ) ≫ w.left) :
    M.ValAt z' e w' := by
  subst hz
  obtain ⟨h1, v, hv, hw0⟩ := h
  have c := centre_specializes φ z
  have h2 := specializes_of_injective (p := ⟨_, h1⟩) (hξ.inj _) c
  have hσ : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes c).hom) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (spMap φ ≫ z)) := Scheme.SpecMap_stalkSpecializes_fromSpecStalk c
  refine ⟨h2, epsBase (X.presheaf.stalkSpecializes c).hom hσ ≫ v, ⟨isTanAt_base _ hσ hv.1, ?_⟩, ?_⟩
  · change _ = _ ≫ spMap (dualMap (X.presheaf.stalkSpecializes c).hom) ≫ v.left
    have e : (genMap ξ ⟨_, h2⟩).comp (X.presheaf.stalkSpecializes c).hom = genMap ξ ⟨_, h1⟩ :=
      RingHom.ext fun s => genMap_specializes ⟨_, h1⟩ h2 c s
    rw [hv.2, ← Category.assoc, spec_dualMap, e]
  · change _ = _ ≫ spMap (dualMap (X.presheaf.stalkSpecializes c).hom) ≫ v.left
    have e : (Scheme.stalkClosedPointTo (spMap φ ≫ z)).hom.comp (X.presheaf.stalkSpecializes c).hom =
        φ.comp (Scheme.stalkClosedPointTo z).hom :=
      RingHom.ext fun s => congrArg (fun g => g.hom s) (stalk_base φ z)
    rw [hw, hw0, ← Category.assoc, ← Category.assoc, spec_dualMap, spec_dualMap, e]

omit [GrpObj G] [Module Ω E] in
/- English proof (translation)
Substitute `hx` using the available equality. Conclude with `(GlobalTheory.T.lie_model_existsUnique_semilinear S G R R' c x E E' M M').exists`.
-/
theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {x : Sp R ⟶ S} {x' : Sp R' ⟶ S} (hx : spMap c ≫ x = x') {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G x' E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, M.Lifts c (𝟙 G.left) e (M'.pt (j e)) := by
  subst hx
  exact (GlobalTheory.T.lie_model_existsUnique_semilinear S G R R' c x E E' M M').exists

end SlopeTestRemainingChoices

/- English proof (translation)
Take `⟨c', h⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))`. Use `⟨_, c', ?_, by rw [← h, mul_comm]⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hc`.
-/
theorem dvd_absNorm {L : Type} [Field L] [NumberField L] (c : 𝓞 L) (hc : c ≠ 0) :
    ∃ (n : ℕ) (c' : 𝓞 L), n ≠ 0 ∧ (n : 𝓞 L) = c * c' := by
  obtain ⟨c', h⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
  refine ⟨_, c', ?_, by rw [← h, mul_comm]⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hc

/- English proof (translation)
Introduce `X G _ _ _ Ω _ ξ Li _ _ M L _ _ 𝔭 _ A _ _ _ _ _ _ z B MB f h hξ hreg hreg'`. Establish `hzz : spMap (algebraMap A L) ≫ spMap (algebraMap (𝓞 L) A) ≫ z = spMap (algebraMap (𝓞 L) L) ≫ z`. Rewrite using `[← Category.assoc, spec_comp, ← IsScalarTower.algebraMap_eq]`. Take `⟨EA, _, _, ⟨MA⟩⟩` from `lieModel_exists X G A (spMap (algebraMap (𝓞 L) A) ≫ z)`. Take `⟨EL, _, _, ⟨ML⟩⟩` from `lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)`.

Use `letI : Module (𝓞 L) EA := Module.compHom EA (algebraMap (𝓞 L) A)`. Use `haveI : IsScalarTower (𝓞 L) A EA := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `letI : Module (𝓞 L) EL := Module.compHom EL (algebraMap (𝓞 L) L)`. Use `haveI : IsScalarTower (𝓞 L) L EL := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Take `⟨j₀, hj₀⟩` from `exists_transport (algebraMap (𝓞 L) A) rfl MB MA`.

Take `⟨k, hk⟩` from `exists_transport (algebraMap A L) hzz MA ML`. Set `j : B.carrier →ₗ[𝓞 L] EA` to `{ toFun := j₀, map_add' := j₀.map_add, map_smul' := fun c x => j₀.map_smulₛₗ c x }`. Establish `hks : ∀ (c : 𝓞 L) (y : EA), k (c • y) = c • k y` using `fun c y => by`. Establish `e : c • y = algebraMap (𝓞 L) A c • y` using `rfl`. Establish `e' : c • k y = algebraMap (𝓞 L) L c • k y` using `rfl`.

Rewrite using `[e, e', k.map_smulₛₗ, IsScalarTower.algebraMap_apply (𝓞 L) A L]`. Set `jL : B.carrier →ₗ[𝓞 L] EL` to `{ toFun := fun x => k (j x), map_add' := fun x x' => by simp map_smul' := fun c x => by simp [hks] }`. Establish `hj : ∀ x, MB.Lifts (algebraMap (𝓞 L) A) (𝟙 G.left) x (MA.pt (j x))` using `hj₀`. Establish `hjL : ∀ x, MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x (ML.pt (jL x))` using `fun x => by`. Establish `h1` using `hk (j x)`.

Establish `h2` using `hj x`. Unfold `LieModel.Lifts at h1 h2 ⊢`. Rewrite `h1`, `h2`, the goal using `[Category.comp_id]`. Express the relevant statement in the definitionally equal form `(ML.pt (k (j x))).left = _`. Rewrite using `[h1, h2, ← Category.assoc, spec_dualMap, ← IsScalarTower.algebraMap_eq]`.

Establish `hbA : IsBaseChange A j` using `GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) A z B.carrier EA MB MA j hj`. Establish `hbL : IsBaseChange L jL` using `GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z B.carrier EL MB ML jL hjL`. Use `haveI : IsLocalizedModule 𝔭.primeCompl j := (isLocalizedModule_iff_isBaseChange 𝔭.primeCompl A j).2 hbA`. Use `haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) jL := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L jL).2 hbL`. Establish `hinj : Function.Injective jL` using `fun x y hxy => by`.

Take `⟨c, hc⟩` from `(IsLocalizedModule.eq_iff_exists (nonZeroDivisors (𝓞 L)) jL).1 hxy`. Conclude with `smul_right_injective B.carrier (nonZeroDivisors.ne_zero c.2) hc`. Establish `hL : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z)` using `specializes_of_injective (p := ⟨_, h⟩) (hξ.inj _) (hzz ▸ centre_specializes (algebraMap A L) (spMap (algebraMap (𝓞 L) A) ≫ z))`. Take `⟨gA, hgA⟩` from `GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M A _ h EA MA f hξ hreg`. Take `⟨gL, hgL⟩` from `GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M L _ hL EL ML f hξ (hreg' hL)`.

Take `⟨ev, hev, -, hspan⟩` from `GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M A _ h EA MA hξ inferInstance`. Establish `hlift : ∀ (e : Li) (y : EA), M.ValAt (spMap (algebraMap (𝓞 L) A) ≫ z) e (MA.pt y) → M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt (k y))` using `fun e y hv => by`. Use `lieValAt_base M hξ (algebraMap A L) hzz hv ?_` and prove the remaining obligations. Establish `h1` using `hk y`. Unfold `LieModel.Lifts at h1`.

Rewrite `h1` using `[Category.comp_id]`. Then use the resulting hypothesis. Establish `hcompat : ∀ y : EA, gL (k y) = algebraMap A L (gA y)` using `fun y => by`. Establish `hy : y ∈ Submodule.span A (Set.range ev)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨⟨e, he⟩, rfl⟩` from `hy`. Establish `hv` using `(hev e _).2 ⟨he, rfl⟩`. Take `⟨s, hs⟩` from `hreg e he`. Establish `hu : ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) _` using `⟨h, s, hs, rfl⟩`. Establish `hu'` using `valAt_base hξ (algebraMap A L) hu`.

Rewrite `hu'` using `[hzz]`. Rewrite using `[hgA _ _ _ hv hu]`. Conclude with `hgL _ _ _ (hlift _ _ hv) hu'`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp [ha, hb]`.

Consider the case `smul c y _ hy => simp [k.map_smulₛₗ, hy]`. Use `⟨(gA.restrictScalars (𝓞 L)).comp j, ?_, ?_⟩` and prove the remaining obligations. Introduce `x e v u hv hl hu`. Establish `hvx : v = ML.pt (jL x)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Establish `h4` using `hjL x`. Unfold `LieModel.Lifts at hl h4`. Rewrite `hl`, `h4` using `[Category.comp_id]`. Conclude with `hl.trans h4.symm`. Substitute `hvx` using the available equality.

Conclude with `(hcompat (j x)).symm.trans (hgL _ _ _ hv hu)`. Introduce `e u he hu`. Establish `hv` using `(hev e _).2 ⟨he, rfl⟩`. Establish `hgy` using `hgA _ _ _ hv hu`. Take `⟨⟨x, d⟩, hxd⟩` from `IsLocalizedModule.surj 𝔭.primeCompl j (ev ⟨e, he⟩)`.

Use `replace hxd : (d : 𝓞 L) • ev ⟨e, he⟩ = j x := hxd`. Take `⟨⟨x₀, c⟩, hc⟩` from `IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) jL (k (ev ⟨e, he⟩))`. Use `replace hc : (c : 𝓞 L) • k (ev ⟨e, he⟩) = jL x₀ := hc`. Take `⟨n, c', hn, hc'⟩` from `dvd_absNorm (c : 𝓞 L) (nonZeroDivisors.ne_zero c.2)`. Establish `hx' : jL (c' • x₀) = (n : 𝓞 L) • k (ev ⟨e, he⟩)`.

Rewrite using `[map_smul, ← hc, hc', mul_comm, mul_smul]`. Use `⟨d, n, x, c' • x₀, ML.pt (jL (c' • x₀)), d.2, hn, ?_, ?_, hjL _, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `gA (j x) = _`. Rewrite using `[← hxd, ← algebraMap_smul A (d : 𝓞 L) (ev ⟨e, he⟩), map_smul, hgy, smul_eq_mul]`. Establish `hs` using `(hlift _ _ hv).smul hL (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))`.

Rewrite `hs` using `[map_natCast, map_natCast]`. Establish `e1 : (n : 𝓞 L) • k (ev ⟨e, he⟩) = (n : L) • k (ev ⟨e, he⟩)`. Rewrite using `[← algebraMap_smul L (n : 𝓞 L), map_natCast]`. Rewrite using `[hx', e1, ML.pt_smul]`. Conclude with `hs`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_smul, map_smul, hx']`. Express the relevant statement in the definitionally equal form `(n : 𝓞 L) • k (j x) = _`. Rewrite using `[← hxd, hks, smul_comm]`.
-/
theorem exists_integral_form : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A]
    [IsLocalization.AtPrime A 𝔭] [Algebra A L] [IsScalarTower (𝓞 L) A L] (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) (f : Module.Dual Ω Li)
    (h : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) A) ≫ z)), IsCptGen ξ →
    (∀ e ∈ M.lat ⟨_, h⟩, f e ∈ regAt ξ ⟨_, h⟩) →
    (∀ h' : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z), ∀ e ∈ M.lat ⟨_, h'⟩, f e ∈ regAt ξ ⟨_, h'⟩) →
    ∃ g : B.carrier →ₗ[𝓞 L] A,
      (∀ (x : B.carrier) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (u : L),
        M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x v →
        ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (f e) u → algebraMap A L (g x) = u) ∧
      ∀ (e : Li) (u : A), e ∈ M.lat ⟨_, h⟩ → ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) u →
        ∃ (d : 𝓞 L) (n : ℕ) (x x' : B.carrier) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
          d ∉ 𝔭 ∧ n ≠ 0 ∧ g x = algebraMap (𝓞 L) A d * u ∧ M.ValAt _ ((n : Ω) • e) v ∧
          MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v ∧ (n : 𝓞 L) • x = d • x' := by
  intro X G _ _ _ Ω _ ξ Li _ _ M L _ _ 𝔭 _ A _ _ _ _ _ _ z B MB f h hξ hreg hreg'
  have hzz : spMap (algebraMap A L) ≫ spMap (algebraMap (𝓞 L) A) ≫ z = spMap (algebraMap (𝓞 L) L) ≫ z := by
    rw [← Category.assoc, spec_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G A (spMap (algebraMap (𝓞 L) A) ≫ z)
  obtain ⟨EL, _, _, ⟨ML⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) EA := Module.compHom EA (algebraMap (𝓞 L) A)
  haveI : IsScalarTower (𝓞 L) A EA := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module (𝓞 L) EL := Module.compHom EL (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L EL := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨j₀, hj₀⟩ := exists_transport (algebraMap (𝓞 L) A) rfl MB MA
  obtain ⟨k, hk⟩ := exists_transport (algebraMap A L) hzz MA ML
  let j : B.carrier →ₗ[𝓞 L] EA :=
    { toFun := j₀, map_add' := j₀.map_add, map_smul' := fun c x => j₀.map_smulₛₗ c x }
  have hks : ∀ (c : 𝓞 L) (y : EA), k (c • y) = c • k y := fun c y => by
    have e : c • y = algebraMap (𝓞 L) A c • y := rfl
    have e' : c • k y = algebraMap (𝓞 L) L c • k y := rfl
    rw [e, e', k.map_smulₛₗ, IsScalarTower.algebraMap_apply (𝓞 L) A L]
  let jL : B.carrier →ₗ[𝓞 L] EL :=
    { toFun := fun x => k (j x), map_add' := fun x x' => by simp
      map_smul' := fun c x => by simp [hks] }
  have hj : ∀ x, MB.Lifts (algebraMap (𝓞 L) A) (𝟙 G.left) x (MA.pt (j x)) := hj₀
  have hjL : ∀ x, MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x (ML.pt (jL x)) := fun x => by
    have h1 := hk (j x)
    have h2 := hj x
    unfold LieModel.Lifts at h1 h2 ⊢
    rw [Category.comp_id] at h1 h2 ⊢
    change (ML.pt (k (j x))).left = _
    rw [h1, h2, ← Category.assoc, spec_dualMap, ← IsScalarTower.algebraMap_eq]
  have hbA : IsBaseChange A j := GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) A z B.carrier EA MB MA j hj
  have hbL : IsBaseChange L jL := GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z B.carrier EL MB ML jL hjL
  haveI : IsLocalizedModule 𝔭.primeCompl j := (isLocalizedModule_iff_isBaseChange 𝔭.primeCompl A j).2 hbA
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) jL :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L jL).2 hbL
  have hinj : Function.Injective jL := fun x y hxy => by
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors (𝓞 L)) jL).1 hxy
    exact smul_right_injective B.carrier (nonZeroDivisors.ne_zero c.2) hc
  have hL : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) :=
    specializes_of_injective (p := ⟨_, h⟩) (hξ.inj _) (hzz ▸ centre_specializes (algebraMap A L) (spMap (algebraMap (𝓞 L) A) ≫ z))
  obtain ⟨gA, hgA⟩ := GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M A _ h EA MA f hξ hreg
  obtain ⟨gL, hgL⟩ := GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M L _ hL EL ML f hξ (hreg' hL)
  obtain ⟨ev, hev, -, hspan⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M A _ h EA MA hξ inferInstance
  have hlift : ∀ (e : Li) (y : EA), M.ValAt (spMap (algebraMap (𝓞 L) A) ≫ z) e (MA.pt y) →
      M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt (k y)) := fun e y hv => by
    refine lieValAt_base M hξ (algebraMap A L) hzz hv ?_
    have h1 := hk y
    unfold LieModel.Lifts at h1
    rwa [Category.comp_id] at h1
  have hcompat : ∀ y : EA, gL (k y) = algebraMap A L (gA y) := fun y => by
    have hy : y ∈ Submodule.span A (Set.range ev) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨e, he⟩, rfl⟩ := hy
      have hv := (hev e _).2 ⟨he, rfl⟩
      obtain ⟨s, hs⟩ := hreg e he
      have hu : ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) _ := ⟨h, s, hs, rfl⟩
      have hu' := valAt_base hξ (algebraMap A L) hu
      rw [hzz] at hu'
      rw [hgA _ _ _ hv hu]
      exact hgL _ _ _ (hlift _ _ hv) hu'
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c y _ hy => simp [k.map_smulₛₗ, hy]
  refine ⟨(gA.restrictScalars (𝓞 L)).comp j, ?_, ?_⟩
  · intro x e v u hv hl hu
    have hvx : v = ML.pt (jL x) := by
      apply Over.OverMorphism.ext
      have h4 := hjL x
      unfold LieModel.Lifts at hl h4
      rw [Category.comp_id] at hl h4
      exact hl.trans h4.symm
    subst hvx
    exact (hcompat (j x)).symm.trans (hgL _ _ _ hv hu)
  · intro e u he hu
    have hv := (hev e _).2 ⟨he, rfl⟩
    have hgy := hgA _ _ _ hv hu
    obtain ⟨⟨x, d⟩, hxd⟩ := IsLocalizedModule.surj 𝔭.primeCompl j (ev ⟨e, he⟩)
    replace hxd : (d : 𝓞 L) • ev ⟨e, he⟩ = j x := hxd
    obtain ⟨⟨x₀, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) jL (k (ev ⟨e, he⟩))
    replace hc : (c : 𝓞 L) • k (ev ⟨e, he⟩) = jL x₀ := hc
    obtain ⟨n, c', hn, hc'⟩ := dvd_absNorm (c : 𝓞 L) (nonZeroDivisors.ne_zero c.2)
    have hx' : jL (c' • x₀) = (n : 𝓞 L) • k (ev ⟨e, he⟩) := by
      rw [map_smul, ← hc, hc', mul_comm, mul_smul]
    refine ⟨d, n, x, c' • x₀, ML.pt (jL (c' • x₀)), d.2, hn, ?_, ?_, hjL _, ?_⟩
    · change gA (j x) = _
      rw [← hxd, ← algebraMap_smul A (d : 𝓞 L) (ev ⟨e, he⟩), map_smul, hgy, smul_eq_mul]
    · have hs := (hlift _ _ hv).smul hL (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
      rw [map_natCast, map_natCast] at hs
      have e1 : (n : 𝓞 L) • k (ev ⟨e, he⟩) = (n : L) • k (ev ⟨e, he⟩) := by
        rw [← algebraMap_smul L (n : 𝓞 L), map_natCast]
      rw [hx', e1, ML.pt_smul]
      exact hs
    · apply hinj
      rw [map_smul, map_smul, hx']
      change (n : 𝓞 L) • k (j x) = _
      rw [← hxd, hks, smul_comm]

end GlobalTheory.CompanionTheory.Ar.RootHt.FinLie
