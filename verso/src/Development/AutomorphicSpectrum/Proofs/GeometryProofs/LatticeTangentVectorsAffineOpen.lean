import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModelOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.RootHt.LieFun GlobalTheory.CompanionTheory.Ar.Flat.BdryModel
open scoped CategoryTheory.Obj

/- English proof (translation)
Establish `h1 : ∀ i, ∃ e, (iota R).hom ≫ M.pt e = v i` using `fun i => by`. Take `⟨e, he⟩` from `M.onto ((iota R).inv ≫ v i) ((tan_iff _).1 (by simpa using hv.1 i))`. Conclude with `⟨e, by simp [he]⟩`. Use `choose e he using h1`. Set `F : Multiplicative E →* (epsR R ⟶ G)` to `MonoidHom.mk' (fun x => (iota R).hom ≫ M.pt x.toAdd) (fun a b => by simp [M.add, MonObj.comp_mul])`.

Establish `hs : ∀ c : Fin n → R, (iota R).hom ≫ M.pt (∑ i, c i • e i) = (List.ofFn fun i => (iota R).hom ≫ M.pt (c i • e i)).prod` using `fun c => by`. Express the relevant statement in the definitionally equal form `F (Multiplicative.ofAdd (∑ i, c i • e i)) = _`. Rewrite using `[ofAdd_sum, ← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Establish `hl : ∀ (c : R) i, ((iota R).hom ≫ M.pt (c • e i)).left = spMap (epsScaleR c) ≫ (v i).left` using `fun c i => by`.

Rewrite using `[iota_left, M.smul, ← he, iota_left]`. Both sides reduce to the same expression. Use `⟨e, fun i => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← he, iota_left]`. Take `⟨c, ⟨u, hu, hx⟩, -⟩` from `hv.2 _ ((tan_iff _).2 (M.tan x))`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `: u = fun i => (iota R).hom ≫ M.pt (c i • e i)`. Use function extensionality and compare the values at `i`. Use `ext1`. Rewrite using `[hu, hl]`.

Rewrite `hx` using `[this, ← hs]`. Conclude with `M.inj ((cancel_epi (iota R).hom).1 hx)`.
-/
theorem exists_coords_of_isLieBasis {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 _) E) :
    ∃ e : Fin n → E, (∀ i, (M.pt (e i)).left = (v i).left) ∧ ∀ x, ∃ c : Fin n → R, x = ∑ i, c i • e i := by
  have h1 : ∀ i, ∃ e, (iota R).hom ≫ M.pt e = v i := fun i => by
    obtain ⟨e, he⟩ := M.onto ((iota R).inv ≫ v i) ((tan_iff _).1 (by simpa using hv.1 i))
    exact ⟨e, by simp [he]⟩
  choose e he using h1
  let F : Multiplicative E →* (epsR R ⟶ G) := MonoidHom.mk' (fun x => (iota R).hom ≫ M.pt x.toAdd)
    (fun a b => by simp [M.add, MonObj.comp_mul])
  have hs : ∀ c : Fin n → R, (iota R).hom ≫ M.pt (∑ i, c i • e i) =
      (List.ofFn fun i => (iota R).hom ≫ M.pt (c i • e i)).prod := fun c => by
    change F (Multiplicative.ofAdd (∑ i, c i • e i)) = _
    rw [ofAdd_sum, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hl : ∀ (c : R) i, ((iota R).hom ≫ M.pt (c • e i)).left = spMap (epsScaleR c) ≫ (v i).left := fun c i => by
    rw [iota_left, M.smul, ← he, iota_left]; rfl
  refine ⟨e, fun i => ?_, fun x => ?_⟩
  · rw [← he, iota_left]
  · obtain ⟨c, ⟨u, hu, hx⟩, -⟩ := hv.2 _ ((tan_iff _).2 (M.tan x))
    refine ⟨c, ?_⟩
    have : u = fun i => (iota R).hom ≫ M.pt (c i • e i) := by
      funext i; ext1; rw [hu, hl]
    rw [this, ← hs] at hx
    exact M.inj ((cancel_epi (iota R).hom).1 hx)

section Base

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S} {x' : Sp R' ⟶ S}
  {G : Over S} [GrpObj G] {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (M.smul c e)`.
-/
theorem pt_smul_eq (M : LieModel G x E) (c : R) (e : E) : M.pt (c • e) = epsScale x c ≫ M.pt e :=
  Over.OverMorphism.ext (M.smul c e)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Rewrite using `[LieModel.pt_zero, LieModel.pt_zero, MonObj.comp_one]`. Consider the case `insert i s hi ih`.

Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, M'.add, M.add, MonObj.comp_mul, ih, pt_smul_eq, pt_smul_eq, h, ← Category.assoc, ← Category.assoc, base_scale]`.
-/
theorem pt_sum_base (φ : R →+* R') (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (M : LieModel G x E)
    (M' : LieModel G x' E') {I : Type} (s : Finset I) (d : I → R) (e : I → E) (e' : I → E')
    (h : ∀ i, M'.pt (e' i) = epsBase φ hφ ≫ M.pt (e i)) :
    M'.pt (∑ i ∈ s, φ (d i) • e' i) = epsBase φ hφ ≫ M.pt (∑ i ∈ s, d i • e i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [LieModel.pt_zero, LieModel.pt_zero, MonObj.comp_one]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, M'.add, M.add, MonObj.comp_mul, ih, pt_smul_eq, pt_smul_eq, h,
      ← Category.assoc, ← Category.assoc, base_scale]

end Base

/- English proof (translation)
Establish `hz : 𝟙 (Sp R) ≫ (spMap f ≫ hU.fromSpec) = x` using `by rw [Category.id_comp, hx]`. Substitute `hz` using the available equality. Establish `hφ` using `isGrpPullback_pullback G (spMap f ≫ hU.fromSpec)`. Take `⟨v', hv1, hv2⟩` from `hv₀ R f _ _ hφ`. Take `⟨M', hM'⟩` from `(LieMove.models_correspond (x := 𝟙 (Sp R)) hφ E).1 M`.

Take `⟨e, he1, he2⟩` from `exists_coords_of_isLieBasis v' hv2 M'`. Use `⟨e, fun j => ?_, he2⟩` and prove the remaining obligations. Rewrite using `[← hM' (e j), he1 j, hv1 j]`. Establish `: ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f = dualMap f`. Apply the tactic sequence `ext a <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]`.

Rewrite using `[this]`.
-/
theorem exists_frame {X : Scheme.{0}} {G : Over X} [GrpObj G] {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (v₀ : Fin n → (Sp (DualNumber Γ(X, U)) ⟶ G.left))
    (hv₀ : ∀ (R' : Type) [CommRing R'] (f : Γ(X, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left),
      IsGrpPullback G' G (spMap f ≫ hU.fromSpec) φ →
        ∃ v' : Fin n → (epsR R' ⟶ G'),
          (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v')
    {R : Type} [CommRing R] (f : Γ(X, U) →+* R) {x : Sp R ⟶ X} (hx : spMap f ≫ hU.fromSpec = x)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∃ e : Fin n → E, (∀ j, (M.pt (e j)).left = spMap (dualMap f) ≫ v₀ j) ∧
      ∀ y, ∃ c : Fin n → R, y = ∑ j, c j • e j := by
  have hz : 𝟙 (Sp R) ≫ (spMap f ≫ hU.fromSpec) = x := by rw [Category.id_comp, hx]
  subst hz
  have hφ := isGrpPullback_pullback G (spMap f ≫ hU.fromSpec)
  obtain ⟨v', hv1, hv2⟩ := hv₀ R f _ _ hφ
  obtain ⟨M', hM'⟩ := (LieMove.models_correspond (x := 𝟙 (Sp R)) hφ E).1 M
  obtain ⟨e, he1, he2⟩ := exists_coords_of_isLieBasis v' hv2 M'
  refine ⟨e, fun j => ?_, he2⟩
  rw [← hM' (e j), he1 j, hv1 j]
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f = dualMap f := by
    ext a <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this]

/- English proof (translation)
Establish `h1` using `Spec.map_injective ((cancel_mono hW.fromSpec).1 h)`. Conclude with `congrArg CommRingCat.Hom.hom h1`.
-/
theorem fromSpec_ringHom_ext {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) {R : Type} [CommRing R]
    {a a' : Γ(X, W) →+* R} (h : spMap a ≫ hW.fromSpec = spMap a' ≫ hW.fromSpec) : a = a' := by
  have h1 := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
  exact congrArg CommRingCat.Hom.hom h1

/- English proof (translation)
Rewrite using `[spec_comp]`. Use `congr 2`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp`.
-/
theorem spec_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (φ' : R' →+* R'') :
    Spec.map (CommRingCat.ofHom (dualMap φ')) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) =
      Spec.map (CommRingCat.ofHom (dualMap (φ'.comp φ))) := by
  rw [spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp

/- English proof (translation)
The claim follows from `hW.fromSpecStalk_eq_fromSpecStalk hp`.
-/
theorem germ_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) {p : X} (hp : p ∈ W) :
    Spec.map (CommRingCat.ofHom (X.presheaf.germ W p hp).hom) ≫ hW.fromSpec = X.fromSpecStalk p :=
  hW.fromSpecStalk_eq_fromSpecStalk hp

/- English proof (translation)
Introduce `X G _ _ _ Ω _ ξ Li _ _ M q N b hξ hb`. Take `⟨W₀, hW₀, hq, -, n, v₀, hv₀⟩` from `GlobalTheory.exists_affine_lieBasis_baseChange X G q.1 ⊤ trivial`. Set `f : Γ(X, W₀) →+* X.presheaf.stalk q.1` to `(X.presheaf.germ W₀ q.1 hq).hom`. Take `⟨e, he1, he2⟩` from `exists_frame hW₀ v₀ hv₀ f (germ_fromSpec hW₀ hq) (stalkLie hξ M q)`. Establish `hc` using `fun k => he2 (⟨b k, hb k⟩ : Stalk M q)`.

Use `choose c hc using hc`. Use `letI : Algebra Γ(X, W₀) (X.presheaf.stalk q.1) := f.toAlgebra`. Use `haveI := hW₀.isLocalization_stalk ⟨q.1, hq⟩`. Take `⟨⟨s, hs⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finite (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl (fun p : Fin N × Fin n => c p.1 p.2)`. Use `choose a ha using hint`.

Establish `hunit : IsUnit (f s)` using `IsLocalization.map_units (M := (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl) (X.presheaf.stalk q.1) ⟨s, hs⟩`. Establish `hqW : q.1 ∈ X.basicOpen s` using `(X.mem_basicOpen s q.1 hq).2 hunit`. Establish `hW : IsAffineOpen (X.basicOpen s)` using `hW₀.basicOpen s`. Set `g : Γ(X, W₀) →+* Γ(X, X.basicOpen s)` to `(X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom`. Establish `hg : spMap g ≫ hW₀.fromSpec = hW.fromSpec` using `IsAffineOpen.map_fromSpec hW₀ hW (homOfLE (X.basicOpen_le s)).op`.

Take `⟨u, hu⟩ : IsUnit (g s)` from `RingedSpace.isUnit_res_basicOpen X.toRingedSpace s`. Take `⟨E', _, _, ⟨M'⟩⟩` from `lieModel_exists X G Γ(X, X.basicOpen s) hW.fromSpec`. Take `⟨e', he'1, -⟩` from `exists_frame hW₀ v₀ hv₀ g hg M'`. Set `d : Fin N → Fin n → Γ(X, X.basicOpen s)` to `fun k j => g (a (k, j)) * (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ)`. Set `v : Fin N → (epsAt (R` to `Γ(X, X.basicOpen s)) hW.fromSpec ⟶ G) := fun k => M'.pt (∑ j, d k j • e' j)`.

Set `θ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk q.1` to `(X.presheaf.germ _ q.1 hqW).hom`. Establish `hθ : Spec.map (CommRingCat.ofHom θ) ≫ hW.fromSpec = X.fromSpecStalk q.1` using `germ_fromSpec hW hqW`. Establish `hθg : θ.comp g = f`. Use `RingHom.ext fun t => ?_` and prove the remaining obligations. Conclude with `congrArg (fun m => m.hom t) (X.presheaf.germ_res (homOfLE (X.basicOpen_le s)) q.1 hqW)`.

Establish `hθa : ∀ t, θ (g t) = f t` using `fun t => congrArg (fun m => m t) hθg`. Establish `key : ∀ k, (stalkLie hξ M q).pt ⟨b k, hb k⟩ = epsBase θ hθ ≫ v k`. Introduce `k`. Establish `hd : ∀ j, θ (d k j) = c k j` using `fun j => by`. Establish `h1 : f (a (k, j)) = f s * c k j` using `ha (k, j)`.

Establish `h2 : θ (g s) * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ) = 1`. Rewrite using `[← map_mul, ← hu, Units.mul_inv, map_one]`. Rewrite `h2` using `[hθa]`. Combine the equalities or inequalities in the displayed calculation. Use `pt_sum_base θ hθ M' (stalkLie hξ M q) Finset.univ (d k) e' e (fun j => Over.OverMorphism.ext (by` as an intermediate fact.

Rewrite using `[he1 j]`. Express the relevant statement in the definitionally equal form `_ = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M'.pt (e' j)).left`. Rewrite using `[he'1 j, ← Category.assoc, spec_dual_comp, hθg]))`. Rewrite using `[hc k]`. Simplify `this` using `only [hd]`.

Use `⟨X.basicOpen s, hW, v, hqW, fun k => M'.tan _, ?_⟩` and prove the remaining obligations. Introduce `ψ z hz h k`. Substitute `hz` using the available equality. Establish `hp : centre (spMap ψ ≫ hW.fromSpec) ∈ X.basicOpen s`. Rewrite using `[← SetLike.mem_coe, ← hW.range_fromSpec]`.

Conclude with `⟨(spMap ψ) (IsLocalRing.closedPoint ℂ), rfl⟩`. Set `θp : Γ(X, X.basicOpen s) →+* X.presheaf.stalk (centre (spMap ψ ≫ hW.fromSpec))` to `(X.presheaf.germ _ _ hp).hom`. Establish `hθp : Spec.map (CommRingCat.ofHom θp) ≫ hW.fromSpec = X.fromSpecStalk _` using `germ_fromSpec hW hp`. Establish `e1 : (genMap ξ q).comp θ = (genMap ξ ⟨_, h⟩).comp θp` using `fromSpec_ringHom_ext hW (by`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom _) ≫ _ = Spec.map (CommRingCat.ofHom _) ≫ _`.

Rewrite using `[← spec_comp, ← spec_comp, Category.assoc, Category.assoc, hθ, hθp, spec_genMap, spec_genMap])`. Establish `e2 : ψ = (Scheme.stalkClosedPointTo (spMap ψ ≫ hW.fromSpec)).hom.comp θp` using `fromSpec_ringHom_ext hW (by`. Express the relevant statement in the definitionally equal form `_ = Spec.map (CommRingCat.ofHom _) ≫ _`. Rewrite using `[← spec_comp, Category.assoc, hθp]`. Conclude with `(spec_centre _).symm)`.

Use `⟨epsBase ψ rfl ≫ v k, ⟨h, epsBase θp hθp ≫ v k, ⟨isTanAt_base _ _ (M'.tan _), ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `t : (M.pt (b k)).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ q))) ≫ ((stalkLie hξ M q).pt ⟨b k, hb k⟩).left` using `(Stalk.tan_spec (⟨b k, hb k⟩ : Stalk M q)).2`. Rewrite using `[t, key k]`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (v k).left = Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left`. Rewrite using `[← Category.assoc, ← Category.assoc, spec_dual_comp, spec_dual_comp, e1]`.

Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (dualMap ψ)) ≫ (v k).left = Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left`. Rewrite using `[← Category.assoc, spec_dual_comp, ← e2]`.
-/
theorem exists_affine_frame : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (q : Cpt ξ) (N : ℕ) (b : Fin N → Li), IsCptGen ξ → (∀ k, b k ∈ M.lat q) → ∃ (W : X.Opens) (hW : IsAffineOpen W) (v : Fin N → (epsAt (R := Γ(X, W)) hW.fromSpec ⟶ G)), q.1 ∈ W ∧ (∀ k, IsTanAt G hW.fromSpec (v k)) ∧ ∀ (ψ : Γ(X, W) →+* ℂ) (z : Sp ℂ ⟶ X), spMap ψ ≫ hW.fromSpec = z → genPt ξ ⤳ centre z → ∀ k, ∃ w : epsAt z ⟶ G, M.ValAt z (b k) w ∧ w.left = spMap (dualMap ψ) ≫ (v k).left := by
  intro X G _ _ _ Ω _ ξ Li _ _ M q N b hξ hb
  obtain ⟨W₀, hW₀, hq, -, n, v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange X G q.1 ⊤ trivial
  let f : Γ(X, W₀) →+* X.presheaf.stalk q.1 := (X.presheaf.germ W₀ q.1 hq).hom
  obtain ⟨e, he1, he2⟩ := exists_frame hW₀ v₀ hv₀ f (germ_fromSpec hW₀ hq) (stalkLie hξ M q)
  have hc := fun k => he2 (⟨b k, hb k⟩ : Stalk M q)
  choose c hc using hc

  letI : Algebra Γ(X, W₀) (X.presheaf.stalk q.1) := f.toAlgebra
  haveI := hW₀.isLocalization_stalk ⟨q.1, hq⟩
  obtain ⟨⟨s, hs⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl (fun p : Fin N × Fin n => c p.1 p.2)
  choose a ha using hint
  have hunit : IsUnit (f s) :=
    IsLocalization.map_units (M := (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl) (X.presheaf.stalk q.1) ⟨s, hs⟩
  have hqW : q.1 ∈ X.basicOpen s := (X.mem_basicOpen s q.1 hq).2 hunit
  have hW : IsAffineOpen (X.basicOpen s) := hW₀.basicOpen s
  let g : Γ(X, W₀) →+* Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  have hg : spMap g ≫ hW₀.fromSpec = hW.fromSpec := IsAffineOpen.map_fromSpec hW₀ hW (homOfLE (X.basicOpen_le s)).op
  obtain ⟨u, hu⟩ : IsUnit (g s) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace s
  obtain ⟨E', _, _, ⟨M'⟩⟩ := lieModel_exists X G Γ(X, X.basicOpen s) hW.fromSpec
  obtain ⟨e', he'1, -⟩ := exists_frame hW₀ v₀ hv₀ g hg M'
  let d : Fin N → Fin n → Γ(X, X.basicOpen s) := fun k j => g (a (k, j)) * (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ)
  let v : Fin N → (epsAt (R := Γ(X, X.basicOpen s)) hW.fromSpec ⟶ G) := fun k => M'.pt (∑ j, d k j • e' j)
  let θ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk q.1 := (X.presheaf.germ _ q.1 hqW).hom
  have hθ : Spec.map (CommRingCat.ofHom θ) ≫ hW.fromSpec = X.fromSpecStalk q.1 := germ_fromSpec hW hqW
  have hθg : θ.comp g = f := by
    refine RingHom.ext fun t => ?_
    exact congrArg (fun m => m.hom t) (X.presheaf.germ_res (homOfLE (X.basicOpen_le s)) q.1 hqW)
  have hθa : ∀ t, θ (g t) = f t := fun t => congrArg (fun m => m t) hθg
  have key : ∀ k, (stalkLie hξ M q).pt ⟨b k, hb k⟩ = epsBase θ hθ ≫ v k := by
    intro k
    have hd : ∀ j, θ (d k j) = c k j := fun j => by
      have h1 : f (a (k, j)) = f s * c k j := ha (k, j)
      have h2 : θ (g s) * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ) = 1 := by
        rw [← map_mul, ← hu, Units.mul_inv, map_one]
      rw [hθa] at h2
      calc θ (d k j) = f (a (k, j)) * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ) := by rw [map_mul, hθa]
        _ = (f s * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ)) * c k j := by rw [h1]; ring
        _ = c k j := by rw [h2, _root_.one_mul]
    have := pt_sum_base θ hθ M' (stalkLie hξ M q) Finset.univ (d k) e' e (fun j => Over.OverMorphism.ext (by
      rw [he1 j]
      change _ = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M'.pt (e' j)).left
      rw [he'1 j, ← Category.assoc, spec_dual_comp, hθg]))
    rw [hc k]
    simpa only [hd] using this
  refine ⟨X.basicOpen s, hW, v, hqW, fun k => M'.tan _, ?_⟩
  intro ψ z hz h k
  subst hz
  have hp : centre (spMap ψ ≫ hW.fromSpec) ∈ X.basicOpen s := by
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨(spMap ψ) (IsLocalRing.closedPoint ℂ), rfl⟩
  let θp : Γ(X, X.basicOpen s) →+* X.presheaf.stalk (centre (spMap ψ ≫ hW.fromSpec)) :=
    (X.presheaf.germ _ _ hp).hom
  have hθp : Spec.map (CommRingCat.ofHom θp) ≫ hW.fromSpec = X.fromSpecStalk _ := germ_fromSpec hW hp
  have e1 : (genMap ξ q).comp θ = (genMap ξ ⟨_, h⟩).comp θp := fromSpec_ringHom_ext hW (by
    change Spec.map (CommRingCat.ofHom _) ≫ _ = Spec.map (CommRingCat.ofHom _) ≫ _
    rw [← spec_comp, ← spec_comp, Category.assoc, Category.assoc, hθ, hθp, spec_genMap, spec_genMap])
  have e2 : ψ = (Scheme.stalkClosedPointTo (spMap ψ ≫ hW.fromSpec)).hom.comp θp := fromSpec_ringHom_ext hW (by
    change _ = Spec.map (CommRingCat.ofHom _) ≫ _
    rw [← spec_comp, Category.assoc, hθp]
    exact (spec_centre _).symm)
  refine ⟨epsBase ψ rfl ≫ v k, ⟨h, epsBase θp hθp ≫ v k, ⟨isTanAt_base _ _ (M'.tan _), ?_⟩, ?_⟩, rfl⟩
  · have t : (M.pt (b k)).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ q))) ≫
        ((stalkLie hξ M q).pt ⟨b k, hb k⟩).left := (Stalk.tan_spec (⟨b k, hb k⟩ : Stalk M q)).2
    rw [t, key k]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (v k).left =
      Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left
    rw [← Category.assoc, ← Category.assoc, spec_dual_comp, spec_dual_comp, e1]
  · change Spec.map (CommRingCat.ofHom (dualMap ψ)) ≫ (v k).left =
      Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left
    rw [← Category.assoc, spec_dual_comp, ← e2]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt
