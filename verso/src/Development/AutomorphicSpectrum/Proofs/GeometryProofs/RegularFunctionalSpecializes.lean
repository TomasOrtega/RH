import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

section Transport

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R']
  {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']

/- English proof (translation)
Substitute `h` using the available equality. Take `⟨j, hj, -⟩` from `GlobalTheory.T.lie_model_existsUnique_semilinear S G R R' c x E E' M M'`. Use `⟨j, fun e => ?_⟩` and prove the remaining obligations. Use `hj e` as an intermediate fact. Rewrite `this` using `[LieModel.Lifts, Category.comp_id]`.

Conclude with `this`.
-/
theorem exists_lie_transport (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S} (h : spMap c ≫ x = y)
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear S G R R' c x E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  rw [LieModel.Lifts, Category.comp_id] at this
  exact this

/- English proof (translation)
Substitute `h` using the available equality. Use `letI : Algebra R R' := c.toAlgebra`. Use `letI : Module R E' := Module.compHom E' c`. Use `haveI : IsScalarTower R R' E' := ⟨fun a b v => by`. Express the relevant statement in the definitionally equal form `(c a * b) • v = c a • (b • v)`.

Rewrite using `[mul_smul]⟩`. Set `jl : E →ₗ[R] E'` to `{ toFun := j map_add' := j.map_add map_smul' := fun r e => j.map_smulₛₗ r e }`. Establish `hb : IsBaseChange R' jl` using `GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' jl (fun e => by`. Rewrite using `[LieModel.Lifts, Category.comp_id]`. Conclude with `hj e)`.

Conclude with `hb.inductionOn n P zero base smul add`.
-/
theorem lie_transport_induction [Smooth G.hom] (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S}
    (h : spMap c ≫ x = y) (M : LieModel G x E) (M' : LieModel G y E') (j : E →ₛₗ[c] E')
    (hj : ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left) {P : E' → Prop} (zero : P 0)
    (base : ∀ e, P (j e)) (smul : ∀ (s : R') n, P n → P (s • n))
    (add : ∀ n n', P n → P n' → P (n + n')) (n : E') : P n := by
  subst h
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    rw [mul_smul]⟩
  let jl : E →ₗ[R] E' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => j.map_smulₛₗ r e }
  have hb : IsBaseChange R' jl := GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' jl (fun e => by
    rw [LieModel.Lifts, Category.comp_id]
    exact hj e)
  exact hb.inductionOn n P zero base smul add

end Transport

/- English proof (translation)
Introduce `X G _ _ _ Ω _ ξ Li _ _ M f p q _ hqp hf e he`. Set `c : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1` to `(X.presheaf.stalkSpecializes hqp).hom`. Establish `hc : spMap c ≫ X.fromSpecStalk p.1 = X.fromSpecStalk q.1` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk hqp`. Establish `hgen : ∀ s, genMap ξ q (c s) = genMap ξ p s` using `fun s => LieTangent.genMap_specializes p q.2 hqp s`. Take `⟨E, _, _, ⟨Mp⟩⟩` from `lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)`.

Take `⟨E', _, _, ⟨Mq⟩⟩` from `lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)`. Take `⟨j, hj⟩` from `exists_lie_transport c hc Mp Mq`. Take `⟨jp, hjp⟩` from `exists_lie_transport (genMap ξ p) (LieTangent.spec_genMap ξ p) Mp M`. Take `⟨jq, hjq⟩` from `exists_lie_transport (genMap ξ q) (LieTangent.spec_genMap ξ q) Mq M`. Establish `hcomp : ∀ e₀, jq (j e₀) = jp e₀`.

Introduce `e₀`. Use `M.inj (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Rewrite using `[hjq, hj, hjp, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations.

Apply the tactic sequence `ext <;> simp [hgen]`. Establish `hmem : ∀ e₀, jp e₀ ∈ M.lat p` using `fun e₀ => (M.mem_lat_iff p _).2 ⟨Mp.pt e₀, Mp.tan e₀, hjp e₀⟩`. Take `⟨v, hv⟩` from `(M.mem_lat_iff q e).1 he`. Take `⟨ε, rfl⟩` from `Mq.onto v hv.1`. Establish `he' : e = jq ε` using `M.inj (Over.OverMorphism.ext (hv.2.trans (hjq ε).symm))`.

Substitute `he'` using the available equality. Use `lie_transport_induction c hc Mp Mq j hj (P := fun n => f (jq n) ∈ regAt ξ q) ?_ ?_ ?_ ?_ ε` and prove the remaining obligations. Simplify using `using zero_mem (regAt ξ q)`. Introduce `e₀`. Take `⟨s, hs⟩` from `hf _ (hmem e₀)`.

Rewrite using `[hcomp]`. Conclude with `⟨c s, (hgen s).trans hs⟩`. Introduce `s n hn`. Establish `: f (jq (s • n)) = genMap ξ q s * f (jq n)`. Rewrite using `[jq.map_smulₛₗ, map_smul, smul_eq_mul]`.

Express the relevant statement in the definitionally equal form `f (jq (s • n)) ∈ regAt ξ q`. Rewrite using `[this]`. Conclude with `mul_mem ⟨s, rfl⟩ hn`. Introduce `n n' hn hn'`. Express the relevant statement in the definitionally equal form `f (jq (n + n')) ∈ regAt ξ q`.

Rewrite using `[map_add, map_add]`. Conclude with `add_mem hn hn'`.
-/
theorem lat_form_regular_generizes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (f : Module.Dual Ω Li) (p q : Cpt ξ),
    IsCptGen ξ → q.1 ⤳ p.1 → (∀ e ∈ M.lat p, f e ∈ regAt ξ p) → ∀ e ∈ M.lat q, f e ∈ regAt ξ q := by
  intro X G _ _ _ Ω _ ξ Li _ _ M f p q _ hqp hf e he
  let c : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hqp).hom
  have hc : spMap c ≫ X.fromSpecStalk p.1 = X.fromSpecStalk q.1 :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hqp
  have hgen : ∀ s, genMap ξ q (c s) = genMap ξ p s :=
    fun s => LieTangent.genMap_specializes p q.2 hqp s
  obtain ⟨E, _, _, ⟨Mp⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨E', _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)
  obtain ⟨j, hj⟩ := exists_lie_transport c hc Mp Mq
  obtain ⟨jp, hjp⟩ := exists_lie_transport (genMap ξ p) (LieTangent.spec_genMap ξ p) Mp M
  obtain ⟨jq, hjq⟩ := exists_lie_transport (genMap ξ q) (LieTangent.spec_genMap ξ q) Mq M

  have hcomp : ∀ e₀, jq (j e₀) = jp e₀ := by
    intro e₀
    refine M.inj (Over.OverMorphism.ext ?_)
    rw [hjq, hj, hjp, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    refine RingHom.ext fun a => ?_
    ext <;> simp [hgen]

  have hmem : ∀ e₀, jp e₀ ∈ M.lat p := fun e₀ =>
    (M.mem_lat_iff p _).2 ⟨Mp.pt e₀, Mp.tan e₀, hjp e₀⟩

  obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
  obtain ⟨ε, rfl⟩ := Mq.onto v hv.1
  have he' : e = jq ε := M.inj (Over.OverMorphism.ext (hv.2.trans (hjq ε).symm))
  subst he'
  refine lie_transport_induction c hc Mp Mq j hj (P := fun n => f (jq n) ∈ regAt ξ q) ?_ ?_ ?_ ?_ ε
  · simpa using zero_mem (regAt ξ q)
  · intro e₀
    obtain ⟨s, hs⟩ := hf _ (hmem e₀)
    rw [hcomp]
    exact ⟨c s, (hgen s).trans hs⟩
  · intro s n hn
    have : f (jq (s • n)) = genMap ξ q s * f (jq n) := by
      rw [jq.map_smulₛₗ, map_smul, smul_eq_mul]
    change f (jq (s • n)) ∈ regAt ξ q
    rw [this]
    exact mul_mem ⟨s, rfl⟩ hn
  · intro n n' hn hn'
    change f (jq (n + n')) ∈ regAt ξ q
    rw [map_add, map_add]
    exact add_mem hn hn'

end GlobalTheory.CompanionTheory.Ar.RootHt
