import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFibre

open GroundTheory.Heights₂.Heights NumberField.ComplexEmbedding

@[instance_reducible]
def coreOfEquiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (c : InnerProductSpace.Core ℂ W) (Φ : V ≃ₗ[ℂ] W) : InnerProductSpace.Core ℂ V where
  inner x y := c.inner (Φ x) (Φ y)
  conj_inner_symm x y := c.conj_inner_symm (Φ x) (Φ y)
  re_inner_nonneg x := c.re_inner_nonneg (Φ x)
  add_left x y z := by simp only [map_add]; exact c.add_left _ _ _
  smul_left x y r := by simp only [map_smul]; exact c.smul_left _ _ _
  definite x hx := Φ.injective (by rw [map_zero]; exact c.definite _ hx)

/- English proof (translation)
Rewrite using `[← c.conj_inner_symm x (y + z), c.add_left, map_add, c.conj_inner_symm, c.conj_inner_symm]`.
-/
theorem core_add_right {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (x y z : V) :
    c.inner x (y + z) = c.inner x y + c.inner x z := by
  rw [← c.conj_inner_symm x (y + z), c.add_left, map_add, c.conj_inner_symm, c.conj_inner_symm]

/- English proof (translation)
Rewrite using `[← c.conj_inner_symm x (r • y), c.smul_left, map_mul, c.conj_inner_symm]`. Simplify using the standard rewrite rules.
-/
theorem core_smul_right {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (x y : V) (r : ℂ) :
    c.inner x (r • y) = r * c.inner x y := by
  rw [← c.conj_inner_symm x (r • y), c.smul_left, map_mul, c.conj_inner_symm]
  simp

/- English proof (translation)
Use `c.add_left 0 0 y` as an intermediate fact. Simplify using `using this`.
-/
theorem core_zero_left {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (y : V) :
    c.inner 0 y = 0 := by
  have := c.add_left 0 0 y
  simpa using this

/- English proof (translation)
Rewrite using `[← c.conj_inner_symm x 0, core_zero_left, map_zero]`.
-/
theorem core_zero_right {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (x : V) :
    c.inner x 0 = 0 := by
  rw [← c.conj_inner_symm x 0, core_zero_left, map_zero]

/- English proof (translation)
Rewrite using `[TensorProduct.smul_tmul', ComplexAt.complex_smul_def, _root_.mul_one]`. Simplify using the standard rewrite rules.
-/
theorem pure_smul {L : Type} [Field L] {E : Type} [AddCommGroup E] [Module (𝓞 L) E] (σ : L →+* ℂ)
    (a : ComplexAt σ) (e : E) :
    a ⊗ₜ[𝓞 L] e = ((ComplexAt.ofComplex σ).symm a : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
  rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def, _root_.mul_one]
  simp

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Apply the tactic sequence `ext a <;> simp [dualMap]`.
-/
theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext a <;> simp [dualMap]

/- English proof (translation)
Use `letI : Module (𝓞 L) Q := Module.compHom Q (σ.comp (algebraMap (𝓞 L) L))`. Set `B : ComplexAt σ →ₗ[𝓞 L] E →ₗ[𝓞 L] Q` to `LinearMap.mk₂ (𝓞 L) (fun a e => ((ComplexAt.ofComplex σ).symm a : ℂ) • j e) (fun a b e => by rw [map_add, add_smul]) (fun r a e => by`. Express the relevant statement in the definitionally equal form `((ComplexAt.ofComplex σ).symm (r • a) : ℂ) • j e = (σ (r : L) : ℂ) • _`. Rewrite using `[ComplexAt.smul_def, map_mul, mul_smul]`. Use the proof step `simp)`.

Use the proof step `(fun a e e' => by rw [map_add, smul_add])`. Use the proof step `(fun r a e => by`. Establish `hr : j (r • e) = (σ (r : L) : ℂ) • j e` using `j.map_smulₛₗ r e`. Express the relevant statement in the definitionally equal form `((ComplexAt.ofComplex σ).symm a : ℂ) • j (r • e) = (σ (r : L) : ℂ) • (((ComplexAt.ofComplex σ).symm a : ℂ) • j e)`. Rewrite using `[hr, smul_comm])`.

Use `⟨{ toFun := TensorProduct.lift B, map_add' := map_add _, map_smul' := ?_ }, fun e => ?_⟩` and prove the remaining obligations. Introduce `c x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`.

Rewrite using `[TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]`. Express the relevant statement in the definitionally equal form `((ComplexAt.ofComplex σ).symm (c • a) : ℂ) • j e = c • ((ComplexAt.ofComplex σ).symm a : ℂ) • j e`. Rewrite using `[ComplexAt.complex_smul_def, map_mul, mul_smul]`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.

Express the relevant statement in the definitionally equal form `TensorProduct.lift B _ = _`. Rewrite using `[TensorProduct.lift.tmul]`. Express the relevant statement in the definitionally equal form `((ComplexAt.ofComplex σ).symm 1 : ℂ) • j e = j e`. Simplify using the standard rewrite rules.
-/
theorem exists_fibreLift {L : Type} [Field L] {E : Type} [AddCommGroup E] [Module (𝓞 L) E] (σ : L →+* ℂ)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (j : E →ₛₗ[σ.comp (algebraMap (𝓞 L) L)] Q) :
    ∃ f : Fibre σ E →ₗ[ℂ] Q, ∀ e, f ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = j e := by
  letI : Module (𝓞 L) Q := Module.compHom Q (σ.comp (algebraMap (𝓞 L) L))
  let B : ComplexAt σ →ₗ[𝓞 L] E →ₗ[𝓞 L] Q := LinearMap.mk₂ (𝓞 L)
    (fun a e => ((ComplexAt.ofComplex σ).symm a : ℂ) • j e)
    (fun a b e => by rw [map_add, add_smul])
    (fun r a e => by
      change ((ComplexAt.ofComplex σ).symm (r • a) : ℂ) • j e = (σ (r : L) : ℂ) • _
      rw [ComplexAt.smul_def, map_mul, mul_smul]
      simp)
    (fun a e e' => by rw [map_add, smul_add])
    (fun r a e => by
      have hr : j (r • e) = (σ (r : L) : ℂ) • j e := j.map_smulₛₗ r e
      change ((ComplexAt.ofComplex σ).symm a : ℂ) • j (r • e) =
        (σ (r : L) : ℂ) • (((ComplexAt.ofComplex σ).symm a : ℂ) • j e)
      rw [hr, smul_comm])
  refine ⟨{ toFun := TensorProduct.lift B, map_add' := map_add _, map_smul' := ?_ }, fun e => ?_⟩
  · intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      change ((ComplexAt.ofComplex σ).symm (c • a) : ℂ) • j e = c • ((ComplexAt.ofComplex σ).symm a : ℂ) • j e
      rw [ComplexAt.complex_smul_def, map_mul, mul_smul]
      simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  · change TensorProduct.lift B _ = _
    rw [TensorProduct.lift.tmul]
    change ((ComplexAt.ofComplex σ).symm 1 : ℂ) • j e = j e
    simp

def oneTmul {L : Type} [Field L] (E : Type) [AddCommGroup E] [Module (𝓞 L) E] (σ : L →+* ℂ) :
    E →ₛₗ[σ.comp (algebraMap (𝓞 L) L)] Fibre σ E where
  toFun e := (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e
  map_add' := TensorProduct.tmul_add _
  map_smul' a e := by
    rw [← TensorProduct.smul_tmul, pure_smul]
    simp [ComplexAt.smul_def]

section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

/- English proof (translation)
Unfold `LieModel.Lifts at h h'`. Rewrite `h`, `h'` using `[Category.comp_id]`. Conclude with `Over.OverMorphism.ext (h.trans h'.symm)`.
-/
theorem lifts_unique {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ X} {E : Type} [AddCommGroup E] [Module R E]
    (MB : LieModel G x E) (c : R →+* R') {x' : Sp R' ⟶ X} {e : E} {v v' : epsAt x' ⟶ G}
    (h : MB.Lifts c (𝟙 G.left) e v) (h' : MB.Lifts c (𝟙 G.left) e v') : v = v' := by
  unfold LieModel.Lifts at h h'
  rw [Category.comp_id] at h h'
  exact Over.OverMorphism.ext (h.trans h'.symm)

/- English proof (translation)
Use `letI : Algebra R C := c.toAlgebra`. Use `letI : Module R V := Module.compHom V c`. Use `letI : Module R Q := Module.compHom Q c`. Use `haveI : IsScalarTower R C V := ⟨fun a b v => by`. Express the relevant statement in the definitionally equal form `(c a * b) • v = c a • (b • v)`.

Conclude with `mul_smul _ _ _⟩`. Use `haveI : IsScalarTower R C Q := ⟨fun a b v => by`. Express the relevant statement in the definitionally equal form `(c a * b) • v = c a • (b • v)`. Conclude with `mul_smul _ _ _⟩`. Set `j' : E →ₗ[R] V` to `{ toFun := j map_add' := j.map_add map_smul' := fun a e => j.map_smulₛₗ a e }`.

Set `g₀ : E →ₗ[R] Q` to `{ toFun := g map_add' := g.map_add map_smul' := fun a e => g.map_smulₛₗ a e }`. Establish `hb : IsBaseChange C j'` using `GlobalTheory.T.lie_model_isBaseChange X G R C x E V MB Mz j' hj`. Conclude with `⟨hb.lift g₀, fun e => hb.lift_eq g₀ e, fun g₂ h2 => hb.algHom_ext' _ _ (LinearMap.ext fun e => (h2 e).trans (hb.lift_eq g₀ e).symm)⟩`.
-/
theorem lie_universal [IsCommMonObj G] [Smooth G.hom] {R C : Type} [CommRing R] [CommRing C] (c : R →+* C) {x : Sp R ⟶ X}
    {E : Type} [AddCommGroup E] [Module R E] {V : Type} [AddCommGroup V] [Module C V]
    (MB : LieModel G x E) (Mz : LieModel G (spMap c ≫ x) V) (j : E →ₛₗ[c] V)
    (hj : ∀ e, MB.Lifts c (𝟙 G.left) e (Mz.pt (j e)))
    {Q : Type} [AddCommGroup Q] [Module C Q] (g : E →ₛₗ[c] Q) :
    ∃ g' : V →ₗ[C] Q, (∀ e, g' (j e) = g e) ∧ ∀ g₂ : V →ₗ[C] Q, (∀ e, g₂ (j e) = g e) → g₂ = g' := by
  letI : Algebra R C := c.toAlgebra
  letI : Module R V := Module.compHom V c
  letI : Module R Q := Module.compHom Q c
  haveI : IsScalarTower R C V := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    exact mul_smul _ _ _⟩
  haveI : IsScalarTower R C Q := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    exact mul_smul _ _ _⟩
  let j' : E →ₗ[R] V :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a e => j.map_smulₛₗ a e }
  let g₀ : E →ₗ[R] Q :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun a e => g.map_smulₛₗ a e }
  have hb : IsBaseChange C j' := GlobalTheory.T.lie_model_isBaseChange X G R C x E V MB Mz j' hj
  exact ⟨hb.lift g₀, fun e => hb.lift_eq g₀ e, fun g₂ h2 =>
    hb.algHom_ext' _ _ (LinearMap.ext fun e => (h2 e).trans (hb.lift_eq g₀ e).symm)⟩
end

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X}
  {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  {M : LieModel G ξ Li} {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ X}
  {E : Type} [AddCommGroup E] [Module (𝓞 L) E]

/- English proof (translation)
Take `⟨V, iA, iM, ⟨Mz⟩⟩` from `lieModel_exists X G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)`. Take `⟨j, hj, -⟩` from `LieBaseChange.existsUnique_semilinear_lifts X G (𝓞 L) ℂ (σ.comp (algebraMap (𝓞 L) L)) z E V MB Mz`. Take `⟨f, hf⟩` from `exists_fibreLift σ j`. Take `⟨g, hg, -⟩` from `lie_universal _ MB Mz j hj (oneTmul E σ)`. Take `⟨i, -, hi⟩` from `lie_universal _ MB Mz j hj j`.

Establish `hfg : f ∘ₗ g = LinearMap.id`. Rewrite using `[hi (f ∘ₗ g) (fun e => ?_), hi LinearMap.id (fun e => rfl)]`. Express the relevant statement in the definitionally equal form `f (g (j e)) = j e`. Rewrite using `[hg]`. Conclude with `hf e`.

Establish `hgf : g ∘ₗ f = LinearMap.id`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`.

Rewrite using `[pure_smul, map_smul, map_smul]`. Express the relevant statement in the definitionally equal form `_ • g (f _) = _`. Rewrite using `[hf, hg]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Use `⟨V, iA, iM, Mz, LinearEquiv.ofLinear f g hfg hgf, fun e => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `MB.Lifts _ _ e (Mz.pt (f _))`. Rewrite using `[hf]`. Conclude with `hj e`.
-/
theorem exists_fibreEquiv (MB : LieModel G z E) (σ : L →+* ℂ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (Mz : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) V)
      (Φ : Fibre σ E ≃ₗ[ℂ] V),
      ∀ e, MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e (Mz.pt (Φ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e))) := by
  obtain ⟨V, iA, iM, ⟨Mz⟩⟩ := lieModel_exists X G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts X G (𝓞 L) ℂ (σ.comp (algebraMap (𝓞 L) L)) z E V MB Mz
  obtain ⟨f, hf⟩ := exists_fibreLift σ j
  obtain ⟨g, hg, -⟩ := lie_universal _ MB Mz j hj (oneTmul E σ)
  obtain ⟨i, -, hi⟩ := lie_universal _ MB Mz j hj j
  have hfg : f ∘ₗ g = LinearMap.id := by
    rw [hi (f ∘ₗ g) (fun e => ?_), hi LinearMap.id (fun e => rfl)]
    change f (g (j e)) = j e
    rw [hg]; exact hf e
  have hgf : g ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [pure_smul, map_smul, map_smul]
      change _ • g (f _) = _
      rw [hf, hg]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨V, iA, iM, Mz, LinearEquiv.ofLinear f g hfg hgf, fun e => ?_⟩
  change MB.Lifts _ _ e (Mz.pt (f _))
  rw [hf]
  exact hj e

/- English proof (translation)
Take `⟨V, iA, iM, Mz, Φ, hΦ⟩` from `exists_fibreEquiv MB σ`. Take `⟨core, hcore⟩` from `h.herm _ V Mz`. Conclude with `⟨coreOfEquiv core Φ, fun a => Mz.pt (Φ a), fun a b => hcore _ _, hΦ⟩`.
-/
theorem exists_core (h : LieMetric M y) (MB : LieModel G z E) (σ : L →+* ℂ) :
    ∃ (core : InnerProductSpace.Core ℂ (Fibre σ E))
      (P : Fibre σ E → (epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G)),
      (∀ a b, core.inner a b = h.ip _ (P a) (P b)) ∧
        ∀ e, MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e (P ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e)) := by
  obtain ⟨V, iA, iM, Mz, Φ, hΦ⟩ := exists_fibreEquiv MB σ
  obtain ⟨core, hcore⟩ := h.herm _ V Mz
  exact ⟨coreOfEquiv core Φ, fun a => Mz.pt (Φ a), fun a b => hcore _ _, hΦ⟩

/- English proof (translation)
Establish `key : ∀ (z₁ z₂ : Sp ℂ ⟶ X) (_ : z₂ = spMap (starRingEnd ℂ) ≫ z₁) (v w : epsAt z₁ ⟶ G) (v' w' : epsAt z₂ ⟶ G), v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left → h.ip z₂ v' w' = starRingEnd ℂ (h.ip z₁ v w)`. Introduce `z₁ z₂ hz v w v' w' h1 h2`. Substitute `hz` using the available equality. Conclude with `h.conj z₁ v w v' w' h1 h2`. Establish `hc : (NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L) = (starRingEnd ℂ).comp (σ.comp (algebraMap (𝓞 L) L))`.

Use extensionality with `a`. Both sides reduce to the same expression. Unfold `LieModel.Lifts at hv hw hv' hw'`. Rewrite `hv`, `hw`, `hv'`, `hw'` using `[Category.comp_id]`. Use `key _ _ ?_ v w v' w' ?_ ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, spMap_spMap', hc]`. Rewrite using `[hv, hv', hc, dualMap_comp', ← Category.assoc, spMap_spMap']`. Rewrite using `[hw, hw', hc, dualMap_comp', ← Category.assoc, spMap_spMap']`.
-/
theorem ip_conj (h : LieMetric M y) (MB : LieModel G z E) (σ : L →+* ℂ) (e f : E)
    {v w : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G}
    {v' w' : epsAt (spMap ((NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G}
    (hv : MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e v)
    (hw : MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) f w)
    (hv' : MB.Lifts ((NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e v')
    (hw' : MB.Lifts ((NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L)) (𝟙 G.left) f w') :
    h.ip _ v' w' = starRingEnd ℂ (h.ip _ v w) := by
  have key : ∀ (z₁ z₂ : Sp ℂ ⟶ X) (_ : z₂ = spMap (starRingEnd ℂ) ≫ z₁) (v w : epsAt z₁ ⟶ G) (v' w' : epsAt z₂ ⟶ G),
      v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left →
      h.ip z₂ v' w' = starRingEnd ℂ (h.ip z₁ v w) := by
    intro z₁ z₂ hz v w v' w' h1 h2
    subst hz
    exact h.conj z₁ v w v' w' h1 h2
  have hc : (NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L) =
      (starRingEnd ℂ).comp (σ.comp (algebraMap (𝓞 L) L)) := by
    ext a; rfl
  unfold LieModel.Lifts at hv hw hv' hw'
  rw [Category.comp_id] at hv hw hv' hw'
  refine key _ _ ?_ v w v' w' ?_ ?_
  · rw [← Category.assoc, spMap_spMap', hc]
  · rw [hv, hv', hc, dualMap_comp', ← Category.assoc, spMap_spMap']
  · rw [hw, hw', hc, dualMap_comp', ← Category.assoc, spMap_spMap']

/- English proof (translation)
Establish `h1 : ∀ e : E, conjMap σ E ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = (1 : ComplexAt (NumberField.ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e` using `fun e => by`. Rewrite using `[conjMap_tmul, map_one]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, core_zero_left]`. Consider the case `add x x' hx hx' => simp only [map_add, (core _).add_left, hx, hx']`.

Consider the case `tmul a e`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, core_zero_right]`. Consider the case `add y y' hy hy' => simp only [map_add, core_add_right, hy, hy']`. Consider the case `tmul b f`.

Rewrite using `[pure_smul σ a e, pure_smul σ b f, conjMap_smul, conjMap_smul, h1, h1, (core _).smul_left, core_smul_right, (core _).smul_left, core_smul_right, h]`. Simplify using `only [map_mul, Complex.conj_conj]`.
-/
theorem form_conj_of_pure (core : ∀ σ : L →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ E))
    (h : ∀ (σ : L →+* ℂ) (e f : E),
      (core (NumberField.ComplexEmbedding.conjugate σ)).inner
        ((1 : ComplexAt (NumberField.ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e)
        ((1 : ComplexAt (NumberField.ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] f) =
      starRingEnd ℂ ((core σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f)))
    (σ : L →+* ℂ) (x y : Fibre σ E) :
    (core (NumberField.ComplexEmbedding.conjugate σ)).inner (conjMap σ E x) (conjMap σ E y) =
      starRingEnd ℂ ((core σ).inner x y) := by
  have h1 : ∀ e : E, conjMap σ E ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) =
      (1 : ComplexAt (NumberField.ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e := fun e => by
    rw [conjMap_tmul, map_one]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, core_zero_left]
  | add x x' hx hx' => simp only [map_add, (core _).add_left, hx, hx']
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, core_zero_right]
    | add y y' hy hy' => simp only [map_add, core_add_right, hy, hy']
    | tmul b f =>
      rw [pure_smul σ a e, pure_smul σ b f, conjMap_smul, conjMap_smul, h1, h1, (core _).smul_left, core_smul_right,
        (core _).smul_left, core_smul_right, h]
      simp only [map_mul, Complex.conj_conj]

end

end GlobalTheory.CompanionTheory.Ar.LieFibre

open GlobalTheory.CompanionTheory.Ar.LieFibre GroundTheory.Heights₂.Heights in

/- English proof (translation)
Introduce `X Ω _ K _ J _ y ξ G _ _ _ Li _ _ M h L _ _ z`. Take `⟨E, iA, iM, ⟨MB⟩⟩` from `lieModel_exists X G (𝓞 L) z`. Take `⟨hf, hp⟩` from `GlobalTheory.T.lie_model_finite_projective X G (𝓞 L) z E MB`. Use `choose core P hcore hlift using fun σ : L →+* ℂ => exists_core h MB σ`. Establish `hconj` using `form_conj_of_pure core (fun σ e f => by`.

Rewrite using `[hcore, hcore]`. Conclude with `ip_conj h MB σ e f (hlift σ e) (hlift σ f) (hlift _ e) (hlift _ f))`. Use `⟨@HermitianBundle.mk L _ _ E iA iM hf hp ⟨core, hconj⟩, MB, ?_⟩` and prove the remaining obligations. Introduce `σ x x' v v' hv hv'`. Express the relevant statement in the definitionally equal form `(core σ).inner _ _ = _`.

Rewrite using `[hcore, lifts_unique MB _ (hlift σ x) hv, lifts_unique MB _ (hlift σ x') hv']`.
-/
theorem GlobalTheory.CompanionTheory.Ar.lie_fibre_exists : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X), ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB := by
  intro X Ω _ K _ J _ y ξ G _ _ _ Li _ _ M h L _ _ z
  obtain ⟨E, iA, iM, ⟨MB⟩⟩ := lieModel_exists X G (𝓞 L) z
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G (𝓞 L) z E MB
  choose core P hcore hlift using fun σ : L →+* ℂ => exists_core h MB σ
  have hconj := form_conj_of_pure core (fun σ e f => by
    rw [hcore, hcore]
    exact ip_conj h MB σ e f (hlift σ e) (hlift σ f) (hlift _ e) (hlift _ f))
  refine ⟨@HermitianBundle.mk L _ _ E iA iM hf hp ⟨core, hconj⟩, MB, ?_⟩
  intro σ x x' v v' hv hv'
  change (core σ).inner _ _ = _
  rw [hcore, lifts_unique MB _ (hlift σ x) hv, lifts_unique MB _ (hlift σ x') hv']
