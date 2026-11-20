import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration.Isomove

noncomputable section Move

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}

/- English proof (translation)
Rewrite using `[Hom.one_def]`. Simplify using the standard rewrite rules.
-/
theorem mv_one_left {Y : Scheme.{0}} (y : Y ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ (η[G]).left := by
  rw [Hom.one_def]
  simp

omit [GrpObj G] [GrpObj G'] in
/- English proof (translation)
Use `⟨Over.homMk (a'.left ≫ φ) ?_, rfl⟩` and prove the remaining obligations. Establish `hw` using `Over.w a'`. Simplify using `only [Over.mk_hom] at hw ⊢`. Rewrite using `[Category.assoc, w, ← Category.assoc, hw, hy]`.
-/
theorem mv_push (w : φ ≫ G.hom = G'.hom ≫ f) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    (a' : Over.mk y' ⟶ G') : ∃ a : Over.mk y ⟶ G, a'.left ≫ φ = a.left := by
  refine ⟨Over.homMk (a'.left ≫ φ) ?_, rfl⟩
  have hw := Over.w a'
  simp only [Over.mk_hom] at hw ⊢
  rw [Category.assoc, w, ← Category.assoc, hw, hy]

/- English proof (translation)
Substitute `hy` using the available equality. Conclude with `(h.2 (Over.mk y') a' b' a b ha.symm hb.symm).symm`.
-/
theorem mv_mul (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    {a' b' : Over.mk y' ⟶ G'} {a b : Over.mk y ⟶ G} (ha : a'.left ≫ φ = a.left) (hb : b'.left ≫ φ = b.left) :
    (a' * b').left ≫ φ = (a * b).left := by
  subst hy
  exact (h.2 (Over.mk y') a' b' a b ha.symm hb.symm).symm

/- English proof (translation)
Establish `hm` using `mv_mul h hy he he`. Rewrite `hm` using `[show (1 : Over.mk y' ⟶ G') * 1 = 1 from mul_one _, he]`. Establish `hee : e * e = e` using `(Over.OverMorphism.ext hm).symm`. Simplify using `using congrArg (· * e⁻¹) hee`.
-/
private theorem mv_one_lemma (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X}
    (hy : y' ≫ f = y) (e : Over.mk y ⟶ G) (he : (1 : Over.mk y' ⟶ G').left ≫ φ = e.left) : e = 1 := by
  have hm := mv_mul h hy he he
  rw [show (1 : Over.mk y' ⟶ G') * 1 = 1 from mul_one _, he] at hm
  have hee : e * e = e := (Over.OverMorphism.ext hm).symm
  simpa using congrArg (· * e⁻¹) hee

/- English proof (translation)
Take `⟨e, he⟩` from `mv_push (φ := φ) h.1.w hy (1 : Over.mk y' ⟶ G')`. Rewrite using `[he, mv_one_lemma h hy e he]`.
-/
theorem mv_one (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y) :
    (1 : Over.mk y' ⟶ G').left ≫ φ = (1 : Over.mk y ⟶ G).left := by
  obtain ⟨e, he⟩ := mv_push (φ := φ) h.1.w hy (1 : Over.mk y' ⟶ G')
  rw [he, mv_one_lemma h hy e he]

/- English proof (translation)
Establish `key : ∀ k : ℕ, (a' ^ k).left ≫ φ = (a ^ k).left`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa only [pow_zero] using mv_one h hy`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, pow_succ]`. Conclude with `mv_mul h hy ih ha`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← key n, hn, mv_one h hy]`.
-/
theorem mv_pow (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    {a' : Over.mk y' ⟶ G'} {a : Over.mk y ⟶ G} (ha : a'.left ≫ φ = a.left) {n : ℕ} (hn : a' ^ n = 1) :
    a ^ n = 1 := by
  have key : ∀ k : ℕ, (a' ^ k).left ≫ φ = (a ^ k).left := by
    intro k
    induction k with
    | zero => simpa only [pow_zero] using mv_one h hy
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mv_mul h hy ih ha
  apply Over.OverMorphism.ext
  rw [← key n, hn, mv_one h hy]

/- English proof (translation)
Use `mv_one h (y' := 𝟙 X') (y := f) (Category.id_comp f)` as an intermediate fact. Simplify `this` using `[mv_one_left]`.
-/
theorem mv_eta (h : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have := mv_one h (y' := 𝟙 X') (y := f) (Category.id_comp f)
  simpa [mv_one_left] using this

/- English proof (translation)
Unfold `IsTanAt at ht ⊢`. Rewrite using `[← hv, ← Category.assoc, ht]`. Conclude with `mv_one h hx`.
-/
theorem mv_tan (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X}
    (hx : x' ≫ f = x) {v' : epsAt x' ⟶ G'} {v : epsAt x ⟶ G} (hv : v'.left ≫ φ = v.left) (ht : IsTanAt G' x' v') :
    IsTanAt G x v := by
  unfold IsTanAt at ht ⊢
  rw [← hv, ← Category.assoc, ht]
  exact mv_one h hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dualMap_lemma {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') (a : DualNumber R) :
    dualMap σ a = TrivSqZeroExt.inl (σ a.fst) + TrivSqZeroExt.inr (σ a.snd) := rfl

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMap_lemma, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem mv_dual_alg {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') :
    spMap (dualMap σ) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  ext <;> simp [dualMap_lemma, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[dualMap_lemma]`.
-/
theorem mv_dual_fst {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap σ) =
      spMap σ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [dualMap_lemma]

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMap_lemma]`.
-/
theorem mv_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (σ : R →+* R') (τ : R' →+* R'') :
    spMap (dualMap τ) ≫ spMap (dualMap σ) = spMap (dualMap (τ.comp σ)) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap_lemma]

/- English proof (translation)
Use `⟨Over.homMk (spMap (dualMap σ) ≫ v.left) ?_, rfl, ?_⟩` and prove the remaining obligations. Establish `hw` using `Over.w v`. Simplify using `only [epsAt, Over.mk_hom] at hw ⊢`. Rewrite using `[Category.assoc, hw, ← Category.assoc, mv_dual_alg, Category.assoc, hx]`. Introduce `ht`.

Unfold `IsTanAt at ht ⊢`. Simplify using `only [Over.homMk_left]`. Rewrite using `[← Category.assoc, mv_dual_fst, Category.assoc, ht, mv_one_left, mv_one_left, ← Category.assoc, hx]`.
-/
theorem mv_bc {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {x : Sp R ⟶ X} {x' : Sp R' ⟶ X}
    (hx : spMap σ ≫ x = x') (v : epsAt x ⟶ G) :
    ∃ v' : epsAt x' ⟶ G, v'.left = spMap (dualMap σ) ≫ v.left ∧ (IsTanAt G x v → IsTanAt G x' v') := by
  refine ⟨Over.homMk (spMap (dualMap σ) ≫ v.left) ?_, rfl, ?_⟩
  · have hw := Over.w v
    simp only [epsAt, Over.mk_hom] at hw ⊢
    rw [Category.assoc, hw, ← Category.assoc, mv_dual_alg, Category.assoc, hx]
  · intro ht
    unfold IsTanAt at ht ⊢
    simp only [Over.homMk_left]
    rw [← Category.assoc, mv_dual_fst, Category.assoc, ht, mv_one_left, mv_one_left, ← Category.assoc, hx]

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Take `⟨q, hqs⟩` from `q`. Take `⟨q', hq's⟩` from `q'`. Express the relevant statement in the definitionally equal form `f q' = q at hq`. Substitute `hq hξ` using the available equality. Express the relevant statement in the definitionally equal form `ξ' (IsLocalRing.closedPoint Ω) ⤳ q' at hq's`.

Express the relevant statement in the definitionally equal form `f (ξ' (IsLocalRing.closedPoint Ω)) ⤳ f q' at hqs`. Use `⟨(f.stalkMap q').hom, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[spMap]`. Express the relevant statement in the definitionally equal form `(X'.presheaf.stalkSpecializes hq's ≫ Scheme.stalkClosedPointTo ξ').hom.comp (f.stalkMap q').hom = (X.presheaf.stalkSpecializes hqs ≫ Scheme.stalkClosedPointTo (ξ' ≫ f)).hom`. Rewrite using `[← CommRingCat.hom_comp]`.

Apply `congrArg CommRingCat.Hom.hom` to reduce the goal to its premises. Rewrite using `[Scheme.stalkClosedPointTo_comp]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Conclude with `(Scheme.Hom.stalkSpecializes_stalkMap f _ q' hq's).symm`.

Use `_ = _ := Category.assoc _ _ _`. Introduce `hf`. Conclude with `ConcreteCategory.bijective_of_isIso (f.stalkMap q')`.
-/
theorem mv_stalk {ξ' : Sp Ω ⟶ X'} {ξ : Sp Ω ⟶ X} (hξ : ξ' ≫ f = ξ) (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) :
    ∃ σ : X.presheaf.stalk q.1 →+* X'.presheaf.stalk q'.1,
      spMap σ ≫ X.fromSpecStalk q.1 = X'.fromSpecStalk q'.1 ≫ f ∧ (genMap ξ' q').comp σ = genMap ξ q ∧
      (IsIso f → Function.Bijective σ) := by
  obtain ⟨q, hqs⟩ := q
  obtain ⟨q', hq's⟩ := q'
  change f q' = q at hq
  subst hq hξ
  change ξ' (IsLocalRing.closedPoint Ω) ⤳ q' at hq's
  change f (ξ' (IsLocalRing.closedPoint Ω)) ⤳ f q' at hqs
  refine ⟨(f.stalkMap q').hom, ?_, ?_, ?_⟩
  · simp [spMap]
  · change (X'.presheaf.stalkSpecializes hq's ≫ Scheme.stalkClosedPointTo ξ').hom.comp (f.stalkMap q').hom =
      (X.presheaf.stalkSpecializes hqs ≫ Scheme.stalkClosedPointTo (ξ' ≫ f)).hom
    rw [← CommRingCat.hom_comp]
    apply congrArg CommRingCat.Hom.hom
    rw [Scheme.stalkClosedPointTo_comp]
    calc _ = (f.stalkMap q' ≫ X'.presheaf.stalkSpecializes hq's) ≫ Scheme.stalkClosedPointTo ξ' :=
          (Category.assoc _ _ _).symm
      _ = (X.presheaf.stalkSpecializes hqs ≫ f.stalkMap _) ≫ Scheme.stalkClosedPointTo ξ' := by
          congr 1
          exact (Scheme.Hom.stalkSpecializes_stalkMap f _ q' hq's).symm
      _ = _ := Category.assoc _ _ _
  · intro hf
    exact ConcreteCategory.bijective_of_isIso (f.stalkMap q')

/- English proof (translation)
Take `⟨σ, -, hσ, -⟩` from `mv_stalk hξ q' q hq`. Unfold `regAt`. Rewrite using `[← hσ]`. Introduce and unpack `_ ⟨r, rfl⟩`. Conclude with `⟨σ r, rfl⟩`.
-/
theorem mv_regAt_le {ξ' : Sp Ω ⟶ X'} {ξ : Sp Ω ⟶ X} (hξ : ξ' ≫ f = ξ) (q' : Cpt ξ') (q : Cpt ξ)
    (hq : f q'.1 = q.1) : regAt ξ q ≤ regAt ξ' q' := by
  obtain ⟨σ, -, hσ, -⟩ := mv_stalk hξ q' q hq
  unfold regAt
  rw [← hσ]
  rintro _ ⟨r, rfl⟩
  exact ⟨σ r, rfl⟩

/- English proof (translation)
Substitute `hy` using the available equality. Unfold `secVal`. Use `congr 1`.
-/
theorem mv_secVal_comp {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Sp B ⟶ Z) (ψ : Z ⟶ Z') (y : Sp B ⟶ Z')
    (hy : x ≫ ψ = y) (W : Z'.Opens) (s : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W) :
    secVal x (ψ ⁻¹ᵁ W) h ((ψ.app W).hom s) = secVal y W h' s := by
  subst hy
  unfold secVal
  congr 1

/- English proof (translation)
Substitute `hy` using the available equality. Establish `key : Scheme.Hom.appLE (spMap σ ≫ x) W ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).hom = Scheme.Hom.appLE x W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom σ`. Rewrite using `[← Scheme.ΓSpecIso_naturality, ← Category.assoc]`. Use `congr 1`. Use `congrArg (fun g => g.hom s) key` as an intermediate fact.

Simplify `this` using `[secVal]`.
-/
theorem mv_secVal_bc {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') {Z : Scheme.{0}} (x : Sp B ⟶ Z)
    (y : Sp B' ⟶ Z) (hy : spMap σ ≫ x = y) (W : Z.Opens) (s : Γ(Z, W)) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W) :
    secVal y W h' s = σ (secVal x W h s) := by
  subst hy
  have key : Scheme.Hom.appLE (spMap σ ≫ x) W ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).hom =
      Scheme.Hom.appLE x W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom σ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc]
    congr 1
  have := congrArg (fun g => g.hom s) key
  simpa [secVal] using this

end Move

end PositivityTheory.UnitarySelfGeneration.Isomove
