import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefs
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugateStatement

noncomputable section

namespace SheetDecomposition.Cj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped CategoryTheory.Obj ComplexOrder

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
The claim follows from `RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])`.
-/
theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

/- English proof (translation)
Express the relevant statement in the definitionally equal form `dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)`. Conclude with `TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])`.
-/
theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  exact TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

/- English proof (translation)
Establish `h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Conclude with `congrArg (fun p => z p) h`.
-/
theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

/- English proof (translation)
Rewrite using `[← Category.assoc, GlobalTheory.ArchMetricCompare.cj_cj, Category.id_comp]`.
-/
theorem cj_cj (z : Sp ℂ ⟶ X) : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ z = z := by
  rw [← Category.assoc, GlobalTheory.ArchMetricCompare.cj_cj, Category.id_comp]

/- English proof (translation)
Substitute `hx` using the available equality. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Establish `h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ))`. Rewrite using `[← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]`. Establish `h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ)` using `Spec.map_injective h1`.

Substitute `h2` using the available equality. Establish `h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom = (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom)` using `dualMap_comp _ _`. Rewrite using `[h3, CommRingCat.ofHom_comp, Spec.map_comp]`. Conclude with `Category.assoc _ _ _`.
-/
theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ) := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom =
      (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom) := dualMap_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

/- English proof (translation)
Establish `h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) = CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))` using `CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)`. Establish `h3` using `congrArg Spec.map h2`. Simplify `h3` using `only [Spec.map_comp]`.
-/
theorem eps_sq : spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
      CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
    CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
  have h3 := congrArg Spec.map h2
  simpa only [Spec.map_comp] using h3

def cjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, eps_sq, Category.assoc])

/- English proof (translation)
Take `⟨h, v, hv, hl⟩` from `hw`. Establish `hc` using `centre_conj z`. Establish `h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z)` using `hc ▸ h`. Take `⟨v', hv', hl'⟩` from `extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z) (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by`. Use `(Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_` and prove the remaining obligations.

Conclude with `congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)`. Use `⟨h', v', hv', ?_⟩` and prove the remaining obligations. Establish `: (cjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left` using `rfl`. Rewrite using `[this, hl]`. Conclude with `hl'.symm`.
-/
theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (cjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := hw
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (cjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

/- English proof (translation)
Use `h.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, e]`. Use `Eq.trans ?_ (GlobalTheory.PolBaseChange.eSec_comm h).symm` and prove the remaining obligations. Use `Eq.trans hv ?_` and prove the remaining obligations. Use `show (toUnit _ ≫ η[G]).left = _`.

Simplify using `[eSec]`. Establish `z` using `congrArg (· ≫ A.hom) (GlobalTheory.ArchMetricCompare.isTangent_zero A)`. Rewrite using `[← z, Category.assoc, Category.assoc, Over.w, Over.w]`.
-/
theorem isTangent_of_fibre {A : Over (Sp ℂ)} [GrpObj A] {z : Sp ℂ ⟶ X} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ)
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) : IsTangent v' := by
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, e]
    refine Eq.trans ?_ (GlobalTheory.PolBaseChange.eSec_comm h).symm
    refine Eq.trans hv ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (GlobalTheory.ArchMetricCompare.isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

/- English proof (translation)
Take `⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩` from `hF`. Establish `h` using `isGrpPullback_pullback A (spMap (starRingEnd ℂ))`. Use `⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ, GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_, fun p => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hH]`. Conclude with `GlobalTheory.ArchMetricCompare.cj_isAH h u hAH`.

Use `show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ = (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t.act.act a).left`. Rewrite using `[hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ, ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]`. Simplify using `only [Category.assoc]`. Introduce `x y e`. Rewrite `e` using `[hP, hP]`.

Conclude with `hinj (star_injective e)`. Use `show star p ∈ u.Λ ↔ _`. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`.

Conclude with `⟨x, by rw [hP, hx, star_star]⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, by rw [hP, star_star]⟩`. Take `⟨v', e, hd⟩` from `hvec i`. Establish `sq : (spMap (dualMap (starRingEnd ℂ)) ≫ v'.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (starRingEnd ℂ)`.

Rewrite using `[Category.assoc, Over.w]`. Conclude with `eps_sq`. Set `t'' : epsR ℂ ⟶ (Over.pullback (spMap (starRingEnd ℂ))).obj A` to `Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)`. Establish `e' : t''.left ≫ pullback.fst _ _ = spMap (dualMap (starRingEnd ℂ)) ≫ v'.left` using `h.1.lift_fst _ _ _`. Use `⟨t'', ?_, GlobalTheory.ArchMetricCompare.cj_isDiff h u (isTangent_of_fibre hpb (htan i) e) e' hd⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, e', Category.assoc, e]`. Both sides reduce to the same expression.
-/
theorem fibreLatVec_conj {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) (R R' : RiemLat E g Λ) {A₀ : Type}
    (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)) (hP : ∀ x, R'.P x = star (R.P x))
    (hH : R'.Hm = R.Hm.map (starRingEnd ℂ)) (hB : ∀ a x, R'.B a x = star (R.B a (star x)))
    (htan : ∀ a, IsTanAt t.G z (v a)) (hF : FibreLatVec t z R x v) :
    FibreLatVec t (spMap (starRingEnd ℂ) ≫ z) R' (fun a => star (x a)) (fun a => cjVec z (v a)) := by
  obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩ := hF
  have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
  refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
    GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
    fun p => ?_, fun i => ?_⟩
  · rw [hH]
    exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
  · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
      (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t.act.act a).left
    rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
      ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
    simp only [Category.assoc]
  · intro x y e
    rw [hP, hP] at e
    exact hinj (star_injective e)
  · show star p ∈ u.Λ ↔ _
    rw [hmem]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hP, hx, star_star]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [hP, star_star]⟩
  · obtain ⟨v', e, hd⟩ := hvec i
    have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ v'.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (starRingEnd ℂ) := by
      rw [Category.assoc, Over.w]
      exact eps_sq
    let t'' : epsR ℂ ⟶ (Over.pullback (spMap (starRingEnd ℂ))).obj A :=
      Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
    have e' : t''.left ≫ pullback.fst _ _ = spMap (dualMap (starRingEnd ℂ)) ≫ v'.left := h.1.lift_fst _ _ _
    refine ⟨t'', ?_, GlobalTheory.ArchMetricCompare.cj_isDiff h u (isTangent_of_fibre hpb (htan i) e) e' hd⟩
    rw [← Category.assoc, e', Category.assoc, e]
    rfl

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Use `⟨{ toFun := fun x => star (k (star x)) invFun := fun x => star (k.symm (star x)) map_add' := fun x y => by simp map_smul' := fun a x => by simp left_inv := fun x => by simp right_inv := fun x => by simp }, fun x => ?_⟩` and prove the remaining obligations. Use `show R₂'.P (gm x) = star (k (star (R₁'.P x)))`. Rewrite using `[h₁, h₂, hk, star_star]`.
-/
theorem eqvBy_conj {R₁ R₂ R₁' R₂' : RiemLat E g Λ} (h₁ : ∀ x, R₁'.P x = star (R₁.P x))
    (h₂ : ∀ x, R₂'.P x = star (R₂.P x)) {gm : Λ ≃ₗ[𝓞 E] Λ} (h : R₁.EqvBy R₂ gm) : R₁'.EqvBy R₂' gm := by
  obtain ⟨k, hk⟩ := h
  refine ⟨{ toFun := fun x => star (k (star x))
            invFun := fun x => star (k.symm (star x))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by simp
            left_inv := fun x => by simp
            right_inv := fun x => by simp }, fun x => ?_⟩
  show R₂'.P (gm x) = star (k (star (R₁'.P x)))
  rw [h₁, h₂, hk, star_star]

/- English proof (translation)
Use extensionality with `gm`. Use `show (∀ x y, (-f) (gm x) (gm y) = (-f) x y) ↔ ∀ x y, f (gm x) (gm y) = f x y`. Simplify using the standard rewrite rules.
-/
theorem autGrp_neg (f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : autGrp (E := E) (-f) = autGrp f := by
  ext gm
  show (∀ x y, (-f) (gm x) (gm y) = (-f) x y) ↔ ∀ x y, f (gm x) (gm y) = f x y
  simp

/- English proof (translation)
Introduce `τ`. Establish `e : 1 - (ballMat q (star t) τ)ᴴ * ballMat q (star t) τ = (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ`. Use extensionality with `a b`. Simplify using `[ballMat, Matrix.mul_apply, Matrix.one_apply, eq_comm, _root_.mul_comm]`. Rewrite using `[e]`.

Conclude with `(ht τ).transpose`.
-/
theorem star_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {q : Ψ × Fin j × Fin j' ≃ Fin n} {t : Fin n → ℂ}
    (ht : t ∈ ballDom q) : star t ∈ ballDom q := by
  intro τ
  have e : 1 - (ballMat q (star t) τ)ᴴ * ballMat q (star t) τ = (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ := by
    ext a b
    simp [ballMat, Matrix.mul_apply, Matrix.one_apply, eq_comm, _root_.mul_comm]
  rw [e]
  exact (ht τ).transpose

/- English proof (translation)
Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `star_mem_ballDom (q := q) (t := star t) h`. Rewrite `h'` using `[star_star]`. Then use the resulting hypothesis.

Introduce `h`. Conclude with `star_mem_ballDom (q := q) (t := t) h`.
-/
theorem preimage_star_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    star ⁻¹' ballDom q = ballDom q := by
  ext t
  constructor
  · intro h
    have h' := star_mem_ballDom (q := q) (t := star t) h
    rwa [star_star] at h'
  · intro h
    exact star_mem_ballDom (q := q) (t := t) h

/- English proof (translation)
Establish `h1 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ f (star t)` using `(continuous_star.continuousAt (x := t₀)).tendsto.eventually h.eventually_analyticAt`. Use `GlobalTheory.SCV.analyticAt_of_differentiableOn (s := {t | AnalyticAt ℂ f (star t)}) (fun t ht => ?_) h1` and prove the remaining obligations. Use `(show AnalyticAt ℂ f (star t) from ht).differentiableAt.star_star` as an intermediate fact. Rewrite `this` using `[star_star]`. Conclude with `this.differentiableWithinAt`.
-/
theorem analyticAt_star_star {n : ℕ} {f : (Fin n → ℂ) → Fin g → ℂ} {t₀ : Fin n → ℂ} (h : AnalyticAt ℂ f (star t₀)) :
    AnalyticAt ℂ (fun t => star (f (star t))) t₀ := by
  have h1 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ f (star t) :=
    (continuous_star.continuousAt (x := t₀)).tendsto.eventually h.eventually_analyticAt
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn (s := {t | AnalyticAt ℂ f (star t)}) (fun t ht => ?_) h1
  have := (show AnalyticAt ℂ f (star t) from ht).differentiableAt.star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

end SheetDecomposition.Cj
