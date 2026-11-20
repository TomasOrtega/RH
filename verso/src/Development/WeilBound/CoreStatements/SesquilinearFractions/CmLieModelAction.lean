import Development.WeilBound.CoreStatements.SesquilinearFractions.CmPackLieProperties
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.cm_lie_model_action

open PositivityTheory.Xgf.isogeny_decomposition_product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}
  (X : CMPack Z c FU i hP)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `X.m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hM1, Over.comp_left, Category.assoc, X.m.act, ← Category.assoc, hM1, hρm X s e, Over.comp_left]`. Rewrite using `[Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]`.
-/
theorem act1 (s : 𝓞 E) (e : Fin g → X.K) : (curveLieModel X).pt (ρm X s e) = (curveLieModel X).pt e ≫ X.t.act.act s := by
  apply Over.OverMorphism.ext
  apply X.m.cart.1.hom_ext
  · rw [hM1, Over.comp_left, Category.assoc, X.m.act, ← Category.assoc, hM1, hρm X s e, Over.comp_left]
  · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]

/- English proof (translation)
Rewrite using `[← hM2, act1, Over.comp_left, Category.assoc, X.m'.act, ← Category.assoc, hM2, Over.comp_left]`.
-/
theorem act2 (s : 𝓞 E) (e : Fin g → X.K) : ((integralLieModel X).pt (ρm X s e)).left = ((integralLieModel X).pt e ≫ X.B.t.act.act s).left := by
  rw [← hM2, act1, Over.comp_left, Category.assoc, X.m'.act, ← Category.assoc, hM2, Over.comp_left]

/- English proof (translation)
Introduce `b a a'`. Use `haveI := ((X.fam b).1 a).isMonHom`. Apply `(integralLieModel X).inj` to reduce the goal to its premises. Rewrite using `[(integralLieModel X).add, lam_spec, lam_spec, lam_spec]`. Unfold `wB`.

Rewrite using `[(X.fam b).2.1 a a', MonObj.comp_mul, MonObj.comp_mul]`.
-/
theorem lamAdd : LamAdd X := by
  intro b a a'
  haveI := ((X.fam b).1 a).isMonHom
  apply (integralLieModel X).inj
  rw [(integralLieModel X).add, lam_spec, lam_spec, lam_spec]
  unfold wB
  rw [(X.fam b).2.1 a a', MonObj.comp_mul, MonObj.comp_mul]

/- English proof (translation)
Introduce `b s a`. Apply `(integralLieModel X).inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[act2, lam_spec, lam_spec]`. Unfold `wB`.

Rewrite using `[(X.fam b).2.2.1 s a]`. Simplify using `only [Category.assoc]`.
-/
theorem lamSmul : LamSmul X := by
  intro b s a
  apply (integralLieModel X).inj
  apply Over.OverMorphism.ext
  rw [act2, lam_spec, lam_spec]
  unfold wB
  rw [(X.fam b).2.2.1 s a]
  simp only [Category.assoc]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite `h`, the goal using `[← Spec.map_preimage f1, ← Spec.map_preimage f2]`. Use `congr 1`. Rewrite `h` using `[spMap, ← Spec.map_comp, ← Spec.map_comp]`. Establish `h'` using `Spec.map_injective h`. Establish `hc : (Spec.preimage f1).hom.comp (algebraMap (𝓞 K) K) = (Spec.preimage f2).hom.comp (algebraMap (𝓞 K) K)`.

Use extensionality with `y`. Conclude with `congrArg (fun φ => φ.hom y) h'`. Use extensionality with `x`. Conclude with `congrFun (congrArg DFunLike.coe (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) hc)) x`.
-/
theorem cancel_frac {A : Type} [CommRing A] (K : Type) [Field K] [NumberField K] (f1 f2 : Sp A ⟶ Sp K)
    (h : f1 ≫ spMap (algebraMap (𝓞 K) K) = f2 ≫ spMap (algebraMap (𝓞 K) K)) : f1 = f2 := by
  rw [← Spec.map_preimage f1, ← Spec.map_preimage f2] at h ⊢
  congr 1
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hc : (Spec.preimage f1).hom.comp (algebraMap (𝓞 K) K) = (Spec.preimage f2).hom.comp (algebraMap (𝓞 K) K) := by
    ext y; exact congrArg (fun φ => φ.hom y) h'
  ext x
  exact congrFun (congrArg DFunLike.coe (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) hc)) x

/- English proof (translation)
Unfold `wB`. Rewrite using `[Over.comp_left, Over.comp_left, bK_left]`.
-/
theorem wB_left (b : Bool) (a : PureType.lat hP (sgnRt H b)) :
    (wB X b a).left = spMap (dualMap (algebraMap (𝓞 X.K) X.K)) ≫ (X.C b).v.left ≫ (X.ψ b a).left := by
  unfold wB; rw [Over.comp_left, Over.comp_left, bK_left]

/- English proof (translation)
Introduce `b a u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr1, hr2⟩`. Establish `hW : r ≫ X.m'.φ = ((curveLieModel X).pt (lam X b a)).left ≫ X.m'.φ`. Rewrite using `[hr2, hM2, lam_spec, wB_left]`.

Establish `r0eq : r = ((curveLieModel X).pt (lam X b a)).left`. Apply `X.m'.cart.1.hom_ext hW` to reduce the goal to its premises. Apply `cancel_frac` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, ← X.m'.cart.1.w, ← Category.assoc, ← Category.assoc, hW]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[← hr1, r0eq, hM1]`. Introduce and unpack `rfl`. Conclude with `⟨((curveLieModel X).pt (lam X b a)).left, hM1 X _, by rw [hM2, lam_spec, wB_left]⟩`.
-/
theorem imageIff : ImageIff X := by
  intro b a u
  constructor
  · rintro ⟨r, hr1, hr2⟩
    have hW : r ≫ X.m'.φ = ((curveLieModel X).pt (lam X b a)).left ≫ X.m'.φ := by
      rw [hr2, hM2, lam_spec, wB_left]
    have r0eq : r = ((curveLieModel X).pt (lam X b a)).left := by
      apply X.m'.cart.1.hom_ext hW
      apply cancel_frac
      rw [Category.assoc, Category.assoc, ← X.m'.cart.1.w, ← Category.assoc, ← Category.assoc, hW]
    apply Over.OverMorphism.ext
    rw [← hr1, r0eq, hM1]
  · rintro rfl
    exact ⟨((curveLieModel X).pt (lam X b a)).left, hM1 X _, by rw [hM2, lam_spec, wB_left]⟩

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite using `[isogeny_decomposition_product.spMap_comp, isogeny_decomposition_product.spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]`.
-/
theorem bc_epsx {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) (x : R) :
    spMap (dualMap f) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul x) = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (f x)) ≫ spMap (dualMap f) := by
  rw [isogeny_decomposition_product.spMap_comp, isogeny_decomposition_product.spMap_comp]
  congr 1
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

/- English proof (translation)
Apply `(integralLieModel X).inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[(integralLieModel X).smul, lam_spec, lam_spec, wB_left, wB_left, (X.fam b).2.2.1 H.w0 a]`. Take `⟨u, hu, hw⟩` from `(X.C b).eig`. Establish `hcomm` using `((X.fam b).1 a).comm (wK H)`.

Establish `hv : ((X.C b).v ≫ (X.C b).act.act (wK H)).left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (X.ω b)) ≫ (X.C b).v.left`. Rewrite using `[hw]`. Use `hu 0` as an intermediate fact. Simplify using `only [Matrix.cons_val_zero] at this`. Simplify using `[List.ofFn_succ, this, epsScaleR_eq]`.

Establish `h2 : (X.C b).v.left ≫ (X.ψ b a ≫ X.B.t.act.act H.w0).left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (X.ω b)) ≫ (X.C b).v.left ≫ (X.ψ b a).left`. Establish `hcomm' : (X.C b).act.act (wK H) ≫ X.ψ b a = X.ψ b a ≫ X.B.t.act.act H.w0`. Rewrite using `[hcomm]`. Both sides reduce to the same expression. Rewrite using `[← hcomm', Over.comp_left, ← Category.assoc, ← Over.comp_left, hv, Category.assoc]`.

Rewrite using `[h2, ← Category.assoc, bc_epsx, Category.assoc]`.
-/
theorem lam_smul_w0 (b : Bool) (a : PureType.lat hP (sgnRt H b)) :
    lam X b (H.w0 • a) = algebraMap (𝓞 X.K) X.K (X.ω b) • lam X b a := by
  apply (integralLieModel X).inj
  apply Over.OverMorphism.ext
  rw [(integralLieModel X).smul, lam_spec, lam_spec, wB_left, wB_left, (X.fam b).2.2.1 H.w0 a]
  obtain ⟨u, hu, hw⟩ := (X.C b).eig
  have hcomm := ((X.fam b).1 a).comm (wK H)
  have hv : ((X.C b).v ≫ (X.C b).act.act (wK H)).left =
      spMap (GlobalTheory.CompanionTheory.Ar.epsMul (X.ω b)) ≫ (X.C b).v.left := by
    rw [hw]
    have := hu 0
    simp only [Matrix.cons_val_zero] at this
    simp [List.ofFn_succ, this, epsScaleR_eq]
  have h2 : (X.C b).v.left ≫ (X.ψ b a ≫ X.B.t.act.act H.w0).left =
      spMap (GlobalTheory.CompanionTheory.Ar.epsMul (X.ω b)) ≫ (X.C b).v.left ≫ (X.ψ b a).left := by
    have hcomm' : (X.C b).act.act (wK H) ≫ X.ψ b a = X.ψ b a ≫ X.B.t.act.act H.w0 := by
      rw [hcomm]; rfl
    rw [← hcomm', Over.comp_left, ← Category.assoc, ← Over.comp_left, hv, Category.assoc]
  rw [h2, ← Category.assoc, bc_epsx, Category.assoc]

/- English proof (translation)
Introduce `b s a hs`. Establish `hrt : H.rt = 2 * H.w0 - 1` using `by linear_combination H.two_weight_eq_one_add_root.symm`. Establish `hsm` using `lamSmul X b H.w0 a`. Rewrite `hsm` using `[lam_smul_w0]`. Establish `hω : (s : X.K) = 2 * algebraMap (𝓞 X.K) X.K (X.ω b) - 1`.

Apply `(algebraMap X.K ℂ).injective` to reduce the goal to its premises. Establish `h1` using `(X.map' b).1`. Establish `h2` using `(Z b).hω`. Rewrite using `[map_sub, map_mul, map_ofNat, map_one, show algebraMap X.K ℂ s = (s : ℂ) from rfl, hs, ← h2, ← h1]`. Both sides reduce to the same expression.

Rewrite using `[hrt, map_sub, map_mul, map_ofNat, map_one, two_mul, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, ← hsm, hω]`. Simplify using `[sub_smul, two_mul, add_smul]`.
-/
theorem lamRt : LamRt X := by
  intro b s a hs
  have hrt : H.rt = 2 * H.w0 - 1 := by linear_combination H.two_weight_eq_one_add_root.symm
  have hsm := lamSmul X b H.w0 a
  rw [lam_smul_w0] at hsm
  have hω : (s : X.K) = 2 * algebraMap (𝓞 X.K) X.K (X.ω b) - 1 := by
    apply (algebraMap X.K ℂ).injective
    have h1 := (X.map' b).1
    have h2 := (Z b).hω
    rw [map_sub, map_mul, map_ofNat, map_one, show algebraMap X.K ℂ s = (s : ℂ) from rfl, hs, ← h2, ← h1]
    rfl
  rw [hrt, map_sub, map_mul, map_ofNat, map_one, two_mul, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.one_apply, ← hsm, hω]
  simp [sub_smul, two_mul, add_smul]

/- English proof (translation)
Introduce `b τ a v`. Establish `bridge` using `(GlobalTheory.T.lie_model_eigenvectors_action Xo.X X.K Xo.univ.t.G (under X.y) (Fin g → X.K) (Mm X)).1`. Set `uv : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (Fin g → X.K)` to `fun j => ρm X (RingOfIntegers.basis E j) (lam X b a)`. Establish `hsum : ∀ (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)), ∑ k, X.β (tauE c τ (HT.dualInt E (e k))) • uv (e k) = HT.eigProj (ρm X) (X.β.comp (tauE c τ)) (lam X b a)`. Introduce `n e`.

Rewrite using `[Equiv.sum_comp e (fun j => X.β (tauE c τ (HT.dualInt E j)) • uv j)]`. Simplify using `[HT.eigProj, uv, LinearMap.sum_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, e, u, hu, hc⟩`. Establish `hu' : u = fun k => (Mm X).pt (uv (e k))`.

Use function extensionality and compare the values at `k`. Rewrite using `[(imageIff X b _ (u k)).1 (hu k), lamSmul]`. Rewrite `hc` using `[hu']`. Rewrite using `[(bridge n _ _ v).1 hc, hsum]`. Introduce and unpack `rfl`.

Set `e` to `(Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm`. Use `⟨_, e, fun k => (Mm X).pt (uv (e k)), fun k => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[imageIff, lamSmul]`. Rewrite using `[bridge, hsum]`.
-/
theorem cmVecIff : CMVecIff X := by
  intro b τ a v
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action Xo.X X.K Xo.univ.t.G (under X.y) (Fin g → X.K) (Mm X)).1
  let uv : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (Fin g → X.K) := fun j => ρm X (RingOfIntegers.basis E j) (lam X b a)
  have hsum : ∀ (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      ∑ k, X.β (tauE c τ (HT.dualInt E (e k))) • uv (e k) = HT.eigProj (ρm X) (X.β.comp (tauE c τ)) (lam X b a) := by
    intro n e
    rw [Equiv.sum_comp e (fun j => X.β (tauE c τ (HT.dualInt E j)) • uv j)]
    simp [HT.eigProj, uv, LinearMap.sum_apply]
  constructor
  · rintro ⟨n, e, u, hu, hc⟩
    have hu' : u = fun k => (Mm X).pt (uv (e k)) := by
      funext k
      rw [(imageIff X b _ (u k)).1 (hu k), lamSmul]
    rw [hu'] at hc
    rw [(bridge n _ _ v).1 hc, hsum]
  · rintro rfl
    let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm
    refine ⟨_, e, fun k => (Mm X).pt (uv (e k)), fun k => ?_, ?_⟩
    · rw [imageIff, lamSmul]
    · rw [bridge, hsum]

end PositivityTheory.Xgf.cm_lie_model_action

namespace PositivityTheory.Xgf

/- English proof (translation)
The claim follows from `cm_pack_lie_properties fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X => ⟨cm_lie_model_action.imageIff X, cm_lie_model_action.lamSmul X, cm_lie_model_action.lamAdd X, cm_lie_model_action.lamRt X, cm_lie_model_action.cmVecIff X⟩`.
-/
theorem cm_lie_model_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP), ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)) (lam : ∀ b, PureType.lat hP (sgnRt H b) → Fin g → X.K), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ b a u, X.IsImage b a u ↔ u = M.pt (lam b a)) ∧ (∀ b (s : 𝓞 E) a, lam b (s • a) = ρ s (lam b a)) ∧ (∀ b a a', lam b (a + a') = lam b a + lam b a') ∧ (∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρ H.rt (lam b a) = s • lam b a) ∧ ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam b a)) :=
  cm_pack_lie_properties fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X =>
    ⟨cm_lie_model_action.imageIff X, cm_lie_model_action.lamSmul X, cm_lie_model_action.lamAdd X, cm_lie_model_action.lamRt X, cm_lie_model_action.cmVecIff X⟩

end PositivityTheory.Xgf

end
