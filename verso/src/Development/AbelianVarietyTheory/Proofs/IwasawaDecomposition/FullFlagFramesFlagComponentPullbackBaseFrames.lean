import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.FlagPull

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hc0 z' A' hA' A hA`. Express the relevant statement in the definitionally equal form `C.Y.X at z'`. Establish `hA₀d : ∀ τ, (A₀ τ).det ≠ 0` using `Fr.det_ne hT.1`. Establish `hA₁d : ∀ τ, (A₁ τ).det ≠ 0` using `Fr.det_ne hT'.1`. Establish `hA'd : ∀ τ, (A' τ).det ≠ 0` using `Fr.det_ne hA'`.

Establish `hmapd : ∀ {B : Mat Dw.mult X.Fn}, (∀ τ, (B τ).det ≠ 0) → ∀ τ, (B.map φ τ).det ≠ 0` using `fun {B} hB τ => by`. Use `Mat.det_map B (φ : X.Fn →+* C.Y.Fn) τ` as an intermediate fact. Rewrite using `[show B.map φ = B.map (φ : X.Fn →+* C.Y.Fn) from rfl, this]`. Conclude with `(map_ne_zero _).2 (hB τ)`. Take `⟨φ₁, fA, hfA⟩` from `hT.2 (f z') A hA`.

Take `⟨φ', f', hf'⟩` from `hT'.2 z' A' hA'`. Set `aY : C.Y.X.presheaf.stalk z' →+* C.Y.Fn` to `algebraMap (C.Y.X.presheaf.stalk z') C.Y.X.functionField`. Set `aB : X.X.presheaf.stalk (f z') →+* X.Fn` to `algebraMap (X.X.presheaf.stalk (f z')) X.X.functionField`. Set `σ : X.X.presheaf.stalk (f z') →+* C.Y.X.presheaf.stalk z'` to `(f.stalkMap z').hom`. Establish `hinj : Function.Injective aY` using `IsFractionRing.injective (C.Y.X.presheaf.stalk z') C.Y.X.functionField`.

Establish `hcomp : (φ : X.Fn →+* C.Y.Fn).comp aB = aY.comp σ` using `RingHom.ext fun a => map_algebraMap_stalk hφ z' a`. Establish `hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X)` using `RingHom.ext fun a => (φ.commutes _).symm`. Establish `hσ : spMap σ ≫ stalkPt X (f z') = stalkPt C.Y z' ≫ f` using `Scheme.SpecMap_stalkMap_fromSpecStalk f`. Establish `hx' : stalkPt C.Y z' ≫ C.π ≫ genι Z = spMap σ ≫ stalkPt X (f z') ≫ j ≫ genι Z`. Rewrite using `[← hπ, Category.assoc, reassoc_of% hσ]`.

Establish `hφ' : φ' = σ.comp φ₁`. Establish `h1 : aY.comp φ' = aY.comp (σ.comp φ₁)`. Rewrite using `[← hf'.2.1, ← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, ← hfA.2.1, hc]`. Conclude with `RingHom.ext fun a => hinj (RingHom.congr_fun h1 a)`. Establish `hstA : fA.Stable` using `GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance`.

Take `⟨⟨G, hG, -⟩, hu⟩` from `(GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA _ φ' (stalkPt C.Y z' ≫ C.π ≫ genι Z) σ inferInstance hstA hx' hφ').1 f'`. Establish `hGd` using `hu G hG`. Establish `h1` using `GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ C.f0 σ aY G (A₁ * A'⁻¹) inferInstance hG hf'`. Establish `h2` using `GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ C.f0 aB (φ : X.Fn →+* C.Y.Fn) _ _ inferInstance hfA hc0`. Rewrite `h2` using `[hcomp]`.

Establish `hU` using `((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA C.Y.Fn (constF e C.Y) (genericPt C.Y ≫ C.π ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 C.f0).1.unique h1 h2`. Establish `e : (A₀ * A⁻¹).map (φ : X.Fn →+* C.Y.Fn) = A₀.map φ * (A.map φ)⁻¹`. Rewrite using `[Mat.map_mul, Mat.map_inv]`. Both sides reduce to the same expression. Establish `key : A₁ * (A'⁻¹ * G.map aY) = A₁ * (A.map φ)⁻¹`.

Rewrite using `[← mul_assoc, hU, e, mul_assoc A₁, ← mul_assoc (A₀.map φ)⁻¹, Mat.inv_mul (hmapd hA₀d), one_mul]`. Establish `hGm : G.map aY = A' * (A.map φ)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul, ← mul_assoc, Mat.mul_inv hA'd, one_mul]`. Use `_ = A' * (A.map φ)⁻¹ := by`.

Rewrite using `[key, ← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul]`. Conclude with `(GlobalTheory.ShFam.TieBase.par_zero_iff aY hinj _ (fun x => mem_O_ratOf) _).2 ⟨G, hGd, hGm.symm⟩`.
-/
theorem frames_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z) (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → ∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hc0 z' A' hA' A hA
  change C.Y.X at z'
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hT'.1
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have hmapd : ∀ {B : Mat Dw.mult X.Fn}, (∀ τ, (B τ).det ≠ 0) →
      ∀ τ, (B.map φ τ).det ≠ 0 := fun {B} hB τ => by
    have := Mat.det_map B (φ : X.Fn →+* C.Y.Fn) τ
    rw [show B.map φ = B.map (φ : X.Fn →+* C.Y.Fn) from rfl, this]; exact (map_ne_zero _).2 (hB τ)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f z') A hA
  obtain ⟨φ', f', hf'⟩ := hT'.2 z' A' hA'
  let aY : C.Y.X.presheaf.stalk z' →+* C.Y.Fn := algebraMap (C.Y.X.presheaf.stalk z') C.Y.X.functionField
  let aB : X.X.presheaf.stalk (f z') →+* X.Fn := algebraMap (X.X.presheaf.stalk (f z')) X.X.functionField
  let σ : X.X.presheaf.stalk (f z') →+* C.Y.X.presheaf.stalk z' := (f.stalkMap z').hom
  have hinj : Function.Injective aY := IsFractionRing.injective (C.Y.X.presheaf.stalk z') C.Y.X.functionField
  have hcomp : (φ : X.Fn →+* C.Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hφ z' a
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hσ : spMap σ ≫ stalkPt X (f z') = stalkPt C.Y z' ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt C.Y z' ≫ C.π ≫ genι Z = spMap σ ≫ stalkPt X (f z') ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, reassoc_of% hσ]
  have hφ' : φ' = σ.comp φ₁ := by
    have h1 : aY.comp φ' = aY.comp (σ.comp φ₁) := by
      rw [← hf'.2.1, ← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, ← hfA.2.1, hc]
    exact RingHom.ext fun a => hinj (RingHom.congr_fun h1 a)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  obtain ⟨⟨G, hG, -⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA _ φ'
    (stalkPt C.Y z' ≫ C.π ≫ genι Z) σ inferInstance hstA hx' hφ').1 f'
  have hGd := hu G hG
  have h1 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ C.f0 σ aY G (A₁ * A'⁻¹) inferInstance hG hf'
  have h2 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ C.f0 aB (φ : X.Fn →+* C.Y.Fn) _ _
    inferInstance hfA hc0
  rw [hcomp] at h2
  have hU := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 C.f0).1.unique h1 h2
  have e : (A₀ * A⁻¹).map (φ : X.Fn →+* C.Y.Fn) = A₀.map φ * (A.map φ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv]; rfl
  have key : A₁ * (A'⁻¹ * G.map aY) = A₁ * (A.map φ)⁻¹ := by
    rw [← mul_assoc, hU, e, mul_assoc A₁, ← mul_assoc (A₀.map φ)⁻¹, Mat.inv_mul (hmapd hA₀d), one_mul]
  have hGm : G.map aY = A' * (A.map φ)⁻¹ := by
    calc G.map aY = A' * (A₁⁻¹ * (A₁ * (A'⁻¹ * G.map aY))) := by
          rw [← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul, ← mul_assoc, Mat.mul_inv hA'd, one_mul]
      _ = A' * (A.map φ)⁻¹ := by
          rw [key, ← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul]
  exact (GlobalTheory.ShFam.TieBase.par_zero_iff aY hinj _ (fun x => mem_O_ratOf) _).2 ⟨G, hGd, hGm.symm⟩

end GlobalTheory.LieBase.FlagPull
