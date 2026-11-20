import Development.WeilBound.CoreStatements.ProjectiveValuations.IsIsoOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLeadStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrameStatement

noncomputable section

namespace DifferentiableLines.FlagIso

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str pm)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
open GlobalTheory GlobalTheory.CompHS Matrix
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Establish `hd : IsUnit B.det`. Rewrite using `[Matrix.det_of_isUpperTriangular hB]`. Conclude with `IsUnit.prod_univ_iff.2 hu`. Set `` to `Matrix.invertibleOfIsUnitDet B hd`. Use `le_antisymm (initSpan_le_of_tri hB h i) (initSpan_le_of_tri (Matrix.blockTriangular_inv_of_blockTriangular hB) (fun i => ?_) i)` and prove the remaining obligations.

Simplify using `only [h, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`. Establish `e : ∀ k, ∑ j, B⁻¹ j i * B k j = (1 : Matrix (Fin m) (Fin m) R) k i` using `fun k => by`. Rewrite using `[← Matrix.mul_nonsing_inv B hd, Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _`. Simplify using `[e, Matrix.one_apply]`.
-/
theorem initSpan_eq_of_tri {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} {v v' : Fin m → N}
    {B : Matrix (Fin m) (Fin m) R} (hB : B.BlockTriangular id) (hu : ∀ i, IsUnit (B i i))
    (h : ∀ i, v' i = ∑ j, B j i • v j) (i : ℕ) : initSpan R v' i = initSpan R v i := by
  have hd : IsUnit B.det := by
    rw [Matrix.det_of_isUpperTriangular hB]
    exact IsUnit.prod_univ_iff.2 hu
  let := Matrix.invertibleOfIsUnitDet B hd
  refine le_antisymm (initSpan_le_of_tri hB h i)
    (initSpan_le_of_tri (Matrix.blockTriangular_inv_of_blockTriangular hB) (fun i => ?_) i)
  simp only [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have e : ∀ k, ∑ j, B⁻¹ j i * B k j = (1 : Matrix (Fin m) (Fin m) R) k i := fun k => by
    rw [← Matrix.mul_nonsing_inv B hd, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
  simp [e, Matrix.one_apply]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {S S' : Type} [CommRing S] [CommRing S']

/- English proof (translation)
Set `y` to `IsOpenImmersion.lift Y.j x (by`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `h (Set.mem_univ q))`. Conclude with `⟨((ev (y ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra, y, (spMap_ev_top _).symm, (IsOpenImmersion.lift_fac _ _ _).symm⟩`.
-/
theorem exists_y (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ LogKS.interior Y) :
    ∃ (_ : Algebra c.F S) (y : Sp S ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) ∧ x = y ≫ Y.j := by
  let y := IsOpenImmersion.lift Y.j x (by
    rintro _ ⟨q, rfl⟩
    exact h (Set.mem_univ q))
  exact ⟨((ev (y ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra, y, (spMap_ev_top _).symm,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩

/- English proof (translation)
Establish `e : spMap φ ≫ x = x₁` using `by rw [← h₁, Category.assoc, hx]`. Rewrite using `[F.step_eq k _ (le_preimage_comp _ hz)]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Rewrite using `[← F.tanPull_vecAt k φ z hz _ hx h₁ e]`.

Use `F'.tanPull_mem_step φ z' hx' rfl h₁' e σ i (h ?_)` and prove the remaining obligations. Rewrite using `[F.step_eq k z hz]`. Conclude with `Submodule.subset_span ⟨j, hj, rfl⟩`.
-/
theorem step_le_bc {Z Z' : Scheme.{0}} {π : Z ⟶ Y.X} {π' : Z' ⟶ Y.X} (F : Frames Y π) (F' : Frames Y π')
    {z : Sp S ⟶ Z} {z' : Sp S ⟶ Z'} {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π' = x) {k : F.J}
    (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (σ : E →+* ℂ) (i : ℕ) (h : F.step z hx σ i ≤ F'.step z' hx' σ i) (φ : S →+* S')
    {x₁ : Sp S' ⟶ Y.X} (h₁ : (spMap φ ≫ z) ≫ π = x₁) (h₁' : (spMap φ ≫ z') ≫ π' = x₁) :
    F.step (spMap φ ≫ z) h₁ σ i ≤ F'.step (spMap φ ≫ z') h₁' σ i := by
  have e : spMap φ ≫ x = x₁ := by rw [← h₁, Category.assoc, hx]
  rw [F.step_eq k _ (le_preimage_comp _ hz)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rw [← F.tanPull_vecAt k φ z hz _ hx h₁ e]
  refine F'.tanPull_mem_step φ z' hx' rfl h₁' e σ i (h ?_)
  rw [F.step_eq k z hz]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

variable (p : Proj (RingHom.id c.F))

/- English proof (translation)
Use `Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_dense (flagOpen X) (dense_flagOpen X) _ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resG X.YY inf_le_left _ = 0`. Use `ext_ev fun S _ z hz => ?_` and prove the remaining obligations. Establish `hk : ⊤ ≤ z ⁻¹ᵁ X.F.U k` using `le_preimage_mono inf_le_left hz`. Take `⟨_, y, hy, hx⟩` from `exists_y (z ≫ X.π) (le_preimage_mono inf_le_right hz : ⊤ ≤ z ⁻¹ᵁ flagOpen X)`.

Establish `hM` using `X.F.inM hk hx`. Establish `h1 : X.F.vecAt k z hk hx σ j ∈ eigLie c (y ≫ Y.j) σ`. Rewrite using `[← X.top S y hy z hx k hk σ]`. Conclude with `Submodule.subset_span ⟨j, j.2, rfl⟩`. Establish `h2` using `congrFun (((LowRank.pm_gen p (X.F.M k).toMChart σ hy hM).1 _).1 ((vec_mem_eigLie _ _ hM σ _).1 h1)) i`.

Rewrite using `[ev_res z _ hz hk, map_zero, map_sub, sub_eq_zero, Matrix.mul_apply, map_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun r _ => ?_) h2` and prove the remaining obligations. Rewrite using `[map_mul, Matrix.map_apply, ev_appLE z X.π _ hk (hx ▸ hM), ev_congr hx _ _ hM]`. Both sides reduce to the same expression.
-/
theorem pm_mul_u (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) :
    (pm p (X.F.M k).toMChart σ).map (X.π.appLE (X.F.M k).U (X.F.U k) (X.F.le k)).hom * X.F.u k σ = X.F.u k σ := by
  refine Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_dense (flagOpen X) (dense_flagOpen X) _ ?_)
  change resG X.YY inf_le_left _ = 0
  refine ext_ev fun S _ z hz => ?_
  have hk : ⊤ ≤ z ⁻¹ᵁ X.F.U k := le_preimage_mono inf_le_left hz
  obtain ⟨_, y, hy, hx⟩ := exists_y (z ≫ X.π) (le_preimage_mono inf_le_right hz : ⊤ ≤ z ⁻¹ᵁ flagOpen X)
  have hM := X.F.inM hk hx
  have h1 : X.F.vecAt k z hk hx σ j ∈ eigLie c (y ≫ Y.j) σ := by
    rw [← X.top S y hy z hx k hk σ]
    exact Submodule.subset_span ⟨j, j.2, rfl⟩
  have h2 := congrFun (((LowRank.pm_gen p (X.F.M k).toMChart σ hy hM).1 _).1 ((vec_mem_eigLie _ _ hM σ _).1 h1)) i
  rw [ev_res z _ hz hk, map_zero, map_sub, sub_eq_zero, Matrix.mul_apply, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) h2
  rw [map_mul, Matrix.map_apply, ev_appLE z X.π _ hk (hx ▸ hM), ev_congr hx _ _ hM]
  rfl

/- English proof (translation)
Substitute `hx` using the available equality. Apply `(vec M _ hM).injective` to reduce the goal to its premises. Rewrite using `[LowRank.vec_pm, h, Frames.vecAt, ← LowRank.vec_pm]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Establish `e` using `congrArg (ev z _ hz) (congrFun (congrFun (pm_mul_u p X k σ) i) j)`. Rewrite `e` using `[Matrix.mul_apply, map_sum]`. Rewrite using `[Matrix.mulVec, dotProduct]`. Use `Eq.trans (Finset.sum_congr rfl fun r _ => ?_) e` and prove the remaining obligations. Rewrite using `[map_mul, Matrix.map_apply, Matrix.map_apply, ev_appLE z X.π _ hz (X.F.inM hz rfl)]`.

Both sides reduce to the same expression.
-/
theorem pm_fix (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (z : Sp S ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    {x : Sp S ⟶ Y.X} (hx : z ≫ X.π = x) (M : MChart Y) (hM : ⊤ ≤ x ⁻¹ᵁ M.U) (j : Fin (Dw.mult σ)) (cv : Fin M.n → S)
    (h : vec M x hM cv = X.F.vecAt k z hz hx σ j) : ((pm p M σ).map (ev x M.U hM)) *ᵥ cv = cv := by
  subst hx
  apply (vec M _ hM).injective
  rw [LowRank.vec_pm, h, Frames.vecAt, ← LowRank.vec_pm]
  congr 1
  funext i
  have e := congrArg (ev z _ hz) (congrFun (congrFun (pm_mul_u p X k σ) i) j)
  rw [Matrix.mul_apply, map_sum] at e
  rw [Matrix.mulVec, dotProduct]
  refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) e
  rw [map_mul, Matrix.map_apply, Matrix.map_apply, ev_appLE z X.π _ hz (X.F.inM hz rfl)]
  rfl

variable {p}

/- English proof (translation)
Establish `ex : ∀ j, ∃ a, ((e.u σ).map (ev x _ h)) *ᵥ a = (vec e.M.toMChart x hM).symm (X.F.vecAt k z hz hx σ j)` using `fun j => (e.fix_iff σ x h hM _).1 (pm_fix p X k σ z hz hx e.M.toMChart hM j _ (LinearEquiv.apply_symm_apply _ _))`. Use `choose a ha using ex`. Establish `hv : ∀ j, X.F.vecAt k z hz hx σ j = vec e.M.toMChart x hM (((e.u σ).map (ev x _ h)) *ᵥ a j)` using `fun j => by`. Rewrite using `[ha, LinearEquiv.apply_symm_apply]`. Use `⟨Matrix.of fun r j => a j r, ?_, hv⟩` and prove the remaining obligations.

Take `⟨w, hw⟩` from `X.F.uAt_split k z hz σ`. Set `L : (Fin (Dw.mult σ) → S) →ₗ[S] (Fin (Dw.mult σ) → S)` to `w.mulVecLin ∘ₗ (vec (X.F.M k).toMChart x (X.F.inM hz hx)).symm.toLinearMap ∘ₗ (vec e.M.toMChart x hM).toLinearMap ∘ₗ ((e.u σ).map (ev x _ h)).mulVecLin`. Establish `h1 : LinearMap.toMatrix' L * (Matrix.of fun r j => a j r) = 1`. Use extensionality with `i j`. Establish `e1 : L (a j) = fun i => (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) i j`.

Express the relevant statement in the definitionally equal form `w *ᵥ (vec (X.F.M k).toMChart x (X.F.inM hz hx)).symm (vec e.M.toMChart x hM (((e.u σ).map (ev x _ h)) *ᵥ a j)) = _`. Rewrite using `[← hv, Frames.vecAt, LinearEquiv.symm_apply_apply, ← hw]`. Both sides reduce to the same expression. Establish `e2` using `congrFun ((LinearMap.toMatrix'_mulVec L (a j)).trans e1) i`. Conclude with `e2`.

Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_one, _root_.mul_comm]`. Conclude with `IsUnit.of_mul_eq_one _ h2`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (z : Sp S ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    {x : Sp S ⟶ Y.X} (hx : z ≫ X.π = x) (e : ECh Y p) (h : ⊤ ≤ x ⁻¹ᵁ e.V) (hM : ⊤ ≤ x ⁻¹ᵁ e.M.U) :
    ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, IsUnit T.det ∧ ∀ j, X.F.vecAt k z hz hx σ j =
      vec e.M.toMChart x hM (fun r => (((e.u σ).map (ev x _ h)) * T) r j) := by
  have ex : ∀ j, ∃ a, ((e.u σ).map (ev x _ h)) *ᵥ a = (vec e.M.toMChart x hM).symm (X.F.vecAt k z hz hx σ j) :=
    fun j => (e.fix_iff σ x h hM _).1 (pm_fix p X k σ z hz hx e.M.toMChart hM j _ (LinearEquiv.apply_symm_apply _ _))
  choose a ha using ex
  have hv : ∀ j, X.F.vecAt k z hz hx σ j = vec e.M.toMChart x hM (((e.u σ).map (ev x _ h)) *ᵥ a j) := fun j => by
    rw [ha, LinearEquiv.apply_symm_apply]
  refine ⟨Matrix.of fun r j => a j r, ?_, hv⟩
  obtain ⟨w, hw⟩ := X.F.uAt_split k z hz σ
  let L : (Fin (Dw.mult σ) → S) →ₗ[S] (Fin (Dw.mult σ) → S) :=
    w.mulVecLin ∘ₗ (vec (X.F.M k).toMChart x (X.F.inM hz hx)).symm.toLinearMap ∘ₗ
      (vec e.M.toMChart x hM).toLinearMap ∘ₗ ((e.u σ).map (ev x _ h)).mulVecLin
  have h1 : LinearMap.toMatrix' L * (Matrix.of fun r j => a j r) = 1 := by
    ext i j
    have e1 : L (a j) = fun i => (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) i j := by
      change w *ᵥ (vec (X.F.M k).toMChart x (X.F.inM hz hx)).symm
        (vec e.M.toMChart x hM (((e.u σ).map (ev x _ h)) *ᵥ a j)) = _
      rw [← hv, Frames.vecAt, LinearEquiv.symm_apply_apply, ← hw]
      rfl
    have e2 := congrFun ((LinearMap.toMatrix'_mulVec L (a j)).trans e1) i
    exact e2
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, _root_.mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

/- English proof (translation)
Establish `e₁ : spMap φ ≫ z ≫ X.π = (spMap φ ≫ z) ≫ X.π` using `(Category.assoc _ _ _).symm`. Rewrite using `[← X.F.tanPull_vecAt k φ z hz hz₁ rfl rfl e₁, hT, tanPull_vec _ φ e₁ hM hM₁]`. Use `congr 1`. Use function extensionality and compare the values at `r`. Establish `hev : (e.u σ).map (ev ((spMap φ ≫ z) ≫ X.π) _ h₁) = ((e.u σ).map (ev _ _ h)).map φ`.

Use extensionality with `r s`. Simplify using `only [Matrix.map_apply]`. Rewrite using `[ev_congr e₁.symm _ h₁ (le_preimage_comp _ h), ev_spMap φ _ _ h]`. Both sides reduce to the same expression. Rewrite using `[hev, ← Matrix.map_mul]`.

Both sides reduce to the same expression.
-/
theorem T_bc (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (z : Sp S ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    (e : ECh Y p) (h : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ e.V) (hM : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ e.M.U)
    (T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) (hT : ∀ j, X.F.vecAt k z hz rfl σ j =
      vec e.M.toMChart _ hM (fun r => (((e.u σ).map (ev _ _ h)) * T) r j)) (φ : S →+* S')
    (hz₁ : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ X.F.U k) (h₁ : ⊤ ≤ ((spMap φ ≫ z) ≫ X.π) ⁻¹ᵁ e.V)
    (hM₁ : ⊤ ≤ ((spMap φ ≫ z) ≫ X.π) ⁻¹ᵁ e.M.U) (j : Fin (Dw.mult σ)) :
    X.F.vecAt k (spMap φ ≫ z) hz₁ rfl σ j =
      vec e.M.toMChart _ hM₁ (fun r => (((e.u σ).map (ev _ _ h₁)) * T.map φ) r j) := by
  have e₁ : spMap φ ≫ z ≫ X.π = (spMap φ ≫ z) ≫ X.π := (Category.assoc _ _ _).symm
  rw [← X.F.tanPull_vecAt k φ z hz hz₁ rfl rfl e₁, hT, tanPull_vec _ φ e₁ hM hM₁]
  congr 1
  funext r
  have hev : (e.u σ).map (ev ((spMap φ ≫ z) ≫ X.π) _ h₁) = ((e.u σ).map (ev _ _ h)).map φ := by
    ext r s
    simp only [Matrix.map_apply]
    rw [ev_congr e₁.symm _ h₁ (le_preimage_comp _ h), ev_spMap φ _ _ h]
    rfl
  rw [hev, ← Matrix.map_mul]
  rfl

variable {A : Atlas Y p} {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)
  (ht : FlagCellFrameChangeTriangular hZ)

/- English proof (translation)
Use `choose L U hL0 hL1 hU hUu hLU using fun σ => GlobalTheory.T.exists_lu_of_isUnit_leading_minors S (Dw.mult σ) ((T σ).submatrix (w σ) id) (hminor σ)`. Set `ψ₀ : Γ(Y.X, (A.V b).1) →+* S` to `ev x _ h`. Set `xc : CellVar Dw.mult → S` to `fun v => L v.1 v.2.1.1 v.2.1.2`. Take `⟨hzπ, hz, huAt⟩` from `GlobalTheory.T.flagCellPoint_image_and_frame E H Dw l Xo c Y p A Z π g κ hZ ht b w _ ψ₀ xc _ rfl`. Establish `hx : (spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w) ≫ π = x` using `hzπ.trans (spMap_ev _ (A.V b).2 h)`.

Use `⟨_, hx, hz, fun σ n => ?_⟩` and prove the remaining obligations. Rewrite using `[(cellFrames hZ ht).step_eq _ _ hz]`. Use `initSpan_eq_of_tri (hU σ) (hUu σ) (fun i => ?_) n` and prove the remaining obligations. Establish `hcell : Matrix.of (cell xc σ) = L σ`. Use extensionality with `i j`.

Simplify using `only [Matrix.of_apply, cell, xc]`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Substitute `h2` using the available equality. Conclude with `(hL1 σ i).symm`.

Conclude with `(hL0 σ i j (lt_of_le_of_ne (not_lt.1 h1) h2)).symm`. Establish `key : ((A.k b).u σ).map ψ₀ * T σ = ((((A.k b).u σ).map ψ₀).submatrix id (w σ) * L σ) * U σ`. Rewrite using `[Matrix.mul_assoc, ← hLU σ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]`. Simplify using `only [Frames.vecAt, huAt σ, hcell, ← map_smul, ← map_sum]`. Use `congr 1`.

Use function extensionality and compare the values at `r`. Express the relevant statement in the definitionally equal form `(((A.k b).u σ).map ψ₀ * T σ) r i = _`. Rewrite using `[key, Matrix.mul_apply]`. Use `erw [Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Conclude with `_root_.mul_comm _ _`.
-/
theorem exists_cell_pt (b : A.B) {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ (A.k b).V) (hM : ⊤ ≤ x ⁻¹ᵁ (A.k b).M.U)
    (T : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) (w : Pm Dw.mult)
    (hminor : ∀ σ (k : ℕ) (hk : k ≤ Dw.mult σ),
      IsUnit (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ (z' : Sp S ⟶ Z) (hx' : z' ≫ π = x) (_ : ⊤ ≤ z' ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult)),
      ∀ σ i, initSpan S (fun j => vec (A.k b).M.toMChart x hM
        (fun r => ((((A.k b).u σ).map (ev x _ h)) * T σ) r j)) i = (cellFrames hZ ht).step z' hx' σ i := by
  choose L U hL0 hL1 hU hUu hLU using fun σ => GlobalTheory.T.exists_lu_of_isUnit_leading_minors S (Dw.mult σ) ((T σ).submatrix (w σ) id) (hminor σ)
  let ψ₀ : Γ(Y.X, (A.V b).1) →+* S := ev x _ h
  let xc : CellVar Dw.mult → S := fun v => L v.1 v.2.1.1 v.2.1.2
  obtain ⟨hzπ, hz, huAt⟩ := GlobalTheory.T.flagCellPoint_image_and_frame E H Dw l Xo c Y p A Z π g κ hZ ht b w _ ψ₀ xc _ rfl
  have hx : (spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w) ≫ π = x := hzπ.trans (spMap_ev _ (A.V b).2 h)
  refine ⟨_, hx, hz, fun σ n => ?_⟩
  rw [(cellFrames hZ ht).step_eq _ _ hz]
  refine initSpan_eq_of_tri (hU σ) (hUu σ) (fun i => ?_) n
  have hcell : Matrix.of (cell xc σ) = L σ := by
    ext i j
    simp only [Matrix.of_apply, cell, xc]
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hL1 σ i).symm
    · exact (hL0 σ i j (lt_of_le_of_ne (not_lt.1 h1) h2)).symm
  have key : ((A.k b).u σ).map ψ₀ * T σ = ((((A.k b).u σ).map ψ₀).submatrix id (w σ) * L σ) * U σ := by
    rw [Matrix.mul_assoc, ← hLU σ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  simp only [Frames.vecAt, huAt σ, hcell, ← map_smul, ← map_sum]
  congr 1
  funext r
  change (((A.k b).u σ).map ψ₀ * T σ) r i = _
  rw [key, Matrix.mul_apply]
  erw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact _root_.mul_comm _ _

def Rel (X : FlagCover Y) (z : Sp S ⟶ X.YY) (z' : Sp S ⟶ Z) : Prop :=
  ∃ hx' : z' ≫ π = z ≫ X.π, ∀ σ i, (cellFrames hZ ht).step z' hx' σ i = X.F.step z rfl σ i

/- English proof (translation)
Establish `hy : y ∈ ⨆ k, X.F.U k` using `by rw [X.F.cover]; trivial`. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 hy`. Take `⟨b, hb⟩` from `A.cov (X.π y)`. Take `⟨_, ⟨(W : X.YY.Opens), hW, rfl⟩, hyW, hle⟩` from `X.YY.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ ((X.F.U k ⊓ X.π ⁻¹ᵁ (A.k b).V : X.YY.Opens) : Set X.YY) from ⟨hk, hb⟩) (Opens.isOpen _)`. Establish `hle' : W ≤ X.F.U k ⊓ X.π ⁻¹ᵁ (A.k b).V` using `hle`.

Set `R : Type` to `Γ(X.YY, W)`. Set `z₀ : Sp R ⟶ X.YY` to `tau hW`. Establish `: IsOpenImmersion z₀` using `IsAffineOpen.isOpenImmersion_fromSpec hW`. Establish `hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ X.F.U k` using `tau_le hW (hle'.trans inf_le_left)`. Establish `h₀ : ⊤ ≤ (z₀ ≫ X.π) ⁻¹ᵁ (A.k b).V` using `tau_le hW (hle'.trans inf_le_right)`.

Establish `hM₀ : ⊤ ≤ (z₀ ≫ X.π) ⁻¹ᵁ (A.k b).M.U` using `le_preimage_mono (A.k b).le h₀`. Take `⟨q, hq⟩ : y ∈ Set.range z₀` from `hW.range_fromSpec.ge hyW`. Set `q' : PrimeSpectrum R` to `q`. Use `choose T hTu hT using fun σ => exists_strictHenselian_absolutely_closed_local_ring X k σ z₀ hz₀ rfl (A.k b) h₀ hM₀`. Use `choose w hw using fun σ => GlobalTheory.T.exists_perm_leadingMinors_not_mem R _ (T σ) q'.asIdeal q'.2 fun h => q'.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hTu σ))`.

Set `m : (Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1)) → R` to `fun i => (((T i.1).submatrix (w i.1) id).submatrix (Fin.castLE (Nat.lt_succ_iff.1 i.2.2)) (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))).det`. Set `f : R` to `∏ i, m i`. Establish `hf : f ∉ q'.asIdeal` using `fun h => by`. Use `q'.2` as an intermediate fact. Take `⟨i, -, hi⟩` from `Ideal.IsPrime.prod_mem_iff.1 h`.

Conclude with `hw i.1 _ _ hi`. Set `φ : R →+* Localization.Away f` to `algebraMap _ _`. Establish `hφ : ∀ i, IsUnit (φ (m i))` using `fun i => isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem m (Finset.mem_univ i))) (IsLocalization.Away.algebraMap_isUnit f)`. Establish `: IsOpenImmersion (spMap φ)` using `IsOpenImmersion.of_isLocalization (R := CommRingCat.of R) (S := CommRingCat.of (Localization.Away f)) f`. Establish `hz₁ : ⊤ ≤ (spMap φ ≫ z₀) ⁻¹ᵁ X.F.U k` using `le_preimage_comp _ hz₀`.

Establish `e₁ : spMap φ ≫ z₀ ≫ X.π = (spMap φ ≫ z₀) ≫ X.π` using `(Category.assoc _ _ _).symm`. Establish `h₁ : ⊤ ≤ ((spMap φ ≫ z₀) ≫ X.π) ⁻¹ᵁ (A.k b).V` using `e₁ ▸ le_preimage_comp _ h₀`. Establish `hM₁ : ⊤ ≤ ((spMap φ ≫ z₀) ≫ X.π) ⁻¹ᵁ (A.k b).M.U` using `le_preimage_mono (A.k b).le h₁`. Take `⟨z', hx', hz', hs⟩` from `exists_cell_pt hZ ht b h₁ hM₁ (fun σ => (T σ).map φ) w fun σ n hn => by`. Establish `h` using `hφ ⟨σ, ⟨n, Nat.lt_succ_of_le hn⟩⟩`.

Establish `e : (((T σ).map φ).submatrix (w σ) id).submatrix (Fin.castLE hn) (Fin.castLE hn) = φ.mapMatrix (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hn) (Fin.castLE hn))` using `rfl`. Rewrite using `[e, ← RingHom.map_det]`. Conclude with `h`. Establish `hs' : ∀ σ i, (cellFrames hZ ht).step z' hx' σ i = X.F.step (spMap φ ≫ z₀) rfl σ i` using `fun σ i => (hs σ i).symm.trans ((congrArg (fun v => initSpan _ v i) (funext (T_bc X k σ z₀ hz₀ (A.k b) h₀ hM₀ (T σ) (hT σ) φ hz₁ h₁ hM₁))).symm.trans (X.F.step_eq k _ hz₁ rfl σ i).symm)`. Use `⟨_, spMap φ ≫ z₀, inferInstance, z', ?_, fun S _ _ t => ?_⟩` and prove the remaining obligations.

Take `⟨q₁, hq₁⟩` from `(PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).ge (show q' ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) from hf)`. Establish `h3 : spMap φ (show Sp (Localization.Away f) from q₁) = q` using `hq₁`. Conclude with `⟨q₁, (Scheme.Hom.comp_apply (spMap φ) z₀ _).trans ((congrArg z₀ h3).trans hq)⟩`. Take `⟨ψ, rfl⟩ : ∃ ψ : Localization.Away f →+* S, spMap ψ = t` from `⟨_, spMap_ev_top t⟩`. Establish `hx₂ : (spMap ψ ≫ z') ≫ π = (spMap ψ ≫ spMap φ ≫ z₀) ≫ X.π`.

Rewrite using `[Category.assoc, hx', ← Category.assoc]`. Conclude with `⟨hx₂, fun σ i => le_antisymm (step_le_bc _ _ hx' rfl hz' σ i (hs' σ i).le ψ hx₂ rfl) (step_le_bc _ _ rfl hx' hz₁ σ i (hs' σ i).ge ψ rfl hx₂)⟩`.
-/
theorem exists_local (X : FlagCover Y) (y : X.YY) :
    ∃ (U : Scheme.{0}) (j : U ⟶ X.YY) (_ : IsOpenImmersion j) (a : U ⟶ Z), y ∈ Set.range j ∧
      ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ U), Rel hZ ht X (t ≫ j) (t ≫ a) := by
  classical
  have hy : y ∈ ⨆ k, X.F.U k := by rw [X.F.cover]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hy
  obtain ⟨b, hb⟩ := A.cov (X.π y)
  obtain ⟨_, ⟨(W : X.YY.Opens), hW, rfl⟩, hyW, hle⟩ := X.YY.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((X.F.U k ⊓ X.π ⁻¹ᵁ (A.k b).V : X.YY.Opens) : Set X.YY) from ⟨hk, hb⟩) (Opens.isOpen _)
  have hle' : W ≤ X.F.U k ⊓ X.π ⁻¹ᵁ (A.k b).V := hle
  let R : Type := Γ(X.YY, W)
  let z₀ : Sp R ⟶ X.YY := tau hW
  have : IsOpenImmersion z₀ := IsAffineOpen.isOpenImmersion_fromSpec hW
  have hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ X.F.U k := tau_le hW (hle'.trans inf_le_left)
  have h₀ : ⊤ ≤ (z₀ ≫ X.π) ⁻¹ᵁ (A.k b).V := tau_le hW (hle'.trans inf_le_right)
  have hM₀ : ⊤ ≤ (z₀ ≫ X.π) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₀
  obtain ⟨q, hq⟩ : y ∈ Set.range z₀ := hW.range_fromSpec.ge hyW
  let q' : PrimeSpectrum R := q
  choose T hTu hT using fun σ => exists_strictHenselian_absolutely_closed_local_ring X k σ z₀ hz₀ rfl (A.k b) h₀ hM₀
  choose w hw using fun σ => GlobalTheory.T.exists_perm_leadingMinors_not_mem R _ (T σ) q'.asIdeal q'.2
    fun h => q'.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hTu σ))
  let m : (Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1)) → R := fun i =>
    (((T i.1).submatrix (w i.1) id).submatrix (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))
      (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))).det
  let f : R := ∏ i, m i
  have hf : f ∉ q'.asIdeal := fun h => by
    have := q'.2
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hw i.1 _ _ hi
  let φ : R →+* Localization.Away f := algebraMap _ _
  have hφ : ∀ i, IsUnit (φ (m i)) := fun i =>
    isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem m (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit f)
  have : IsOpenImmersion (spMap φ) := IsOpenImmersion.of_isLocalization (R := CommRingCat.of R)
    (S := CommRingCat.of (Localization.Away f)) f
  have hz₁ : ⊤ ≤ (spMap φ ≫ z₀) ⁻¹ᵁ X.F.U k := le_preimage_comp _ hz₀
  have e₁ : spMap φ ≫ z₀ ≫ X.π = (spMap φ ≫ z₀) ≫ X.π := (Category.assoc _ _ _).symm
  have h₁ : ⊤ ≤ ((spMap φ ≫ z₀) ≫ X.π) ⁻¹ᵁ (A.k b).V := e₁ ▸ le_preimage_comp _ h₀
  have hM₁ : ⊤ ≤ ((spMap φ ≫ z₀) ≫ X.π) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₁
  obtain ⟨z', hx', hz', hs⟩ := exists_cell_pt hZ ht b h₁ hM₁ (fun σ => (T σ).map φ) w fun σ n hn => by
    have h := hφ ⟨σ, ⟨n, Nat.lt_succ_of_le hn⟩⟩
    have e : (((T σ).map φ).submatrix (w σ) id).submatrix (Fin.castLE hn) (Fin.castLE hn) =
        φ.mapMatrix (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hn) (Fin.castLE hn)) := rfl
    rw [e, ← RingHom.map_det]
    exact h
  have hs' : ∀ σ i, (cellFrames hZ ht).step z' hx' σ i = X.F.step (spMap φ ≫ z₀) rfl σ i := fun σ i =>
    (hs σ i).symm.trans ((congrArg (fun v => initSpan _ v i)
      (funext (T_bc X k σ z₀ hz₀ (A.k b) h₀ hM₀ (T σ) (hT σ) φ hz₁ h₁ hM₁))).symm.trans
        (X.F.step_eq k _ hz₁ rfl σ i).symm)
  refine ⟨_, spMap φ ≫ z₀, inferInstance, z', ?_, fun S _ _ t => ?_⟩
  · obtain ⟨q₁, hq₁⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).ge
      (show q' ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) from hf)
    have h3 : spMap φ (show Sp (Localization.Away f) from q₁) = q := hq₁
    exact ⟨q₁, (Scheme.Hom.comp_apply (spMap φ) z₀ _).trans ((congrArg z₀ h3).trans hq)⟩
  · obtain ⟨ψ, rfl⟩ : ∃ ψ : Localization.Away f →+* S, spMap ψ = t := ⟨_, spMap_ev_top t⟩
    have hx₂ : (spMap ψ ≫ z') ≫ π = (spMap ψ ≫ spMap φ ≫ z₀) ≫ X.π := by
      rw [Category.assoc, hx', ← Category.assoc]
    exact ⟨hx₂, fun σ i => le_antisymm (step_le_bc _ _ hx' rfl hz' σ i (hs' σ i).le ψ hx₂ rfl)
      (step_le_bc _ _ rfl hx' hz₁ σ i (hs' σ i).ge ψ rfl hx₂)⟩

end DifferentiableLines.FlagIso
