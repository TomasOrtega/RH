import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.LieRel

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [QuasiSeparated G.hom]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Establish `h1 : ptMap (TrivSqZeroExt.fstHom R R R) ≫ (1 : specO R (DualNumber R) ⟶ G) = 1` using `MonObj.comp_one _`. Use `⟨⟨1, h1⟩, rfl, ?_⟩` and prove the remaining obligations. Establish `h2` using `tangent_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩ (OmegaGlobal.fst_mul _ _)`.

Establish `h3 : (⟨_, OmegaGlobal.fst_mul (G` using `G) ⟨1, h1⟩ ⟨1, h1⟩⟩ : LieG G) = ⟨1, h1⟩ := Subtype.ext (_root_.mul_one _)`. Rewrite `h2` using `[h3]`. Simplify using `using h2`. Consider the case `cons x l ih`. Take `⟨z, hz, hz'⟩` from `ih`.

Use `⟨⟨_, OmegaGlobal.fst_mul x z⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_cons, List.prod_cons, ← hz]`. Rewrite using `[tangent_mul, hz', List.map_cons, List.sum_cons]`.
-/
theorem exists_prod (l : List (LieG G)) :
    ∃ z : LieG G, z.1 = (l.map fun x => x.1).prod ∧ tangent z = (l.map tangent).sum := by
  induction l with
  | nil =>
    have h1 : ptMap (TrivSqZeroExt.fstHom R R R) ≫ (1 : specO R (DualNumber R) ⟶ G) = 1 := MonObj.comp_one _
    refine ⟨⟨1, h1⟩, rfl, ?_⟩
    have h2 := tangent_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩ (OmegaGlobal.fst_mul _ _)
    have h3 : (⟨_, OmegaGlobal.fst_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩⟩ : LieG G) = ⟨1, h1⟩ :=
      Subtype.ext (_root_.mul_one _)
    rw [h3] at h2
    simpa using h2
  | cons x l ih =>
    obtain ⟨z, hz, hz'⟩ := ih
    refine ⟨⟨_, OmegaGlobal.fst_mul x z⟩, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← hz]
    · rw [tangent_mul, hz', List.map_cons, List.sum_cons]

/- English proof (translation)
Set `u : Fin n → LieG G` to `fun m => ⟨_, OmegaGlobal.fst_scale (a m) (v m)⟩`. Take `⟨z, hz, hz'⟩` from `exists_prod (List.ofFn u)`. Establish `e : w = z` using `tangent_injective R G (by`. Rewrite using `[h, hz', List.map_ofFn, List.sum_ofFn]`. Conclude with `Finset.sum_congr rfl fun m _ => (tangent_scale _ _ _).symm)`.

Use `⟨fun m => (u m).1, fun m => ?_, ?_⟩` and prove the remaining obligations. Establish `ha : (dualScale (a m)).toRingHom = epsScaleR (a m)`. Apply the tactic sequence `ext y <;> simp [dualScale, epsScaleR]`. Conclude with `congrArg (fun r => spMap r ≫ (v m).1.left) ha`. Rewrite using `[e, hz, List.map_ofFn]`.

Both sides reduce to the same expression.
-/
theorem isLieComb_of_tangent {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G)
    (h : tangent w = ∑ m, cst R (a m) • tangent (v m)) : IsLieComb a (fun m => (v m).1) w.1 := by
  let u : Fin n → LieG G := fun m => ⟨_, OmegaGlobal.fst_scale (a m) (v m)⟩
  obtain ⟨z, hz, hz'⟩ := exists_prod (List.ofFn u)
  have e : w = z := tangent_injective R G (by
    rw [h, hz', List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun m _ => (tangent_scale _ _ _).symm)
  refine ⟨fun m => (u m).1, fun m => ?_, ?_⟩
  · have ha : (dualScale (a m)).toRingHom = epsScaleR (a m) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v m).1.left) ha
  · rw [e, hz, List.map_ofFn]
    rfl

/- English proof (translation)
Use `⟨fun j m => (Scheme.ΓSpecIso (.of R)).hom (dualApp (tangent (v j)) le_top (e' m)), fun j => ?_, ?_⟩` and prove the remaining obligations. Use `isLieComb_of_tangent _ _ _ (he'.dual_ext le_rfl fun k => ?_)` and prove the remaining obligations. Rewrite using `[resM_self, dualApp_sum, LinearMap.sum_apply]`. Simplify using `only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, LB.resG_self]`. Rewrite using `[Finset.sum_congr rfl fun m _ => congrArg (cst R _ * ·) (hv' m k)]`.

Simplify using the standard rewrite rules. Establish `hc (j : Fin g) : tangent (v j) = he.coord j` using `he.dual_ext le_rfl fun k => by`. Rewrite using `[he.dualApp_coord_frame, resM_self]`. Conclude with `(hv j k).trans (by simp only [eq_comm])`. Rewrite using `[IsFrame.val_detUnit, Module.Basis.det_apply]`.

Use `Eq.trans ?_ (RingHom.map_det (Scheme.ΓSpecIso (.of R)).hom.hom _).symm` and prove the remaining obligations. Use `congr 1`. Use extensionality with `j m`. Rewrite using `[hc, RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, resM_self]`. Both sides reduce to the same expression.
-/
theorem exists_matrix {g : ℕ} {e e' : Fin g → Γ(omega G, ⊤)} (he : IsFrame e) (he' : IsFrame e') (v v' : Fin g → LieG G)
    (hv : ∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0)
    (hv' : ∀ j k, dualApp (tangent (v' j)) le_top (e' k) = if j = k then 1 else 0) :
    ∃ M : Matrix (Fin g) (Fin g) R, (∀ j, IsLieComb (M j) (fun m => (v' m).1) (v j).1) ∧
      M.det = (Scheme.ΓSpecIso (.of R)).hom (he.detUnit he' le_rfl le_rfl : Γ(Sp R, ⊤)) := by
  refine ⟨fun j m => (Scheme.ΓSpecIso (.of R)).hom (dualApp (tangent (v j)) le_top (e' m)), fun j => ?_, ?_⟩
  · refine isLieComb_of_tangent _ _ _ (he'.dual_ext le_rfl fun k => ?_)
    rw [resM_self, dualApp_sum, LinearMap.sum_apply]
    simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, LB.resG_self]
    rw [Finset.sum_congr rfl fun m _ => congrArg (cst R _ * ·) (hv' m k)]
    simp
  · have hc (j : Fin g) : tangent (v j) = he.coord j := he.dual_ext le_rfl fun k => by
      rw [he.dualApp_coord_frame, resM_self]
      exact (hv j k).trans (by simp only [eq_comm])
    rw [IsFrame.val_detUnit, Module.Basis.det_apply]
    refine Eq.trans ?_ (RingHom.map_det (Scheme.ΓSpecIso (.of R)).hom.hom _).symm
    congr 1
    ext j m
    rw [hc, RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, resM_self]
    rfl

end Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {g : ℕ}

/- English proof (translation)
The claim follows from `funext fun _ => congrArg _ (QCoh.res_pullbackSections ξ _ _ _ _).symm`.
-/
theorem pfr_eq (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) :
    pfr c ξ hc = fun k => (omegaBase (isGrpPullback_pullback G ξ)).app ⊤
      (resM _ hc (QCoh.pullbackSections ξ (omega G) (le_refl (ξ ⁻¹ᵁ c.U)) (c.e k))) :=
  funext fun _ => congrArg _ (QCoh.res_pullbackSections ξ _ _ _ _).symm

/- English proof (translation)
Rewrite using `[pfr_eq]`. Conclude with `((c.isFrame.pullback ξ).res hc).map_iso _`.
-/
theorem isFrame_pfr (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) : IsFrame (pfr c ξ hc) := by
  rw [pfr_eq]
  exact ((c.isFrame.pullback ξ).res hc).map_iso _

/- English proof (translation)
Establish `key {e e' f f' : Fin g → Γ(omega (bG G ξ), ⊤)} (he : IsFrame e) (he' : IsFrame e') (hf : IsFrame f) (hf' : IsFrame f') (h₁ : e = f) (h₂ : e' = f') : he.detUnit he' le_rfl le_rfl = hf.detUnit hf' le_rfl le_rfl`. Substitute `h₁ h₂` using the available equality. Both sides reduce to the same expression. Rewrite using `[key _ _ (((c.isFrame.pullback ξ).res hc).map_iso (omegaBase (isGrpPullback_pullback G ξ))) (((c'.isFrame.pullback ξ).res hc').map_iso (omegaBase (isGrpPullback_pullback G ξ))) (pfr_eq c ξ hc) (pfr_eq c' ξ hc'), IsFrame.detUnit_map_iso ((c.isFrame.pullback ξ).res hc) ((c'.isFrame …`. Conclude with `c.isFrame.val_detUnit_pullback c'.isFrame ξ inf_le_left inf_le_right h`.
-/
theorem val_detUnit_pfr (c c' : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (hc' : ⊤ ≤ ξ ⁻¹ᵁ c'.U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ((isFrame_pfr c ξ hc).detUnit (isFrame_pfr c' ξ hc') le_rfl le_rfl : Γ(Sp R, ⊤)) =
      (ξ.appLE (c.U ⊓ c'.U) ⊤ h).hom (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right : Γ(S, c.U ⊓ c'.U)) := by
  have key {e e' f f' : Fin g → Γ(omega (bG G ξ), ⊤)} (he : IsFrame e) (he' : IsFrame e') (hf : IsFrame f)
      (hf' : IsFrame f') (h₁ : e = f) (h₂ : e' = f') :
      he.detUnit he' le_rfl le_rfl = hf.detUnit hf' le_rfl le_rfl := by
    subst h₁ h₂; rfl
  rw [key _ _ (((c.isFrame.pullback ξ).res hc).map_iso (omegaBase (isGrpPullback_pullback G ξ)))
    (((c'.isFrame.pullback ξ).res hc').map_iso (omegaBase (isGrpPullback_pullback G ξ))) (pfr_eq c ξ hc) (pfr_eq c' ξ hc'),
    IsFrame.detUnit_map_iso ((c.isFrame.pullback ξ).res hc) ((c'.isFrame.pullback ξ).res hc'),
    IsFrame.detUnit_res (c.isFrame.pullback ξ) (c'.isFrame.pullback ξ)]
  exact c.isFrame.val_detUnit_pullback c'.isFrame ξ inf_le_left inf_le_right h

/- English proof (translation)
Establish `k : ⊤ ≤ S.fromSpecStalk (genericPoint S) ⁻¹ᵁ U` using `genPt_le U hU`. Establish `e : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k = S.presheaf.germ U _ hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv`. Rewrite using `[Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]`. Simplify using `only [Category.assoc, ← Functor.map_comp]`. Establish `e : ((homOfLE le_top).op ≫ (homOfLE k).op : Opposite.op (⊤ : (Spec (S.presheaf.stalk (genericPoint S))).Opens) ⟶ Opposite.op ⊤) = 𝟙 _` using `rfl`.

Rewrite using `[e, CategoryTheory.Functor.map_id, Category.comp_id]`. Establish `e' : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).hom = S.presheaf.germ U _ hU`. Rewrite using `[e, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Conclude with `congr($e' a)`.
-/
theorem genPt_appLE [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    (Scheme.ΓSpecIso (.of (FF S))).hom (((genPt S).appLE U ⊤ (genPt_le U hU)).hom a) =
      S.presheaf.germ U (genericPoint S) hU a := by
  have k : ⊤ ≤ S.fromSpecStalk (genericPoint S) ⁻¹ᵁ U := genPt_le U hU
  have e : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k =
      S.presheaf.germ U _ hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE k).op :
      Opposite.op (⊤ : (Spec (S.presheaf.stalk (genericPoint S))).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  have e' : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k ≫
      (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).hom = S.presheaf.germ U _ hU := by
    rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congr($e' a)

/- English proof (translation)
Introduce `S _ G _ _ g hG _ c c' h1 y y' ⟨hc, hy⟩ ⟨hc', hy'⟩`. Use `choose v hv hv₁ using hy`. Use `choose v' hv' hv₁' using hy'`. Establish `: QuasiSeparated (bG G (genPt S)).hom` using `MorphismProperty.of_isPullback (isGrpPullback_pullback G (genPt S)).1 inferInstance`. Take `⟨M, hM, hd⟩` from `exists_matrix (isFrame_pfr c _ hc) (isFrame_pfr c' _ hc') v v' hv₁ hv₁'`.

Take `rfl : (fun j => (v j).1) = y` from `funext hv`. Take `rfl : (fun j => (v' j).1) = y'` from `funext hv'`. Use `⟨M, hM, hd.trans ?_⟩` and prove the remaining obligations. Rewrite using `[val_detUnit_pfr c c' _ hc hc' (genPt_le _ h1)]`. Conclude with `genPt_appLE _ h1 _`.
-/
theorem lieRel : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  intro S _ G _ _ g hG _ c c' h1 y y' ⟨hc, hy⟩ ⟨hc', hy'⟩
  choose v hv hv₁ using hy
  choose v' hv' hv₁' using hy'
  have : QuasiSeparated (bG G (genPt S)).hom :=
    MorphismProperty.of_isPullback (isGrpPullback_pullback G (genPt S)).1 inferInstance
  obtain ⟨M, hM, hd⟩ := exists_matrix (isFrame_pfr c _ hc) (isFrame_pfr c' _ hc') v v' hv₁ hv₁'
  obtain rfl : (fun j => (v j).1) = y := funext hv
  obtain rfl : (fun j => (v' j).1) = y' := funext hv'
  refine ⟨M, hM, hd.trans ?_⟩
  rw [val_detUnit_pfr c c' _ hc hc' (genPt_le _ h1)]
  exact genPt_appLE _ h1 _

end GlobalTheory.KeyVals.LieRel

end
