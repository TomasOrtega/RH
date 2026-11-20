import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.HeatTrans

namespace GlobalTheory.Heat

/- English proof (translation)
Use `set T := tr G x with hTdef`. Establish `key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ T ⁻¹ᵁ O), (G.left.presheaf.map (homOfLE hle).op).hom (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) = (G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O))`. Introduce `U hU hle`. Set `g : Sp Γ(G.left, U) ⟶ G.left` to `hU.fromSpec`. Set `φ : R →+* Γ(G.left, U)` to `(Spec.preimage (g ≫ G.hom)).hom`.

Establish `hφ : g ≫ G.hom = spMap φ` using `by simp [φ, spMap]`. Establish `hgU : ⊤ ≤ g ⁻¹ᵁ U` using `hU.fromSpec_preimage_self.ge`. Establish `hgO : ⊤ ≤ g ⁻¹ᵁ (T ⁻¹ᵁ O)` using `hgU.trans (g.preimage_mono hle)`. Establish `hgTO : ⊤ ≤ (g ≫ T) ⁻¹ᵁ O` using `hgO`. Establish `e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ`.

Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R))` using `(Over.w (tv v)).trans (Category.comp_id _)`. Establish `h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom` using `by show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom`. Use `(Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)` and prove the remaining obligations. Rewrite using `[hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]`.

Set `g' : tEpsG (g ≫ G.hom) ⟶ G` to `Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)`. Set `v' : tEpsG (g ≫ G.hom) ⟶ G` to `Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2`. Establish `htr : IsTr G φ g v (g' * v').left` using `⟨g', v', rfl, rfl, rfl⟩`. Establish `hval` using `hinv.2 _ φ g _ (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O)) hφ hgO htr`. Establish `hT' : (g ≫ T) ≫ G.hom = g ≫ G.hom` using `by rw [Category.assoc, hTdef, tr_hom]`.

Establish `hφ₁ : (g ≫ T) ≫ G.hom = spMap φ` using `hT'.trans hφ`. Establish `eo : tEpsG ((g ≫ T) ≫ G.hom) = tEpsG (g ≫ G.hom)` using `congrArg tEpsG hT'`. Set `g'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G` to `eqToHom eo ≫ (g' * (toUnit _ ≫ x))`. Set `v'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G` to `eqToHom eo ≫ v'`. Establish `hl : ∀ k : tEpsG (g ≫ G.hom) ⟶ G, (eqToHom eo ≫ k).left = k.left`.

Introduce `k`. Rewrite using `[Over.comp_left]`. Simplify using the standard rewrite rules. Establish `hg'T : g' ≫ (𝟙 G * (toUnit G ≫ x)) = g' * (toUnit _ ≫ x)`. Rewrite using `[MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (g' ≫ toUnit G) (toUnit _)]`.

Establish `hwT : (g' * v') ≫ (𝟙 G * (toUnit G ≫ x)) = (g' * (toUnit _ ≫ x)) * v'`. Rewrite using `[MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((g' * v') ≫ toUnit G) (toUnit _), _root_.mul_assoc, _root_.mul_comm v', ← _root_.mul_assoc]`. Establish `htr₁ : IsTr G φ (g ≫ T) v ((g' * v').left ≫ T)`. Use `⟨g'₁, v'₁, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (eqToHom eo ≫ (g' * (toUnit _ ≫ x))).left = _`.

Rewrite using `[hl, ← hg'T, Over.comp_left]`. Both sides reduce to the same expression. Use `show (eqToHom eo ≫ v').left = _`. Rewrite using `[hl]`. Both sides reduce to the same expression.

Use `show (eqToHom eo ≫ (g' * (toUnit _ ≫ x)) * (eqToHom eo ≫ v')).left = _`. Rewrite using `[← MonObj.comp_mul, hl, ← hwT, Over.comp_left]`. Both sides reduce to the same expression. Establish `hval₁` using `hinv.2 _ φ (g ≫ T) _ O f hφ₁ hgTO htr₁`. Establish `hpb : ∀ s : Γ(G.left, O), pbT T s (T ⁻¹ᵁ O) = (T.app O).hom s` using `fun s => by`.

Rewrite using `[GlobalTheory.KS.pbT_of_le T le_rfl, Scheme.Hom.app_eq_appLE]`. Establish `hL : valR g (T ⁻¹ᵁ O) (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) = valR (g ≫ T) O (dd O f)`. Rewrite using `[← hval, ← hval₁, GlobalTheory.HolHom.valR_comp, hpb]`. Establish `hR : valR g (T ⁻¹ᵁ O) (pbT T (dd O f) (T ⁻¹ᵁ O)) = valR (g ≫ T) O (dd O f)`. Rewrite using `[GlobalTheory.HolHom.valR_comp, hpb]`.

Rewrite using `[← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom _), ← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O))), GlobalTheory.HolHom.valR_res g hle _ hgU, GlobalTheory.HolHom.valR_res g hle …`. Conclude with `hL.trans hR.symm`. Use `G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ T ⁻¹ᵁ O} => k.1) _ (fun k => homOfLE k.2.2) ?_ _ _ fun k => ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨U, hU, hyU, hUO⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hy`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hyU⟩`. Conclude with `key k.1 k.2.1 k.2.2`.
-/
theorem IsInv.pbT_tr_preimage {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (x : 𝟙_ (Over (Sp R)) ⟶ G)
    (O : G.left.Opens) (f : Γ(G.left, O)) :
    dd (tr G x ⁻¹ᵁ O) (pbT (tr G x) f (tr G x ⁻¹ᵁ O)) = pbT (tr G x) (dd O f) (tr G x ⁻¹ᵁ O) := by
  set T := tr G x with hTdef
  have key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ T ⁻¹ᵁ O),
      (G.left.presheaf.map (homOfLE hle).op).hom (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) =
        (G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O)) := by
    intro U hU hle
    let g : Sp Γ(G.left, U) ⟶ G.left := hU.fromSpec
    let φ : R →+* Γ(G.left, U) := (Spec.preimage (g ≫ G.hom)).hom
    have hφ : g ≫ G.hom = spMap φ := by simp [φ, spMap]
    have hgU : ⊤ ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have hgO : ⊤ ≤ g ⁻¹ᵁ (T ⁻¹ᵁ O) := hgU.trans (g.preimage_mono hle)
    have hgTO : ⊤ ≤ (g ≫ T) ⁻¹ᵁ O := hgO
    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) =
        (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
      (Over.w (tv v)).trans (Category.comp_id _)
    have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
      show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom
      refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
      rw [hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    let g' : tEpsG (g ≫ G.hom) ⟶ G :=
      Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)
    let v' : tEpsG (g ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2
    have htr : IsTr G φ g v (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩
    have hval := hinv.2 _ φ g _ (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O)) hφ hgO htr

    have hT' : (g ≫ T) ≫ G.hom = g ≫ G.hom := by rw [Category.assoc, hTdef, tr_hom]
    have hφ₁ : (g ≫ T) ≫ G.hom = spMap φ := hT'.trans hφ
    have eo : tEpsG ((g ≫ T) ≫ G.hom) = tEpsG (g ≫ G.hom) := congrArg tEpsG hT'
    let g'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G := eqToHom eo ≫ (g' * (toUnit _ ≫ x))
    let v'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G := eqToHom eo ≫ v'
    have hl : ∀ k : tEpsG (g ≫ G.hom) ⟶ G, (eqToHom eo ≫ k).left = k.left := by
      intro k; rw [Over.comp_left]; simp
    have hg'T : g' ≫ (𝟙 G * (toUnit G ≫ x)) = g' * (toUnit _ ≫ x) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (g' ≫ toUnit G) (toUnit _)]
    have hwT : (g' * v') ≫ (𝟙 G * (toUnit G ≫ x)) = (g' * (toUnit _ ≫ x)) * v' := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique ((g' * v') ≫ toUnit G) (toUnit _), _root_.mul_assoc, _root_.mul_comm v',
        ← _root_.mul_assoc]
    have htr₁ : IsTr G φ (g ≫ T) v ((g' * v').left ≫ T) := by
      refine ⟨g'₁, v'₁, ?_, ?_, ?_⟩
      · show (eqToHom eo ≫ (g' * (toUnit _ ≫ x))).left = _
        rw [hl, ← hg'T, Over.comp_left]
        rfl
      · show (eqToHom eo ≫ v').left = _
        rw [hl]
        rfl
      · show (eqToHom eo ≫ (g' * (toUnit _ ≫ x)) * (eqToHom eo ≫ v')).left = _
        rw [← MonObj.comp_mul, hl, ← hwT, Over.comp_left]
        rfl
    have hval₁ := hinv.2 _ φ (g ≫ T) _ O f hφ₁ hgTO htr₁

    have hpb : ∀ s : Γ(G.left, O), pbT T s (T ⁻¹ᵁ O) = (T.app O).hom s := fun s => by
      rw [GlobalTheory.KS.pbT_of_le T le_rfl, Scheme.Hom.app_eq_appLE]
    have hL : valR g (T ⁻¹ᵁ O) (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) = valR (g ≫ T) O (dd O f) := by
      rw [← hval, ← hval₁, GlobalTheory.HolHom.valR_comp, hpb]
    have hR : valR g (T ⁻¹ᵁ O) (pbT T (dd O f) (T ⁻¹ᵁ O)) = valR (g ≫ T) O (dd O f) := by
      rw [GlobalTheory.HolHom.valR_comp, hpb]
    rw [← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom _),
      ← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O))),
      GlobalTheory.HolHom.valR_res g hle _ hgU, GlobalTheory.HolHom.valR_res g hle _ hgU]
    exact hL.trans hR.symm
  refine G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ T ⁻¹ᵁ O} => k.1) _
    (fun k => homOfLE k.2.2) ?_ _ _ fun k => ?_
  · intro y hy
    obtain ⟨U, hU, hyU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hyU⟩
  · exact key k.1 k.2.1 k.2.2

/- English proof (translation)
Rewrite using `[← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' f, ← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' (dd O f), GlobalTheory.KS.rsT_of_le hO', GlobalTheory.KS.rsT_of_le hO', hinv.1.2.2 _ _ hO' le_top, IsInv.pbT_tr_preimage G v dd hinv x O f]`.
-/
theorem IsInv.pbT_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    (dd : Fld G.left) (hinv : IsInv G v dd) (x : 𝟙_ (Over (Sp R)) ⟶ G) (O O' : G.left.Opens)
    (hO' : O' ≤ tr G x ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    dd O' (pbT (tr G x) f O') = pbT (tr G x) (dd O f) O' := by
  rw [← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' f, ← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' (dd O f),
    GlobalTheory.KS.rsT_of_le hO', GlobalTheory.KS.rsT_of_le hO', hinv.1.2.2 _ _ hO' le_top,
    IsInv.pbT_tr_preimage G v dd hinv x O f]

end GlobalTheory.Heat
