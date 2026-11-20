import Mathlib
import Development.AutomorphicArithmetic.GenericGermInjectivity.CoverGeneric
import Development.AutomorphicArithmetic.CommutativeAlgebra.FunctionFieldOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteEtaleFunctionFieldIntegralClosureDifferentStatement

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace UpperTheory.GenericCoverClass

section Tr

variable {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {p : Z ⟶ Sp ℂ} {p' : Y ⟶ Sp ℂ}
  [inst' : Algebra ℂ Y.functionField] {c : Y ⟶ Z} {ι : Type} {U : ι → Z.Opens}
  {B' : Finset ι → Subalgebra ℂ Y.functionField}

/- English proof (translation)
Use extensionality with `y`. Express the relevant statement in the definitionally equal form `c.base y ∈ cechOpen ⊤ U s ↔ y ∈ cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s`. Rewrite using `[mem_cechOpen, mem_cechOpen]`. Both sides reduce to the same expression.
-/
theorem preimage_cech (s : Finset ι) :
    c ⁻¹ᵁ cechOpen ⊤ U s = cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s := by
  ext y
  change c.base y ∈ cechOpen ⊤ U s ↔ y ∈ cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s
  rw [mem_cechOpen, mem_cechOpen]
  rfl

/- English proof (translation)
Rewrite using `[preimage_cech]`. Conclude with `cover_affine hU' h`.
-/
theorem pre_affine (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') {s : Finset ι} (h : s.Nonempty) :
    IsAffineOpen (c ⁻¹ᵁ cechOpen ⊤ U s) := by
  rw [preimage_cech]; exact cover_affine hU' h

/- English proof (translation)
Rewrite using `[preimage_cech]`. Conclude with `cover_generic hU' s`.
-/
theorem pre_generic (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (s : Finset ι) :
    genericPoint Y ∈ c ⁻¹ᵁ cechOpen ⊤ U s := by
  rw [preimage_cech]; exact cover_generic hU' s

variable (hc : c ≫ p = p')

def up (a : ℕ) (W : Z.Opens) :
    letI := algΓ p; letI := algΓ p'
    sectionsOn ((Scheme.Modules.pushforward c).obj (Omega p' a)) W →ₗ[ℂ]
      sectionsOn (Omega p' a) (c ⁻¹ᵁ W) :=
  letI := algΓ p; letI := algΓ p'
  sectionsOn.mapOver (appTop_algebraMap hc) (𝟙 _) W

/- English proof (translation)
Use `letI := algΓ p`. Use `letI := algΓ p'`. Conclude with `⟨fun x y h => (sectionsOn.toΓ _ _).injective ((sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W)).injective.eq_iff.2 h), fun y => ⟨(sectionsOn.toΓ _ _).symm (sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W) y), rfl⟩⟩`.
-/
theorem up_bijective (a : ℕ) (W : Z.Opens) :
    letI := algΓ p; letI := algΓ p'
    Function.Bijective (up hc a W) := by
  letI := algΓ p; letI := algΓ p'
  exact ⟨fun x y h => (sectionsOn.toΓ _ _).injective
      ((sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W)).injective.eq_iff.2 h),
    fun y => ⟨(sectionsOn.toΓ _ _).symm (sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W) y), rfl⟩⟩

end Tr

section Gp

variable {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {p : Z ⟶ Sp ℂ} (p' : Y ⟶ Sp ℂ)
  [inst' : Algebra ℂ Y.functionField] {c : Y ⟶ Z} {ι : Type} {U : ι → Z.Opens}
  {B' : Finset ι → Subalgebra ℂ Y.functionField}

def gp (hc : c ≫ p = p') (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B')
    (a : ℕ) (s : Finset ι) :
    letI := algΓ p
    (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U).obj s →ₗ[ℂ]
      DR ℂ Y.functionField :=
  letI := algΓ p; letI := algΓ p'
  if h : s.Nonempty then
    (formGermI p' a (pre_affine hU' h) (pre_generic hU' s) hinst') ∘ₗ
      up hc a (cechOpen ⊤ U s)
  else 0

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem gp_pos (hc : c ≫ p = p') (hinst' : inst' = ffAlg p')
    (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) {s : Finset ι} (h : s.Nonempty) :
    letI := algΓ p; letI := algΓ p'
    gp p' hc hinst' hU' a s =
      (formGermI p' a (pre_affine hU' h) (pre_generic hU' s) hinst') ∘ₗ
        up hc a (cechOpen ⊤ U s) :=
  dif_pos h

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `UpperTheory.affineCechOpen_functionField_generic d Y p' ι _ B' hinst' hU' a s hs hV hη`.
-/
theorem germ_inj_range_pre (d : ℕ) [SmoothOfRelativeDimension d p'] (hinst' : inst' = ffAlg p')
    (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) (s : Finset ι) (hs : s.Nonempty)
    (V : Y.Opens) (e : V = cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s) (hV : IsAffineOpen V)
    (hη : genericPoint Y ∈ V) :
    letI := algΓ p'
    Function.Injective (formGermI p' a hV hη hinst') ∧
      LinearMap.range (formGermI p' a hV hη hinst') = omB ℂ Y.functionField (B' s) a := by
  subst e
  exact UpperTheory.affineCechOpen_functionField_generic d Y p' ι _ B' hinst' hU' a s hs hV hη

/- English proof (translation)
Use `letI := algΓ p`. Use `letI := algΓ p'`. Use `⟨fun s hs => ?_, fun s hs => ?_, fun s t h hs y => ?_⟩` and prove the remaining obligations. Rewrite using `[gp_pos p' hc hinst' hU' a hs]`. Conclude with `(germ_inj_range_pre p' d hinst' hU' a s hs _ (preimage_cech s) _ _).1.comp (up_bijective hc a _).1`.

Rewrite using `[gp_pos p' hc hinst' hU' a hs]`. Use `Eq.trans (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (up_bijective hc a _).2)) ?_` and prove the remaining obligations. Conclude with `(germ_inj_range_pre p' d hinst' hU' a s hs _ (preimage_cech s) _ _).2`. Rewrite using `[gp_pos p' hc hinst' hU' a hs, gp_pos p' hc hinst' hU' a (hs.mono h)]`. Conclude with `GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen Y p' hinst' a _ _ _ _ _ _ (c.preimage_mono (cechOpen_anti ⊤ U h)) _`.
-/
theorem gp_spec (d : ℕ) [SmoothOfRelativeDimension d p'] (hc : c ≫ p = p')
    (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) :
    letI := algΓ p
    (∀ s, s.Nonempty → Function.Injective (gp p' hc hinst' hU' a s)) ∧
    (∀ s, s.Nonempty → LinearMap.range (gp p' hc hinst' hU' a s) = omB ℂ Y.functionField (B' s) a) ∧
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ y,
      gp p' hc hinst' hU' a t
        (Cube.res (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U) h y) =
      gp p' hc hinst' hU' a s y) := by
  letI := algΓ p; letI := algΓ p'
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s t h hs y => ?_⟩
  · rw [gp_pos p' hc hinst' hU' a hs]
    exact (germ_inj_range_pre p' d hinst' hU' a s hs _ (preimage_cech s) _ _).1.comp
      (up_bijective hc a _).1
  · rw [gp_pos p' hc hinst' hU' a hs]
    refine Eq.trans (LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 (up_bijective hc a _).2)) ?_
    exact (germ_inj_range_pre p' d hinst' hU' a s hs _ (preimage_cech s) _ _).2
  · rw [gp_pos p' hc hinst' hU' a hs, gp_pos p' hc hinst' hU' a (hs.mono h)]
    exact GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen Y p' hinst' a _ _ _ _ _ _ (c.preimage_mono (cechOpen_anti ⊤ U h)) _

end Gp

section Main

/- English proof (translation)
Use `letI := algΓ p`. Use `letI := algΓ p'`. Establish `hfin` using `(GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials Z Y p p' c hc inferInstance inferInstance d hinst hinst' hg).1`. Take `⟨z1, hz1⟩` from `cechClass_surjective (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U) b ((cechHEquivCoh ℂ hU.cover (cover_biInf hU) ((Scheme.Modules.pushforward c).obj (Omega p' a)) b).symm ((coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z))`. Establish `hs` using `gp_spec (p := p) (U := U) (B' := B') p' d hc hinst' hU' a`.

Take `⟨-, -, h2, -⟩` from `GlobalTheory.T.cechHomologyEquivFamAlt ℂ ι (DR ℂ Y.functionField) (fun I => omB ℂ Y.functionField (B' I) a) (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U) (gp p' hc hinst' hU' a) hs.1 hs.2.1 hs.2.2 b`. Take `⟨w, hw⟩` from `h2 z1`. Establish `hle : ∀ s : Finset ι, cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s ≤ c ⁻¹ᵁ cechOpen ⊤ U s` using `fun s => (preimage_cech s).ge`. Establish `hne : ∀ t : {s : Finset ι // s.card = b + 1}, t.1.Nonempty` using `fun t => Finset.card_pos.1 (by rw [t.2]; omega)`. Set `x0 : Cube.Term (cechCube ℂ (Omega p' a) ⊤ fun i => c ⁻¹ᵁ U i) (b + 1)` to `fun t => sectionsOn.res ℂ (Omega p' a) (hle t.1) (up hc a _ (z1.1 t))`.

Establish `hx0 : ∀ t : {s : Finset ι // s.card = b + 1}, (w : Finset ι → DR ℂ Y.functionField) t.1 = gm p' hinst' hU' a t.1 (x0 t)`. Introduce `t`. Rewrite using `[hw t, gp_pos p' hc hinst' hU' a (hne t), gm_pos hinst' hU' a (hne t)]`. Conclude with `(GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen Y p' hinst' a _ _ _ _ _ _ (hle t.1) _).symm`. Establish `hd` using `(Classical.choose_spec (cube_exists d p' hinst' hU' a b)).2.2 x0 w hx0`.

Set `z0 : LinearMap.ker (Cube.d (cechCube ℂ (Omega p' a) ⊤ fun i => c ⁻¹ᵁ U i) (b + 1))` to `⟨x0, hd⟩`. Establish `key` using `GlobalTheory.T.scheme_cechComparison_natural_refinement Z Y ℂ c (appTop_algebraMap hc) ((Scheme.Modules.pushforward c).obj (Omega p' a)) (Omega p' a) (𝟙 _) ι ι U (fun i => c ⁻¹ᵁ U i) hU.cover (cover_biInf hU) hU'.cover (cover_biInf hU') id (fun _ => le_rfl) b z1 z0 (fun t s h _ e …`. Take `rfl : s = t` from `Subtype.ext (by simpa using e)`. Establish `h1 : sortSign (id : ι → ι) s.1 = 1`. Use `Finset.prod_eq_one fun x _ => Finset.prod_eq_one fun y _ => ?_` and prove the remaining obligations.

Conclude with `if_neg fun h => lt_asymm h.1 h.2`. Rewrite using `[h1, one_smul]`. Use the proof step `rfl) (fun t h => absurd Function.injective_id.injOn h)`. Establish `hback : cechHEquivCoh ℂ hU.cover (cover_biInf hU) ((Scheme.Modules.pushforward c).obj (Omega p' a)) b (cechClass _ b z1) = (coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z`. Rewrite using `[hz1]`.

Conclude with `LinearEquiv.apply_symm_apply _ _`. Establish `hz : cechHEquivCoh ℂ hU'.cover (cover_biInf hU') (Omega p' a) b (cechClass _ b z0) = z`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[hback]`. Conclude with `LinearEquiv.apply_symm_apply (coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b) z`.

Set `z2 : LinearMap.ker (Cube.d (cechCube ℂ (Omega p a) ⊤ U) (b + 1))` to `⟨Cube.termMap (cechCubeMap ℂ ⊤ U (omegaTrace hc a)) (b + 1) z1.1, Cube.termMap_mem_ker _ z1.2⟩`. Establish `hTw` using `hm b w w.2.1`. Establish `hTw' : (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) (w : Finset ι → DR ℂ Y.functionField) ∈ (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ)`. Use `⟨hTw.1, ?_⟩` and prove the remaining obligations. Establish `h0 : (GlobalTheory.PD.cech fun I => omB ℂ Y.functionField (B' I) a).D w = 0` using `w.2.2`.

Express the relevant statement in the definitionally equal form `_ = 0`. Rewrite using `[← hTw.2, h0, map_zero]`. Set `w2 : (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ)` to `⟨_, hTw'⟩`. Establish `hw2 : ∀ t : {s : Finset ι // s.card = b + 1}, (w2 : Finset ι → DR ℂ Z.functionField) t.1 = gm p hinst hU a t.1 (z2.1 t)`. Introduce `t`.

Express the relevant statement in the definitionally equal form `GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField ((w : Finset ι → DR ℂ Y.functionField) t.1) = _`. Rewrite using `[hw t, gp_pos p' hc hinst' hU' a (hne t), gm_pos hinst hU a (hne t)]`. Conclude with `(UpperTheory.functionField_of_finite_etale_cover Z Y p p' c hc hinst hinst' hg hfin a _ (cover_affine hU (hne t)) (cover_generic hU _) (pre_generic hU' _) _).symm`. Establish `htr : hodgeTrace hc a b z = cechHEquivCoh ℂ hU.cover (cover_biInf hU) (Omega p a) b (cechClass _ b z2)`. Express the relevant statement in the definitionally equal form `cohOn.map ℂ (omegaTrace hc a) ⊤ b ((coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z) = _`.

Rewrite using `[← hback]`. Use `(cechHEquivCoh_map ℂ hU.cover (cover_biInf hU) (omegaTrace hc a) b (cechClass _ b z1)).symm.trans ?_` and prove the remaining obligations. Conclude with `congrArg _ (homologyMap_cechClass (cechCubeMap ℂ ⊤ U (omegaTrace hc a)) b z1 z2 rfl)`. Establish `e1` using `cmp_class d p' hinst' hU' a b z0 w hx0`. Establish `e2` using `cmp_class d p hinst hU a b z2 w2 hw2`.

Rewrite `e1` using `[hz]`. Rewrite using `[htr, e2, e1]`. Both sides reduce to the same expression.
-/
theorem cmp_trace (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (Y : Scheme.{0}) [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d p'] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (B' : Finset ι → Subalgebra ℂ Y.functionField) (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B')
    (hg : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g))
    (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Y.functionField (B' I) a) (cech fun I => omB ℂ Z.functionField (B I) a) (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s))) (z : hodgeH p' a b) :
    cmp d p hinst hU a b (hodgeTrace hc a b z) = Cx.hmap _ _ (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) hm b (cmp d p' hinst' hU' a b z) := by
  letI := algΓ p
  letI := algΓ p'
  have hfin := (GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials Z Y p p' c hc inferInstance inferInstance d hinst hinst' hg).1
  obtain ⟨z1, hz1⟩ := cechClass_surjective
    (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U) b
    ((cechHEquivCoh ℂ hU.cover (cover_biInf hU) ((Scheme.Modules.pushforward c).obj (Omega p' a)) b).symm
      ((coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z))
  have hs := gp_spec (p := p) (U := U) (B' := B') p' d hc hinst' hU' a
  obtain ⟨-, -, h2, -⟩ := GlobalTheory.T.cechHomologyEquivFamAlt ℂ ι (DR ℂ Y.functionField)
    (fun I => omB ℂ Y.functionField (B' I) a)
    (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U)
    (gp p' hc hinst' hU' a) hs.1 hs.2.1 hs.2.2 b
  obtain ⟨w, hw⟩ := h2 z1
  have hle : ∀ s : Finset ι, cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s ≤ c ⁻¹ᵁ cechOpen ⊤ U s :=
    fun s => (preimage_cech s).ge
  have hne : ∀ t : {s : Finset ι // s.card = b + 1}, t.1.Nonempty := fun t =>
    Finset.card_pos.1 (by rw [t.2]; omega)
  let x0 : Cube.Term (cechCube ℂ (Omega p' a) ⊤ fun i => c ⁻¹ᵁ U i) (b + 1) := fun t =>
    sectionsOn.res ℂ (Omega p' a) (hle t.1) (up hc a _ (z1.1 t))
  have hx0 : ∀ t : {s : Finset ι // s.card = b + 1},
      (w : Finset ι → DR ℂ Y.functionField) t.1 = gm p' hinst' hU' a t.1 (x0 t) := by
    intro t
    rw [hw t, gp_pos p' hc hinst' hU' a (hne t), gm_pos hinst' hU' a (hne t)]
    exact (GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen Y p' hinst' a _ _ _ _ _ _ (hle t.1) _).symm
  have hd := (Classical.choose_spec (cube_exists d p' hinst' hU' a b)).2.2 x0 w hx0
  let z0 : LinearMap.ker (Cube.d (cechCube ℂ (Omega p' a) ⊤ fun i => c ⁻¹ᵁ U i) (b + 1)) := ⟨x0, hd⟩
  have key := GlobalTheory.T.scheme_cechComparison_natural_refinement Z Y ℂ c (appTop_algebraMap hc)
    ((Scheme.Modules.pushforward c).obj (Omega p' a)) (Omega p' a) (𝟙 _) ι ι U
    (fun i => c ⁻¹ᵁ U i) hU.cover (cover_biInf hU) hU'.cover (cover_biInf hU') id (fun _ => le_rfl) b
    z1 z0 (fun t s h _ e => by
      obtain rfl : s = t := Subtype.ext (by simpa using e)
      have h1 : sortSign (id : ι → ι) s.1 = 1 := by
        refine Finset.prod_eq_one fun x _ => Finset.prod_eq_one fun y _ => ?_
        exact if_neg fun h => lt_asymm h.1 h.2
      rw [h1, one_smul]
      rfl) (fun t h => absurd Function.injective_id.injOn h)
  have hback : cechHEquivCoh ℂ hU.cover (cover_biInf hU)
      ((Scheme.Modules.pushforward c).obj (Omega p' a)) b (cechClass _ b z1) =
      (coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z := by
    rw [hz1]; exact LinearEquiv.apply_symm_apply _ _
  have hz : cechHEquivCoh ℂ hU'.cover (cover_biInf hU') (Omega p' a) b (cechClass _ b z0) = z := by
    refine key.trans ?_
    rw [hback]
    exact LinearEquiv.apply_symm_apply (coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b) z
  let z2 : LinearMap.ker (Cube.d (cechCube ℂ (Omega p a) ⊤ U) (b + 1)) :=
    ⟨Cube.termMap (cechCubeMap ℂ ⊤ U (omegaTrace hc a)) (b + 1) z1.1,
      Cube.termMap_mem_ker _ z1.2⟩
  have hTw := hm b w w.2.1
  have hTw' : (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) (w : Finset ι → DR ℂ Y.functionField) ∈
      (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ) := by
    refine ⟨hTw.1, ?_⟩
    have h0 : (GlobalTheory.PD.cech fun I => omB ℂ Y.functionField (B' I) a).D w = 0 := w.2.2
    change _ = 0
    rw [← hTw.2, h0, map_zero]
  let w2 : (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ) := ⟨_, hTw'⟩
  have hw2 : ∀ t : {s : Finset ι // s.card = b + 1},
      (w2 : Finset ι → DR ℂ Z.functionField) t.1 = gm p hinst hU a t.1 (z2.1 t) := by
    intro t
    change GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField ((w : Finset ι → DR ℂ Y.functionField) t.1) = _
    rw [hw t, gp_pos p' hc hinst' hU' a (hne t), gm_pos hinst hU a (hne t)]
    exact (UpperTheory.functionField_of_finite_etale_cover Z Y p p' c hc hinst hinst' hg hfin a _ (cover_affine hU (hne t))
      (cover_generic hU _) (pre_generic hU' _) _).symm
  have htr : hodgeTrace hc a b z =
      cechHEquivCoh ℂ hU.cover (cover_biInf hU) (Omega p a) b (cechClass _ b z2) := by
    change cohOn.map ℂ (omegaTrace hc a) ⊤ b
      ((coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z) = _
    rw [← hback]
    refine (cechHEquivCoh_map ℂ hU.cover (cover_biInf hU) (omegaTrace hc a) b
      (cechClass _ b z1)).symm.trans ?_
    exact congrArg _ (homologyMap_cechClass (cechCubeMap ℂ ⊤ U (omegaTrace hc a)) b z1 z2 rfl)
  have e1 := cmp_class d p' hinst' hU' a b z0 w hx0
  have e2 := cmp_class d p hinst hU a b z2 w2 hw2
  rw [hz] at e1
  rw [htr, e2, e1]
  rfl

end Main

end UpperTheory.GenericCoverClass
