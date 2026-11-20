import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Take `⟨h0, hi⟩` from `h`. Establish `h1 : ∀ j, (σ j ≫ y) ≫ s' = c ≫ z` using `fun j => by`. Rewrite using `[Category.assoc, hy, ← Category.assoc, h0 j]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `ec : (pullback.fst s c ≫ y) ≫ s' = pullback.snd s c ≫ c ≫ z`.

Rewrite using `[Category.assoc, hy, ← Category.assoc, pullback.condition, Category.assoc]`. Establish `ec' : (pullback.fst s' (c ≫ z) ≫ inv y) ≫ s = pullback.snd s' (c ≫ z) ≫ c`. Rewrite using `[← cancel_mono z, Category.assoc, Category.assoc, Category.assoc, ← hy, IsIso.inv_hom_id_assoc, pullback.condition]`. Set `e : pullback s c ⟶ pullback s' (c ≫ z)` to `pullback.lift _ _ ec`. Set `e' : pullback s' (c ≫ z) ⟶ pullback s c` to `pullback.lift _ _ ec'`.

Establish `e1 : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ y` using `pullback.lift_fst _ _ _`. Establish `e2 : e ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `e1' : e' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ inv y` using `pullback.lift_fst _ _ _`. Establish `e2' : e' ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `he : IsIso e`.

Use `⟨e', pullback.hom_ext ?_ ?_, pullback.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, e1', ← Category.assoc, e1, Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]`. Rewrite using `[Category.assoc, e2', e2, Category.id_comp]`. Rewrite using `[Category.assoc, e1, ← Category.assoc, e1', Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]`. Rewrite using `[Category.assoc, e2, e2', Category.id_comp]`.

Establish `key : (Sigma.desc (fun j => pullback.lift (σ j ≫ y) (𝟙 W) (by rw [h1 j, Category.id_comp])) : ∐ (fun _ : J => W) ⟶ pullback s' (c ≫ z)) = Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h0 j, Category.id_comp])) ≫ e`. Use `Sigma.hom_ext _ _ fun j => ?_` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc, Sigma.ι_desc_assoc]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, Category.assoc, e1, pullback.lift_fst_assoc]`.

Rewrite using `[pullback.lift_snd, Category.assoc, e2, pullback.lift_snd]`. Rewrite using `[key]`. Conclude with `IsIso.comp_isIso`.
-/
private theorem splits_transport {Z Y W Z' Y' : Scheme.{0}} {J : Type} {s : Y ⟶ Z} {c : W ⟶ Z} {σ : J → (W ⟶ Y)}
    (y : Y ⟶ Y') [IsIso y] (z : Z ⟶ Z') [IsIso z] (s' : Y' ⟶ Z') (hy : y ≫ s' = s ≫ z)
    (h : GlobalTheory.GalV.Splits s c σ) : GlobalTheory.GalV.Splits s' (c ≫ z) (fun j => σ j ≫ y) := by
  obtain ⟨h0, hi⟩ := h
  have h1 : ∀ j, (σ j ≫ y) ≫ s' = c ≫ z := fun j => by
    rw [Category.assoc, hy, ← Category.assoc, h0 j]
  refine ⟨h1, ?_⟩
  have ec : (pullback.fst s c ≫ y) ≫ s' = pullback.snd s c ≫ c ≫ z := by
    rw [Category.assoc, hy, ← Category.assoc, pullback.condition, Category.assoc]
  have ec' : (pullback.fst s' (c ≫ z) ≫ inv y) ≫ s = pullback.snd s' (c ≫ z) ≫ c := by
    rw [← cancel_mono z, Category.assoc, Category.assoc, Category.assoc, ← hy, IsIso.inv_hom_id_assoc,
      pullback.condition]
  let e : pullback s c ⟶ pullback s' (c ≫ z) := pullback.lift _ _ ec
  let e' : pullback s' (c ≫ z) ⟶ pullback s c := pullback.lift _ _ ec'
  have e1 : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ y := pullback.lift_fst _ _ _
  have e2 : e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have e1' : e' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ inv y := pullback.lift_fst _ _ _
  have e2' : e' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have he : IsIso e := by
    refine ⟨e', pullback.hom_ext ?_ ?_, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, e1', ← Category.assoc, e1, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, e2', e2, Category.id_comp]
    · rw [Category.assoc, e1, ← Category.assoc, e1', Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, e2, e2', Category.id_comp]
  have key : (Sigma.desc (fun j => pullback.lift (σ j ≫ y) (𝟙 W) (by rw [h1 j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s' (c ≫ z)) =
      Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h0 j, Category.id_comp])) ≫ e := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, e1, pullback.lift_fst_assoc]
    · rw [pullback.lift_snd, Category.assoc, e2, pullback.lift_snd]
  rw [key]
  exact IsIso.comp_isIso

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [geomMap, Category.assoc, pullback.lift_fst, galMap_fst, galMap_fst_assoc]`. Simplify using `only [geomMap, Category.assoc, pullback.lift_snd, galMap_snd, galMap_snd_assoc, pullback.lift_snd_assoc]`.
-/
private theorem galMap_geomMap {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p)
    (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ ≫ geomMap Ω p u hu = geomMap Ω p u hu ≫ galMap Ω q σ := by
  apply pullback.hom_ext
  · simp only [geomMap, Category.assoc, pullback.lift_fst, galMap_fst, galMap_fst_assoc]
  · simp only [geomMap, Category.assoc, pullback.lift_snd, galMap_snd, galMap_snd_assoc, pullback.lift_snd_assoc]

/- English proof (translation)
Rewrite using `[← galMap_mul, inv_mul_cancel, galMap_one]`.
-/
private theorem galMap_inv_comp {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ⁻¹ ≫ galMap Ω p σ = 𝟙 _ := by
  rw [← galMap_mul, inv_mul_cancel, galMap_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨galMap Ω p σ⁻¹, by rw [← galMap_mul, mul_inv_cancel, galMap_one], galMap_inv_comp Ω p σ⟩`.
-/
private theorem galMap_isIso {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ : Ω ≃ₐ[k] Ω) : IsIso (galMap Ω p σ) :=
  ⟨galMap Ω p σ⁻¹, by rw [← galMap_mul, mul_inv_cancel, galMap_one], galMap_inv_comp Ω p σ⟩

/- English proof (translation)
Introduce and unpack `l _ k _ H Ω _ _ g T σ ⟨W, c, G, _, _, a, J, _, σj, ⟨hf, he, hsu, h1, hm, hc⟩, hS, hT⟩`. Establish `hz' : IsIso (galMap Ω H.q σ⁻¹)` using `galMap_isIso Ω H.q σ⁻¹`. Establish `hy' : IsIso (galMap Ω (H.s g ≫ H.q) σ⁻¹)` using `galMap_isIso Ω _ σ⁻¹`. Establish `hs : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.sΩ Ω g = H.sΩ Ω g ≫ galMap Ω H.q σ⁻¹` using `galMap_geomMap Ω (H.s g) rfl σ⁻¹`. Establish `ht : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.tΩ Ω g = H.tΩ Ω g ≫ galMap Ω H.q σ⁻¹` using `galMap_geomMap Ω (H.t g) (H.comm g) σ⁻¹`.

Use `⟨W, c ≫ galMap Ω H.q σ⁻¹, G, inferInstance, inferInstance, a, J, inferInstance, fun j => σj j ≫ galMap Ω (H.s g ≫ H.q) σ⁻¹, ⟨inferInstance, inferInstance, inferInstance, h1, hm, ?_⟩, splits_transport _ _ _ hs hS, fun x => ?_⟩` and prove the remaining obligations. Simplify `splits_transport (𝟙 W) (galMap Ω H.q σ⁻¹) (c ≫ galMap Ω H.q σ⁻¹) (Category.id_comp _) hc` using `only [Category.comp_id]`. Establish `hL : ∀ v, GlobalTheory.GalV.pullTot l (sch.map (c ≫ galMap Ω H.q σ⁻¹)) (galTot l Ω H.q σ v) = GlobalTheory.GalV.pullTot l (sch.map c) v` using `fun v => by`. Unfold `galTot`. Rewrite using `[← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc, galMap_inv_comp, Category.comp_id]`.

Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hL, hT]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `galTot`. Rewrite using `[← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc, Category.assoc, ht]`.
-/
theorem UpperTheory.Gal.Int.Geo.opConj_of :
    OpConj := by
  rintro l _ k _ H Ω _ _ g T σ ⟨W, c, G, _, _, a, J, _, σj, ⟨hf, he, hsu, h1, hm, hc⟩, hS, hT⟩
  have hz' : IsIso (galMap Ω H.q σ⁻¹) := galMap_isIso Ω H.q σ⁻¹
  have hy' : IsIso (galMap Ω (H.s g ≫ H.q) σ⁻¹) := galMap_isIso Ω _ σ⁻¹
  have hs : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.sΩ Ω g = H.sΩ Ω g ≫ galMap Ω H.q σ⁻¹ :=
    galMap_geomMap Ω (H.s g) rfl σ⁻¹
  have ht : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.tΩ Ω g = H.tΩ Ω g ≫ galMap Ω H.q σ⁻¹ :=
    galMap_geomMap Ω (H.t g) (H.comm g) σ⁻¹
  refine ⟨W, c ≫ galMap Ω H.q σ⁻¹, G, inferInstance, inferInstance, a, J, inferInstance,
    fun j => σj j ≫ galMap Ω (H.s g ≫ H.q) σ⁻¹, ⟨inferInstance, inferInstance, inferInstance, h1, hm, ?_⟩,
    splits_transport _ _ _ hs hS, fun x => ?_⟩
  · simpa only [Category.comp_id] using
      splits_transport (𝟙 W) (galMap Ω H.q σ⁻¹) (c ≫ galMap Ω H.q σ⁻¹) (Category.id_comp _) hc
  · have hL : ∀ v, GlobalTheory.GalV.pullTot l (sch.map (c ≫ galMap Ω H.q σ⁻¹)) (galTot l Ω H.q σ v) =
        GlobalTheory.GalV.pullTot l (sch.map c) v := fun v => by
      unfold galTot
      rw [← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc,
        galMap_inv_comp, Category.comp_id]
    simp only [LinearMap.comp_apply]
    rw [hL, hT]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold galTot
    rw [← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc, Category.assoc, ht]
