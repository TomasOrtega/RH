import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualNumberThickeningOpenDecompStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.InvFieldBase

section Val

variable {A : Type} [CommRing A] {Y : Scheme.{0}}

/- English proof (translation)
Unfold `valR`. Rewrite using `[dif_pos h]`.
-/
theorem valR_of' (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, V)) :
    valR x V f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE V ⊤ h).hom f) := by
  unfold valR
  rw [dif_pos h]

/- English proof (translation)
Simplify using `only [valR_of' x V h, map_add]`.
-/
theorem valR_add' (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f + g) = valR x V f + valR x V g := by
  simp only [valR_of' x V h, map_add]

/- English proof (translation)
Simplify using `only [valR_of' x V h, map_mul]`.
-/
theorem valR_mul' (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f * g) = valR x V f * valR x V g := by
  simp only [valR_of' x V h, map_mul]

/- English proof (translation)
Establish `h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V` using `h.trans (x.preimage_mono e)`. Rewrite using `[valR_of' x W h, valR_of' (x ≫ g) V h', ← Scheme.Hom.appLE_comp_appLE x g V W ⊤ e h]`. Both sides reduce to the same expression.
-/
theorem valR_appLE' {Z : Scheme.{0}} (x : Sp A ⟶ Z) (g : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ g ⁻¹ᵁ V)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Y, V)) : valR x W ((g.appLE V W e).hom f) = valR (x ≫ g) V f := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V := h.trans (x.preimage_mono e)
  rw [valR_of' x W h, valR_of' (x ≫ g) V h', ← Scheme.Hom.appLE_comp_appLE x g V W ⊤ e h]
  rfl

/- English proof (translation)
Unfold `constFn`. Use `(valR_appLE' x p ⊤ V (fun _ _ => trivial) h _).trans ?_` and prove the remaining obligations. Rewrite using `[hx, valR_of' _ _ le_rfl]`. Establish `n` using `congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))`. Establish `e' : ((spMap ψ).appLE ⊤ ⊤ le_rfl) = (spMap ψ).appTop` using `(Scheme.Hom.app_eq_appLE _).symm`.

Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (ψ a) = (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a) at n`. Rewrite using `[e', ← n]`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _`.
-/
theorem valR_constFn' {B : Type} [CommRing B] (x : Sp A ⟶ Y) (p : Y ⟶ Sp B) (ψ : B →+* A) (hx : x ≫ p = spMap ψ)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : B) : valR x V (constFn p V a) = ψ a := by
  unfold constFn
  refine (valR_appLE' x p ⊤ V (fun _ _ => trivial) h _).trans ?_
  rw [hx, valR_of' _ _ le_rfl]
  have n := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  have e' : ((spMap ψ).appLE ⊤ ⊤ le_rfl) = (spMap ψ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (ψ a) =
    (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a) at n
  rw [e', ← n]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

/- English proof (translation)
Establish `h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ V` using `fun y _ => h (Set.mem_univ ((spMap ψ) y))`. Rewrite using `[valR_of' _ V h', valR_of' x V h]`. Establish `e : (spMap ψ ≫ x).appLE V ⊤ h' = x.appLE V ⊤ h ≫ (spMap ψ).appTop` using `(Scheme.Hom.appLE_comp_appLE (spMap ψ) x V ⊤ ⊤ h le_rfl).symm`. Establish `n` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)`. Express the relevant statement in the definitionally equal form `((spMap ψ ≫ x).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f = (x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f`.

Rewrite using `[e, Category.assoc, n]`.
-/
theorem valR_spMap_comp' {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, V)) : valR (spMap ψ ≫ x) V f = ψ (valR x V f) := by
  have h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ V := fun y _ => h (Set.mem_univ ((spMap ψ) y))
  rw [valR_of' _ V h', valR_of' x V h]
  have e : (spMap ψ ≫ x).appLE V ⊤ h' = x.appLE V ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x V ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

end Val

section Geo

/- English proof (translation)
Establish `hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom` using `fun x => ⟨TrivSqZeroExt.inl x, rfl⟩`. Use `⟨fun P => ?_⟩` and prove the remaining obligations. Establish `: P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom)`. Rewrite using `[range_comap_of_surjective _ _ hs]`. Introduce `x hx`.

Use `(P : PrimeSpectrum (DualNumber R)).2.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Establish `hx' : x.fst = 0` using `hx`. Apply the tactic sequence `have : x ^ 2 = 0 := by ext <;> simp [sq, hx']`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Conclude with `this`.
-/
theorem surjective_spMap_fst' (R : Type) [CommRing R] : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber R)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.
-/
theorem spMap_fst_comp' (R : Type) [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

/- English proof (translation)
Use `f.isIso_app O hO` as an intermediate fact. Conclude with `(ConcreteCategory.bijective_of_isIso (f.app O)).1`.
-/
theorem app_injective' {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsOpenImmersion f] (O : Z.Opens) (hO : O ≤ f.opensRange) :
    Function.Injective (f.app O).hom := by
  have := f.isIso_app O hO
  exact (ConcreteCategory.bijective_of_isIso (f.app O)).1

/- English proof (translation)
Substitute `hg` using the available equality. Both sides reduce to the same expression.
-/
theorem appLE_eq_of_eq' {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (hg : g = g') (V : Y.Opens) (W : Z.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W e = g'.appLE V W e' := by
  subst hg
  rfl

/- English proof (translation)
Rewrite using `[← Scheme.Hom.appLE_comp_appLE k g V W W' e e']`. Both sides reduce to the same expression.
-/
theorem appLE_appLE' {Y Z Q : Scheme.{0}} (g : Z ⟶ Y) (k : Q ⟶ Z) (V : Y.Opens) (W : Z.Opens) (W' : Q.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ k ⁻¹ᵁ W) (f : Γ(Y, V)) :
    (k.appLE W W' e').hom ((g.appLE V W e).hom f) = ((k ≫ g).appLE V W' (e'.trans (k.preimage_mono e))).hom f := by
  rw [← Scheme.Hom.appLE_comp_appLE k g V W W' e e']
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Y.presheaf.map (homOfLE h).op ≫ g.appLE V' W' e').hom f = (g.appLE V W e ≫ Z.presheaf.map (homOfLE h').op).hom f`. Rewrite using `[Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`.
-/
theorem appLE_res' {Y Z : Scheme.{0}} (g : Z ⟶ Y) {V V' : Y.Opens} {W W' : Z.Opens} (h : V' ≤ V) (h' : W' ≤ W)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ g ⁻¹ᵁ V') (f : Γ(Y, V)) :
    (g.appLE V' W' e').hom (resG Y h f) = resG Z h' ((g.appLE V W e).hom f) := by
  change (Y.presheaf.map (homOfLE h).op ≫ g.appLE V' W' e').hom f = (g.appLE V W e ≫ Z.presheaf.map (homOfLE h').op).hom f
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/- English proof (translation)
Unfold `constFn`. Conclude with `appLE_appLE' p k ⊤ W W' _ e' _`.
-/
theorem appLE_constFn' {R : Type} [CommRing R] {Z Q : Scheme.{0}} (p : Z ⟶ Sp R) (k : Q ⟶ Z) (W : Z.Opens)
    (W' : Q.Opens) (e' : W' ≤ k ⁻¹ᵁ W) (a : R) : (k.appLE W W' e').hom (constFn p W a) = constFn (k ≫ p) W' a := by
  unfold constFn
  exact appLE_appLE' p k ⊤ W W' _ e' _

/- English proof (translation)
Establish `h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop`. Rewrite using `[Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]`. Both sides reduce to the same expression. Establish `h2` using `congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))`. Establish `h3` using `congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))`.

Rewrite `h3` using `[h]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3`. Unfold `constFn`. Rewrite using `[← h3, h2]`.
-/
theorem constFn_spMap' {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]

/- English proof (translation)
Simplify using `only [constFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]`.
-/
theorem constFn_eps_sq' {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp (DualNumber R)) (O : Y.Opens) :
    constFn p O DualNumber.eps * constFn p O DualNumber.eps = 0 := by
  simp only [constFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]

/- English proof (translation)
The claim follows from `congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)`.
-/
theorem res_constFn' {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) {V W : Y.Opens} (h : W ≤ V) (a : R) :
    resG Y h (constFn f V a) = constFn f W a :=
  congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(f.app V ≫ Z.presheaf.map (homOfLE h').op).hom a = (Y.presheaf.map (homOfLE h).op ≫ f.app W).hom a`. Rewrite using `[Scheme.Hom.naturality]`. Both sides reduce to the same expression.
-/
theorem res_app' {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V W : Y.Opens} (h : W ≤ V) (h' : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    resG Z h' ((f.app V).hom a) = (f.app W).hom (resG Y h a) := by
  change (f.app V ≫ Z.presheaf.map (homOfLE h').op).hom a = (Y.presheaf.map (homOfLE h).op ≫ f.app W).hom a
  rw [Scheme.Hom.naturality]
  rfl

end Geo

section Group

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)

def transl : tEpsG (𝟙 (Sp R)) ⊗ G ⟶ G :=
  snd _ G * (fst _ G ≫ tv v)

variable (R) in

def redPt : Over.mk (𝟙 (Sp R)) ⟶ tEpsG (𝟙 (Sp R)) :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change _ ≫ spMap _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, spMap_fst_comp'])

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [redPt, Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem redPt_smT : redPt R ≫ Formalism.L2.Pj.homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R))) = redPt R := by
  apply Over.OverMorphism.ext
  simp only [redPt, Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  simp

/- English proof (translation)
Establish `h` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v`. Rewrite using `[← MonObj.comp_one (redPt R), ← h, smT, ← Category.assoc]`. Conclude with `congrArg (fun k => k ≫ tv v) (redPt_smT (R := R)).symm`.
-/
theorem redPt_tv : redPt R ≫ tv v = 1 := by
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v
  rw [← MonObj.comp_one (redPt R), ← h, smT, ← Category.assoc]
  exact congrArg (fun k => k ≫ tv v) (redPt_smT (R := R)).symm

/- English proof (translation)
Unfold `transl`. Rewrite using `[MonObj.comp_mul, ← Category.assoc, whiskerRight_fst, Category.assoc, redPt_tv, whiskerRight_snd, MonObj.comp_one, _root_.mul_one]`.
-/
theorem whisker_transl : redPt R ▷ G ≫ transl G v = redPt R ▷ G ≫ snd _ G := by
  unfold transl
  rw [MonObj.comp_mul, ← Category.assoc, whiskerRight_fst, Category.assoc, redPt_tv, whiskerRight_snd, MonObj.comp_one,
    _root_.mul_one]

end Group

section Group2

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := (snd (tEpsG (𝟙 (Sp R))) G).left) (v₁₃ := G.hom) (h₂₂ := (tEpsG (𝟙 (Sp R))).hom) ?_ ?_ (IsPullback.of_hasPullback (tEpsG (𝟙 (Sp R))).hom G.hom).flip` and prove the remaining obligations. Rewrite using `[← Over.comp_left, whiskerRight_snd, Over.w (redPt R)]`. Conclude with `(IsPullback.of_hasPullback (𝟙 (Sp R)) G.hom).flip`. Rewrite using `[← Over.comp_left, whiskerRight_fst, Over.comp_left]`.
-/
theorem isPullback_red :
    IsPullback (redPt R ▷ G).left (fst (Over.mk (𝟙 (Sp R))) G).left (fst (tEpsG (𝟙 (Sp R))) G).left
      (redPt R).left := by
  refine IsPullback.of_right (h₁₂ := (snd (tEpsG (𝟙 (Sp R))) G).left) (v₁₃ := G.hom)
    (h₂₂ := (tEpsG (𝟙 (Sp R))).hom) ?_ ?_ (IsPullback.of_hasPullback (tEpsG (𝟙 (Sp R))).hom G.hom).flip
  · rw [← Over.comp_left, whiskerRight_snd, Over.w (redPt R)]
    exact (IsPullback.of_hasPullback (𝟙 (Sp R)) G.hom).flip
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

/- English proof (translation)
Rewrite using `[← Over.comp_left, whiskerRight_snd]`.
-/
theorem snd_left_red : (redPt R ▷ G).left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left = (snd (Over.mk (𝟙 (Sp R))) G).left := by
  rw [← Over.comp_left, whiskerRight_snd]

/- English proof (translation)
Rewrite using `[← Over.comp_left, whisker_transl, Over.comp_left, snd_left_red]`.
-/
theorem transl_left_red : (redPt R ▷ G).left ≫ (transl G v).left = (snd (Over.mk (𝟙 (Sp R))) G).left := by
  rw [← Over.comp_left, whisker_transl, Over.comp_left, snd_left_red]

/- English proof (translation)
Establish `hs : Surjective (redPt R ▷ G).left` using `MorphismProperty.of_isPullback (P := @Surjective) (isPullback_red G).flip (surjective_spMap_fst' _)`. Establish `e : (redPt R ▷ G).left ≫ (transl G v).left = (redPt R ▷ G).left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left`. Rewrite using `[transl_left_red, snd_left_red]`. Use extensionality with `x`. Take `⟨y, rfl⟩` from `hs.surj x`.

Express the relevant statement in the definitionally equal form `((redPt R ▷ G).left ≫ (transl G v).left).base y ∈ O ↔ ((redPt R ▷ G).left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left).base y ∈ O`. Rewrite using `[e]`.
-/
theorem preimage_transl (O : G.left.Opens) :
    (transl G v).left ⁻¹ᵁ O = (snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ O := by
  have hs : Surjective (redPt R ▷ G).left :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_red G).flip (surjective_spMap_fst' _)
  have e : (redPt R ▷ G).left ≫ (transl G v).left = (redPt R ▷ G).left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left := by
    rw [transl_left_red, snd_left_red]
  ext x
  obtain ⟨y, rfl⟩ := hs.surj x
  change ((redPt R ▷ G).left ≫ (transl G v).left).base y ∈ O ↔
    ((redPt R ▷ G).left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left).base y ∈ O
  rw [e]

/- English proof (translation)
Establish `hP₀ : IsPullback (snd (Over.mk (𝟙 (Sp R))) G).left (fst (Over.mk (𝟙 (Sp R))) G).left G.hom (𝟙 (Sp R))` using `(IsPullback.of_hasPullback (𝟙 (Sp R)) G.hom).flip`. Establish `: IsOpenImmersion (snd (Over.mk (𝟙 (Sp R))) G).left` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP₀.flip (show IsOpenImmersion (𝟙 (Sp R)) from inferInstance)`. Establish `hrange : O ≤ (snd (Over.mk (𝟙 (Sp R))) G).left.opensRange` using `fun x _ => by`. Take `⟨z, hz, -⟩` from `Scheme.exists_preimage_of_isPullback hP₀ x (G.hom.base x) rfl`. Conclude with `⟨z, hz⟩`.

Establish `hjO : (snd (Over.mk (𝟙 (Sp R))) G).left ⁻¹ᵁ O ≤ (redPt R ▷ G).left ⁻¹ᵁ ((snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ O)`. Rewrite using `[← Scheme.Hom.comp_preimage, snd_left_red]`. Establish `ef : (redPt R ▷ G).left ≫ (fst (tEpsG (𝟙 (Sp R))) G).left = (fst (Over.mk (𝟙 (Sp R))) G).left ≫ (redPt R).left`. Rewrite using `[← Over.comp_left, whiskerRight_fst, Over.comp_left]`. Establish `k` using `congrArg ((redPt R ▷ G).left.appLE _ _ hjO).hom h`.

Simplify using `only [map_add, map_mul, Scheme.Hom.app_eq_appLE, appLE_appLE', appLE_constFn'] at k`. Rewrite `k` using `[appLE_eq_of_eq' (transl_left_red G v) _ _ _ le_rfl, appLE_eq_of_eq' (snd_left_red G) _ _ _ le_rfl, ef]`. Establish `hr : (redPt R).left = spMap (TrivSqZeroExt.fstHom R R R).toRingHom` using `rfl`. Establish `h0 : (TrivSqZeroExt.fstHom R R R).toRingHom DualNumber.eps = 0` using `by simp`. Rewrite `k` using `[hr, constFn_spMap', h0]`.

Simplify using `only [constFn, map_zero, zero_mul, add_zero] at k`. Rewrite `k` using `[← Scheme.Hom.app_eq_appLE]`. Conclude with `(app_injective' _ O hrange k).symm`.
-/
theorem real_part (O : G.left.Opens) (f a b : Γ(G.left, O))
    (h : ((transl G v).left.appLE O _ (preimage_transl G v O).ge).hom f =
      ((snd (tEpsG (𝟙 (Sp R))) G).left.app O).hom a + constFn (fst (tEpsG (𝟙 (Sp R))) G).left _ DualNumber.eps *
        ((snd (tEpsG (𝟙 (Sp R))) G).left.app O).hom b) : a = f := by
  have hP₀ : IsPullback (snd (Over.mk (𝟙 (Sp R))) G).left (fst (Over.mk (𝟙 (Sp R))) G).left G.hom (𝟙 (Sp R)) :=
    (IsPullback.of_hasPullback (𝟙 (Sp R)) G.hom).flip
  have : IsOpenImmersion (snd (Over.mk (𝟙 (Sp R))) G).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP₀.flip
      (show IsOpenImmersion (𝟙 (Sp R)) from inferInstance)
  have hrange : O ≤ (snd (Over.mk (𝟙 (Sp R))) G).left.opensRange := fun x _ => by
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hP₀ x (G.hom.base x) rfl
    exact ⟨z, hz⟩
  have hjO : (snd (Over.mk (𝟙 (Sp R))) G).left ⁻¹ᵁ O ≤
      (redPt R ▷ G).left ⁻¹ᵁ ((snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ O) := by
    rw [← Scheme.Hom.comp_preimage, snd_left_red]
  have ef : (redPt R ▷ G).left ≫ (fst (tEpsG (𝟙 (Sp R))) G).left =
      (fst (Over.mk (𝟙 (Sp R))) G).left ≫ (redPt R).left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have k := congrArg ((redPt R ▷ G).left.appLE _ _ hjO).hom h
  simp only [map_add, map_mul, Scheme.Hom.app_eq_appLE, appLE_appLE', appLE_constFn'] at k
  rw [appLE_eq_of_eq' (transl_left_red G v) _ _ _ le_rfl, appLE_eq_of_eq' (snd_left_red G) _ _ _ le_rfl, ef] at k
  have hr : (redPt R).left = spMap (TrivSqZeroExt.fstHom R R R).toRingHom := rfl
  have h0 : (TrivSqZeroExt.fstHom R R R).toRingHom DualNumber.eps = 0 := by simp
  rw [hr, constFn_spMap', h0] at k
  simp only [constFn, map_zero, zero_mul, add_zero] at k
  rw [← Scheme.Hom.app_eq_appLE] at k
  exact (app_injective' _ O hrange k).symm

/- English proof (translation)
The claim follows from `IsPullback.of_iso (IsPullback.of_hasPullback (tEpsG (𝟙 (Sp R))).hom G.hom).flip (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)`.
-/
theorem isPullback_thick :
    IsPullback (snd (tEpsG (𝟙 (Sp R))) G).left (fst (tEpsG (𝟙 (Sp R))) G).left G.hom
      (spMap (algebraMap R (DualNumber R))) :=
  IsPullback.of_iso (IsPullback.of_hasPullback (tEpsG (𝟙 (Sp R))).hom G.hom).flip (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

end Group2

/- English proof (translation)
Introduce `R _ G _ _ v`. Establish `hd` using `fun (O : G.left.Opens) (f : Γ(G.left, O)) => GlobalTheory.T.existsUnique_dualNumberThickening_open_decomp R G.hom _ _ (isPullback_thick G) O (((transl G v).left.appLE O _ (preimage_transl G v O).ge).hom f)`. Use `choose ab hab huq using hd`. Establish `huniq : ∀ O f (a b : Γ(G.left, O)), ((transl G v).left.appLE O _ (preimage_transl G v O).ge).hom f = ((snd (tEpsG (𝟙 (Sp R))) G).left.app O).hom a + constFn (fst (tEpsG (𝟙 (Sp R))) G).left _ DualNumber.eps * ((snd (tEpsG (𝟙 (Sp R))) G).left.app O).hom b → (ab O f).2 = b` using `fun O f a b h => congrArg Prod.snd (huq O f (a, b) h).symm`. Establish `hre : ∀ O f, (ab O f).1 = f` using `fun O f => real_part G v O f _ _ (hab O f)`.

Establish `hee` using `fun O : G.left.Opens => constFn_eps_sq' (fst (tEpsG (𝟙 (Sp R))) G).left ((snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ O)`. Use `⟨fun O f => (ab O f).2, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `W _ f f'`. Use `huniq W _ (f + f') _ ?_` and prove the remaining obligations. Rewrite using `[map_add, hab W f, hab W f', hre, hre]`.

Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree. Introduce `W _ f f'`. Use `huniq W _ (f * f') _ ?_` and prove the remaining obligations. Rewrite using `[map_mul, hab W f, hab W f', hre, hre]`.

Simplify using `only [map_add, map_mul]`. Take the linear combination `(((snd (tEpsG (𝟙 (Sp R))) G).left.app W).hom (ab W f).2 * ((snd (tEpsG (𝟙 (Sp R))) G).left.app W).hom (ab W f').2) * hee W`. Introduce `W W' h _ f`. Use `huniq W' _ (resG _ h f) _ ?_` and prove the remaining obligations. Establish `h' : (snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ W' ≤ (snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ W` using `(snd (tEpsG (𝟙 (Sp R))) G).left.preimage_mono h`.

Rewrite using `[appLE_res' _ h h' (preimage_transl G v W).ge, hab W f, hre, map_add, map_mul, res_app' _ h h', res_app' _ h h', res_constFn']`. Introduce `S _ φ g w O f hg hgO htr`. Use `symm`. Take `⟨g', v', hg', hv', rfl⟩` from `htr`. Establish `e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ`.

Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Set `kA : tEpsG (g ≫ G.hom) ⟶ tEpsG (𝟙 (Sp R))` to `Over.homMk (spMap (dualMap φ)) (by`. Express the relevant statement in the definitionally equal form `spMap (dualMap φ) ≫ spMap (algebraMap _ _) ≫ 𝟙 _ = spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom`. Rewrite using `[hg, Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e])`. Establish `hk : lift kA g' ≫ transl G v = g' * v'`.

Unfold `transl`. Rewrite using `[MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]`. Use `congr 1`. Conclude with `Over.OverMorphism.ext hv'.symm`. Establish `hk2 : (lift kA g').left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left = spMap (algebraMap S (DualNumber S)) ≫ g`.

Rewrite using `[← Over.comp_left, lift_snd, hg']`. Establish `hk1 : (lift kA g').left ≫ (fst (tEpsG (𝟙 (Sp R))) G).left = spMap (dualMap φ)`. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression. Establish `hT : (g' * v').left = (lift kA g').left ≫ (transl G v).left` using `by rw [← hk, Over.comp_left]`.

Establish `hx : ⊤ ≤ (lift kA g').left ⁻¹ᵁ ((snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ O)`. Introduce `y _`. Use `show ((lift kA g').left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left).base y ∈ O`. Rewrite using `[hk2]`. Conclude with `hgO (Set.mem_univ _)`.

Rewrite using `[hT, ← valR_appLE' _ _ O _ (preimage_transl G v O).ge hx, hab O f, hre, valR_add' _ _ hx, valR_mul' _ _ hx, valR_constFn' _ _ _ hk1 _ hx, Scheme.Hom.app_eq_appLE, valR_appLE' _ _ _ _ _ hx, valR_appLE' _ _ _ _ _ hx, hk2, valR_spMap_comp' _ _ _ hgO, valR_spMap_comp' _ _ _ hgO]`. Simplify using `[dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem exists_isInv : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G), ∃ dd : Fld G.left, IsInv G v dd := by
  intro R _ G _ _ v
  have hd := fun (O : G.left.Opens) (f : Γ(G.left, O)) =>
    GlobalTheory.T.existsUnique_dualNumberThickening_open_decomp R G.hom _ _ (isPullback_thick G) O
      (((transl G v).left.appLE O _ (preimage_transl G v O).ge).hom f)
  choose ab hab huq using hd
  have huniq : ∀ O f (a b : Γ(G.left, O)),
      ((transl G v).left.appLE O _ (preimage_transl G v O).ge).hom f =
        ((snd (tEpsG (𝟙 (Sp R))) G).left.app O).hom a + constFn (fst (tEpsG (𝟙 (Sp R))) G).left _ DualNumber.eps *
          ((snd (tEpsG (𝟙 (Sp R))) G).left.app O).hom b → (ab O f).2 = b :=
    fun O f a b h => congrArg Prod.snd (huq O f (a, b) h).symm
  have hre : ∀ O f, (ab O f).1 = f := fun O f => real_part G v O f _ _ (hab O f)
  have hee := fun O : G.left.Opens => constFn_eps_sq' (fst (tEpsG (𝟙 (Sp R))) G).left
    ((snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ O)
  refine ⟨fun O f => (ab O f).2, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W _ f f'
    refine huniq W _ (f + f') _ ?_
    rw [map_add, hab W f, hab W f', hre, hre]
    simp only [map_add]
    ring
  · intro W _ f f'
    refine huniq W _ (f * f') _ ?_
    rw [map_mul, hab W f, hab W f', hre, hre]
    simp only [map_add, map_mul]
    linear_combination (((snd (tEpsG (𝟙 (Sp R))) G).left.app W).hom (ab W f).2 *
      ((snd (tEpsG (𝟙 (Sp R))) G).left.app W).hom (ab W f').2) * hee W
  · intro W W' h _ f
    refine huniq W' _ (resG _ h f) _ ?_
    have h' : (snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ W' ≤ (snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ W :=
      (snd (tEpsG (𝟙 (Sp R))) G).left.preimage_mono h
    rw [appLE_res' _ h h' (preimage_transl G v W).ge, hab W f, hre, map_add, map_mul, res_app' _ h h',
      res_app' _ h h', res_constFn']
  · intro S _ φ g w O f hg hgO htr
    symm
    obtain ⟨g', v', hg', hv', rfl⟩ := htr
    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let kA : tEpsG (g ≫ G.hom) ⟶ tEpsG (𝟙 (Sp R)) := Over.homMk (spMap (dualMap φ)) (by
      change spMap (dualMap φ) ≫ spMap (algebraMap _ _) ≫ 𝟙 _ = spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom
      rw [hg, Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, e])
    have hk : lift kA g' ≫ transl G v = g' * v' := by
      unfold transl
      rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
      congr 1
      exact Over.OverMorphism.ext hv'.symm
    have hk2 : (lift kA g').left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left = spMap (algebraMap S (DualNumber S)) ≫ g := by
      rw [← Over.comp_left, lift_snd, hg']
    have hk1 : (lift kA g').left ≫ (fst (tEpsG (𝟙 (Sp R))) G).left = spMap (dualMap φ) := by
      rw [← Over.comp_left, lift_fst]
      rfl
    have hT : (g' * v').left = (lift kA g').left ≫ (transl G v).left := by rw [← hk, Over.comp_left]
    have hx : ⊤ ≤ (lift kA g').left ⁻¹ᵁ ((snd (tEpsG (𝟙 (Sp R))) G).left ⁻¹ᵁ O) := by
      intro y _
      show ((lift kA g').left ≫ (snd (tEpsG (𝟙 (Sp R))) G).left).base y ∈ O
      rw [hk2]
      exact hgO (Set.mem_univ _)
    rw [hT, ← valR_appLE' _ _ O _ (preimage_transl G v O).ge hx, hab O f, hre, valR_add' _ _ hx, valR_mul' _ _ hx,
      valR_constFn' _ _ _ hk1 _ hx, Scheme.Hom.app_eq_appLE, valR_appLE' _ _ _ _ _ hx, valR_appLE' _ _ _ _ _ hx, hk2,
      valR_spMap_comp' _ _ _ hgO, valR_spMap_comp' _ _ _ hgO]
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.InvFieldBase
