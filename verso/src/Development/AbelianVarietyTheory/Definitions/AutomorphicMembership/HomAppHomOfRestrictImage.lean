import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG Sp spMap)
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply structureModule)
open GlobalTheory.VB
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.PtNorm

variable {X : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens} {ι : Type} [Fintype ι]

def homEval (G : X.Modules) (s : Γ(F, V)) : Γ(homMod F G, V) →ₗ[Γ(X, V)] Γ(G, V) where
  toFun ψ := homApp ψ le_rfl s
  map_add' _ _ := rfl
  map_smul' a ψ := by rw [homApp_smul, resG_self]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem homEval_apply (s : Γ(F, V)) (ψ : Γ(homMod F G, V)) : homEval G s ψ = homApp ψ le_rfl s := rfl

def homIns {e : ι → Γ(F, U)} (he : IsFrame e) (h : V ≤ U) (i : ι) : Γ(G, V) →ₗ[Γ(X, V)] Γ(homMod F G, V) where
  toFun n := homMk (fun _ hW => ((he.basis (hW.trans h)).coord i).smulRight (resM G hW n)) fun W W' hW h' s => by
    simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply, resM_smul, resM_resM]
    rw [← he.repr_resM]
  map_add' a b := VB.hom_ext fun W hW s => by
    simp only [homApp_homMk, homApp_add, LinearMap.add_apply, LinearMap.smulRight_apply, map_add, smul_add]
  map_smul' a b := VB.hom_ext fun W hW s => by
    simp only [homApp_homMk, homApp_smul, LinearMap.smul_apply, LinearMap.smulRight_apply, resM_smul, RingHom.id_apply]
    rw [smul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homApp_homIns {e : ι → Γ(F, U)} (he : IsFrame e) (h : V ≤ U) (i : ι) (n : Γ(G, V)) (hW : W ≤ V) (s : Γ(F, W)) :
    homApp (homIns he h i n) hW s = (he.basis (hW.trans h)).repr s i • resM G hW n := rfl

/- English proof (translation)
Use `VB.hom_ext fun W hW s => ?_` and prove the remaining obligations. Rewrite using `[homApp_sum, LinearMap.sum_apply]`. Use `conv_rhs => rw [← (he.basis (hW.trans h)).sum_repr s, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[homApp_homIns, map_smul, ← homApp_resM, resM_resM, IsFrame.basis_apply]`.
-/
theorem sum_homIns {e : ι → Γ(F, U)} (he : IsFrame e) (h : V ≤ U) (ψ : Γ(homMod F G, V)) :
    ∑ i, homIns he h i (homApp ψ le_rfl (resM F h (e i))) = ψ := by
  refine VB.hom_ext fun W hW s => ?_
  rw [homApp_sum, LinearMap.sum_apply]
  conv_rhs => rw [← (he.basis (hW.trans h)).sum_repr s, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [homApp_homIns, map_smul, ← homApp_resM, resM_resM, IsFrame.basis_apply]

def homPi {e : ι → Γ(F, U)} (he : IsFrame e) (h : V ≤ U) : Γ(homMod F G, V) ≃ₗ[Γ(X, V)] (ι → Γ(G, V)) :=
  LinearEquiv.ofLinear (LinearMap.pi fun i => homEval G (resM F h (e i)))
    (∑ i, homIns he h i ∘ₗ LinearMap.proj i)
    (by
      classical
      refine LinearMap.ext fun n => funext fun j => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.pi_apply, map_sum, homEval_apply,
        LinearMap.proj_apply, LinearMap.id_apply, homApp_homIns, resM_self, Finset.sum_apply]
      simp only [← he.basis_apply, Module.Basis.repr_self]
      simp [Finsupp.single_apply])
    (LinearMap.ext fun ψ => by
      simpa using sum_homIns he h ψ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homPi_apply {e : ι → Γ(F, U)} (he : IsFrame e) (h : V ≤ U) (ψ : Γ(homMod F G, V)) (i : ι) :
    homPi he h ψ i = homApp ψ le_rfl (resM F h (e i)) := rfl

/- English proof (translation)
Rewrite using `[homPi_apply, homPi_apply, homApp_res, ← homApp_resM, resM_resM]`.
-/
theorem homPi_res {e : ι → Γ(F, U)} (he : IsFrame e) (h : V ≤ U) (h' : W ≤ V) (ψ : Γ(homMod F G, V)) (i : ι) :
    homPi he (h'.trans h) (resM _ h' ψ) i = resM G h' (homPi he h ψ i) := by
  rw [homPi_apply, homPi_apply, homApp_res, ← homApp_resM, resM_resM]

/- English proof (translation)
Establish `: (homMod F G).IsQuasicoherent`. Use `QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_` and prove the remaining obligations. Take `⟨U, e, hU, hx, -, he⟩` from `hF.exists_affine (V := ⊤) (x := x) trivial`. Use `⟨U, hU, hx, fun f => (QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩⟩` and prove the remaining obligations. Use `choose n t ht using fun i => QCoh.exists_pow_smul_eq_res G hU f (X.basicOpen_le f) rfl (homPi he (X.basicOpen_le f) s i)`.

Use `⟨∑ i, n i, (homPi he le_rfl).symm fun i => f ^ (∑ i, n i - n i) • t i, (homPi he (X.basicOpen_le f)).injective (funext fun i => ?_)⟩` and prove the remaining obligations. Establish `hi : n i ≤ ∑ i, n i` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Use `Eq.trans ?_ (homPi_res he le_rfl (X.basicOpen_le f) _ i).symm` and prove the remaining obligations. Rewrite using `[LinearEquiv.apply_symm_apply, resM_smul, map_smul, Pi.smul_apply, map_pow]`. Use `Eq.trans ?_ (congrArg _ (ht i))` and prove the remaining obligations.

Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel hi]`. Use `choose n hn using fun i => QCoh.exists_pow_smul_eq_zero G hU f (X.basicOpen_le f) rfl (homPi he le_rfl t i) ((homPi_res he le_rfl (X.basicOpen_le f) t i).symm.trans (by`. Rewrite using `[show resM _ (X.basicOpen_le f) t = 0 from ht, map_zero]`. Use the proof step `rfl))`. Use `⟨∑ i, n i, (homPi he le_rfl).injective (funext fun i => ?_)⟩` and prove the remaining obligations.

Establish `hi : n i ≤ ∑ i, n i` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Rewrite using `[map_smul, Pi.smul_apply, ← Nat.sub_add_cancel hi, pow_add, mul_smul, hn, smul_zero, map_zero]`. Both sides reduce to the same expression. Use `.of_forall_exists_affine fun x => ?_` and prove the remaining obligations. Take `⟨U, e, hU, hx, -, he⟩` from `hF.exists_affine (V := ⊤) (x := x) trivial`.

Use `QCoh.finite_sections G hU` as an intermediate fact. Conclude with `⟨U, hU, hx, Module.Finite.equiv (homPi he le_rfl).symm⟩`.
-/
theorem isFiniteQC_homMod {r : ℕ} (hF : IsVB F r) [IsFiniteQC G] : IsFiniteQC (homMod F G) := by
  have : (homMod F G).IsQuasicoherent := by
    refine QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
    obtain ⟨U, e, hU, hx, -, he⟩ := hF.exists_affine (V := ⊤) (x := x) trivial
    refine ⟨U, hU, hx, fun f => (QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩⟩
    · choose n t ht using fun i =>
        QCoh.exists_pow_smul_eq_res G hU f (X.basicOpen_le f) rfl (homPi he (X.basicOpen_le f) s i)
      refine ⟨∑ i, n i, (homPi he le_rfl).symm fun i => f ^ (∑ i, n i - n i) • t i,
        (homPi he (X.basicOpen_le f)).injective (funext fun i => ?_)⟩
      have hi : n i ≤ ∑ i, n i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      refine Eq.trans ?_ (homPi_res he le_rfl (X.basicOpen_le f) _ i).symm
      rw [LinearEquiv.apply_symm_apply, resM_smul, map_smul, Pi.smul_apply, map_pow]
      refine Eq.trans ?_ (congrArg _ (ht i))
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hi]
    · choose n hn using fun i =>
        QCoh.exists_pow_smul_eq_zero G hU f (X.basicOpen_le f) rfl (homPi he le_rfl t i)
          ((homPi_res he le_rfl (X.basicOpen_le f) t i).symm.trans (by
            rw [show resM _ (X.basicOpen_le f) t = 0 from ht, map_zero]; rfl))
      refine ⟨∑ i, n i, (homPi he le_rfl).injective (funext fun i => ?_)⟩
      have hi : n i ≤ ∑ i, n i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [map_smul, Pi.smul_apply, ← Nat.sub_add_cancel hi, pow_add, mul_smul, hn, smul_zero, map_zero]
      rfl
  refine .of_forall_exists_affine fun x => ?_
  obtain ⟨U, e, hU, hx, -, he⟩ := hF.exists_affine (V := ⊤) (x := x) trivial
  have := QCoh.finite_sections G hU
  exact ⟨U, hU, hx, Module.Finite.equiv (homPi he le_rfl).symm⟩

/- English proof (translation)
Introduce `x` and use `by obtain ⟨U, e, hx, he⟩ := hF x obtain ⟨V, e', -, hx', hle, he'⟩ := hG.exists_affine hx refine ⟨V, fun j => (homPi he hle).symm fun _ => e' j, hx', he'.map_of_linearEquiv (fun T hT => (LinearEquiv.funUnique (Fin 1) _ _).symm ≪≫ₗ (homPi he (hT.trans hle)).symm) fun T hT j => ?_⟩ …`.
-/
theorem isVB_homMod {r : ℕ} (hF : IsVB F 1) (hG : IsVB G r) : IsVB (homMod F G) r := fun x => by
  obtain ⟨U, e, hx, he⟩ := hF x
  obtain ⟨V, e', -, hx', hle, he'⟩ := hG.exists_affine hx
  refine ⟨V, fun j => (homPi he hle).symm fun _ => e' j, hx', he'.map_of_linearEquiv
    (fun T hT => (LinearEquiv.funUnique (Fin 1) _ _).symm ≪≫ₗ (homPi he (hT.trans hle)).symm) fun T hT j => ?_⟩
  refine (homPi he (hT.trans hle)).injective (funext fun i => ?_)
  rw [homPi_res he hle hT, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/- English proof (translation)
Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]`. Conclude with `inf_eq_right.2 h`.
-/
theorem image_preimage_ι (h : W ≤ U) : U.ι ''ᵁ U.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 h

def appIm (φ : F.restrict U.ι ⟶ G.restrict U.ι) (T : U.toScheme.Opens) :
    Γ(F, U.ι ''ᵁ T) →ₗ[Γ(X, U.ι ''ᵁ T)] Γ(G, U.ι ''ᵁ T) where
  toFun s := φ.app T s
  map_add' a b := map_add (ConcreteCategory.hom (φ.app T)) a b
  map_smul' a s := by
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (U.ι.appIso T).inv).2 a
    exact φ.app_smul b s

/- English proof (translation)
The claim follows from `app_resM φ h s`.
-/
theorem appIm_res (φ : F.restrict U.ι ⟶ G.restrict U.ι) {T T' : U.toScheme.Opens} (h : T' ≤ T) (s : Γ(F, U.ι ''ᵁ T)) :
    appIm φ T' (resM F (U.ι.image_mono h) s) = resM G (U.ι.image_mono h) (appIm φ T s) :=
  app_resM φ h s

def homOfRestrict (φ : F.restrict U.ι ⟶ G.restrict U.ι) : Γ(homMod F G, U) :=
  homMk (fun W h =>
    { toFun s := resM G (image_preimage_ι h).ge (appIm φ (U.ι ⁻¹ᵁ W) (resM F (image_preimage_ι h).le s))
      map_add' a b := by rw [map_add, map_add, map_add]
      map_smul' a s := by
        rw [resM_smul, map_smul, resM_smul, resG_resG, resG_self, RingHom.id_apply] })
    fun W W' h h' s => by
      have := appIm_res φ (U.ι.preimage_mono h') (resM F (image_preimage_ι h).le s)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, resM_resM] at this ⊢
      rw [this, resM_resM]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homApp_homOfRestrict (φ : F.restrict U.ι ⟶ G.restrict U.ι) (h : W ≤ U) (s : Γ(F, W)) :
    homApp (homOfRestrict φ) h s =
      resM G (image_preimage_ι h).ge (appIm φ (U.ι ⁻¹ᵁ W) (resM F (image_preimage_ι h).le s)) := rfl

/- English proof (translation)
Establish `hT : U.ι ⁻¹ᵁ U.ι ''ᵁ T ≤ T` using `(U.ι.preimage_image_eq T).le`. Rewrite using `[homApp_homOfRestrict, appIm_res φ hT, resM_resM, resM_self]`.
-/
theorem homApp_homOfRestrict_image (φ : F.restrict U.ι ⟶ G.restrict U.ι) (T : U.toScheme.Opens)
    (h : U.ι ''ᵁ T ≤ U) (s : Γ(F, U.ι ''ᵁ T)) : homApp (homOfRestrict φ) h s = appIm φ T s := by
  have hT : U.ι ⁻¹ᵁ U.ι ''ᵁ T ≤ T := (U.ι.preimage_image_eq T).le
  rw [homApp_homOfRestrict, appIm_res φ hT, resM_resM, resM_self]

/- English proof (translation)
Simplify using `only [homApp_homOfRestrict, resM_resM, resM_self]`. Both sides reduce to the same expression.
-/
theorem homOfRestrict_comp (φ : F.restrict U.ι ⟶ G.restrict U.ι) (ψ : G.restrict U.ι ⟶ H.restrict U.ι)
    (h : W ≤ U) (s : Γ(F, W)) :
    homApp (homOfRestrict ψ) h (homApp (homOfRestrict φ) h s) = homApp (homOfRestrict (φ ≫ ψ)) h s := by
  simp only [homApp_homOfRestrict, resM_resM, resM_self]
  rfl

/- English proof (translation)
Establish `(T : U.toScheme.Opens) (t : Γ(F, U.ι ''ᵁ T)) : appIm (𝟙 (F.restrict U.ι)) T t = t` using `rfl`. Rewrite using `[homApp_homOfRestrict, this, resM_resM, resM_self]`.
-/
theorem homOfRestrict_id (h : W ≤ U) (s : Γ(F, W)) : homApp (homOfRestrict (𝟙 (F.restrict U.ι))) h s = s := by
  have (T : U.toScheme.Opens) (t : Γ(F, U.ι ''ᵁ T)) : appIm (𝟙 (F.restrict U.ι)) T t = t := rfl
  rw [homApp_homOfRestrict, this, resM_resM, resM_self]

def equivOfRestrict (φ : F.restrict U.ι ≅ G.restrict U.ι) (h : W ≤ U) : Γ(F, W) ≃ₗ[Γ(X, W)] Γ(G, W) :=
  LinearEquiv.ofLinear (homApp (homOfRestrict φ.hom) h) (homApp (homOfRestrict φ.inv) h)
    (LinearMap.ext fun s => by
      rw [LinearMap.comp_apply, homOfRestrict_comp, φ.inv_hom_id, homOfRestrict_id]; rfl)
    (LinearMap.ext fun s => by
      rw [LinearMap.comp_apply, homOfRestrict_comp, φ.hom_inv_id, homOfRestrict_id]; rfl)

section Value

variable {R R' : Type} [CommRing R] [CommRing R']

def evz (z : Sp R ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (z.appLE U ⊤ h).hom

/- English proof (translation)
The claim follows from `congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (ConcreteCategory.congr_hom (z.map_appLE h (homOfLE hle).op) a)`.
-/
theorem evz_res (z : Sp R ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ z ⁻¹ᵁ U) (hle : V ≤ U) (a : Γ(X, U)) :
    evz z h (resG X hle a) = evz z h' a :=
  congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (ConcreteCategory.congr_hom (z.map_appLE h (homOfLE hle).op) a)

/- English proof (translation)
Establish `e₁ : (spMap ψ ≫ z).appLE U ⊤ h' = z.appLE U ⊤ h ≫ (spMap ψ).appTop`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Conclude with `(Scheme.Hom.appLE_comp_appLE (spMap ψ) z U ⊤ ⊤ h le_top).symm`. Establish `e₂` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)`. Express the relevant statement in the definitionally equal form `((spMap ψ ≫ z).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso _).hom) a = _`.

Rewrite using `[e₁, Category.assoc, e₂]`. Both sides reduce to the same expression.
-/
theorem evz_comp (ψ : R →+* R') (z : Sp R ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap ψ ≫ z) ⁻¹ᵁ U) (a : Γ(X, U)) :
    evz (spMap ψ ≫ z) h' a = ψ (evz z h a) := by
  have e₁ : (spMap ψ ≫ z).appLE U ⊤ h' = z.appLE U ⊤ h ≫ (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap ψ) z U ⊤ ⊤ h le_top).symm
  have e₂ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ z).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso _).hom) a = _
  rw [e₁, Category.assoc, e₂]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h (Set.mem_univ _), fun h => ((IsLocalRing.closedPoint_mem_iff (z ⁻¹ᵁ U)).1 h).ge⟩`.
-/
theorem top_le_preimage_iff [IsLocalRing R] (z : Sp R ⟶ X) :
    ⊤ ≤ z ⁻¹ᵁ U ↔ z (IsLocalRing.closedPoint R) ∈ U :=
  ⟨fun h => h (Set.mem_univ _), fun h => ((IsLocalRing.closedPoint_mem_iff (z ⁻¹ᵁ U)).1 h).ge⟩

def resForm (h : V ≤ U) {ε : Γ(X, V) →+* R} {ε' : Γ(X, U) →+* R} (hε : ∀ a, ε (resG X h a) = ε' a)
    (μ : Γ(F, V) →ₛₗ[ε] R) : Γ(F, U) →ₛₗ[ε'] R where
  toFun s := μ (resM F h s)
  map_add' a b := by rw [map_add, map_add]
  map_smul' a s := by rw [resM_smul, μ.map_smulₛₗ, hε]

/- English proof (translation)
Use `letI := QCoh.resAlgebra h`. Use `letI := QCoh.resModule F h`. Use `haveI := QCoh.res_isScalarTower F h`. Use `letI : Module Γ(X, V) R := Module.compHom R ε`. Use `letI : Module Γ(X, U) R := Module.compHom R ε'`.

Use `haveI : IsScalarTower Γ(X, U) Γ(X, V) R := .of_algebraMap_smul fun a x => congrArg (· * x) (hε a)`. Set `l' : Γ(F, U) →ₗ[Γ(X, U)] R` to `⟨⟨l, l.map_add⟩, l.map_smulₛₗ⟩`. Set `μ` to `(QCoh.isBaseChange_resLinear F hU hV h).lift l'`. Conclude with `⟨⟨⟨μ, μ.map_add⟩, μ.map_smul⟩, fun s => (QCoh.isBaseChange_resLinear F hU hV h).lift_eq l' s⟩`.
-/
theorem exists_extend [F.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {ε : Γ(X, V) →+* R} {ε' : Γ(X, U) →+* R} (hε : ∀ a, ε (resG X h a) = ε' a) (l : Γ(F, U) →ₛₗ[ε'] R) :
    ∃ μ : Γ(F, V) →ₛₗ[ε] R, ∀ s, μ (resM F h s) = l s := by
  letI := QCoh.resAlgebra h
  letI := QCoh.resModule F h
  haveI := QCoh.res_isScalarTower F h
  letI : Module Γ(X, V) R := Module.compHom R ε
  letI : Module Γ(X, U) R := Module.compHom R ε'
  haveI : IsScalarTower Γ(X, U) Γ(X, V) R := .of_algebraMap_smul fun a x => congrArg (· * x) (hε a)
  let l' : Γ(F, U) →ₗ[Γ(X, U)] R := ⟨⟨l, l.map_add⟩, l.map_smulₛₗ⟩
  let μ := (QCoh.isBaseChange_resLinear F hU hV h).lift l'
  exact ⟨⟨⟨μ, μ.map_add⟩, μ.map_smul⟩, fun s => (QCoh.isBaseChange_resLinear F hU hV h).lift_eq l' s⟩

/- English proof (translation)
Use `letI := QCoh.resAlgebra h`. Use `letI := QCoh.resModule F h`. Use `haveI := QCoh.res_isScalarTower F h`. Use `LinearMap.ext fun t => (QCoh.isBaseChange_resLinear F hU hV h).inductionOn t (fun t => μ t = μ' t) (by simp) H (fun a t ht => ?_) fun a b ha hb => ?_` and prove the remaining obligations. Rewrite using `[μ.map_smulₛₗ, μ'.map_smulₛₗ, ht]`.

Rewrite using `[map_add, map_add, ha, hb]`.
-/
theorem form_ext [F.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {ε : Γ(X, V) →+* R} {μ μ' : Γ(F, V) →ₛₗ[ε] R} (H : ∀ s, μ (resM F h s) = μ' (resM F h s)) : μ = μ' := by
  letI := QCoh.resAlgebra h
  letI := QCoh.resModule F h
  haveI := QCoh.res_isScalarTower F h
  refine LinearMap.ext fun t => (QCoh.isBaseChange_resLinear F hU hV h).inductionOn t
    (fun t => μ t = μ' t) (by simp) H (fun a t ht => ?_) fun a b ha hb => ?_
  · rw [μ.map_smulₛₗ, μ'.map_smulₛₗ, ht]
  · rw [map_add, map_add, ha, hb]

def IsLineForm {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {ε : A →+* R} (μ₀ : M →ₛₗ[ε] R) : Prop :=
  μ₀ ≠ 0 ∧ ∀ μ : M →ₛₗ[ε] R, ∃ c : R, μ = c • μ₀

/- English proof (translation)
Use `⟨fun e => h.1 (LinearMap.ext fun m => ?_), fun μ => ?_⟩` and prove the remaining obligations. Simplify using `using LinearMap.congr_fun e (φ.symm m)`. Take `⟨c, hc⟩` from `h.2 (μ.comp φ.symm.toLinearMap)`. Conclude with `⟨c, LinearMap.ext fun n => by simpa using LinearMap.congr_fun hc (φ n)⟩`.
-/
theorem IsLineForm.comp {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {ε : A →+* R} {μ₀ : M →ₛₗ[ε] R} (h : IsLineForm μ₀) (φ : N ≃ₗ[A] M) : IsLineForm (μ₀.comp φ.toLinearMap) := by
  refine ⟨fun e => h.1 (LinearMap.ext fun m => ?_), fun μ => ?_⟩
  · simpa using LinearMap.congr_fun e (φ.symm m)
  · obtain ⟨c, hc⟩ := h.2 (μ.comp φ.symm.toLinearMap)
    exact ⟨c, LinearMap.ext fun n => by simpa using LinearMap.congr_fun hc (φ n)⟩

/- English proof (translation)
Take `⟨T, hT, hx, hle⟩` from `QCoh.exists_affine_mem_le (U := V ⊓ W) _ ⟨(top_le_preimage_iff z).1 h, hW⟩`. Establish `hz` using `(top_le_preimage_iff z).2 hx`. Establish `h₁ : T ≤ V` using `hle.trans inf_le_left`. Set `b` to `he.basis (hle.trans inf_le_right)`. Set `ν : Γ(F, T) →ₛₗ[evz z hz] R` to `(evz z hz).toSemilinearMap.comp (b.coord 0)`.

Establish `hν (t : Γ(F, T)) : ν t = evz z hz (b.repr t 0)` using `rfl`. Use `⟨resForm h₁ (evz_res z hz h h₁) ν, fun e0 => ?_, fun μ => ?_⟩` and prove the remaining obligations. Establish `: ν = 0` using `form_ext hV hT h₁ fun s => LinearMap.congr_fun e0 s`. Establish `h1` using `hν (b 0)`. Rewrite `h1` using `[this]`.

Simplify using `at h1`. Take `⟨μ', hμ'⟩` from `exists_extend hV hT h₁ (evz_res z hz h h₁) μ`. Use `⟨μ' (b 0), LinearMap.ext fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[← hμ']`. Express the relevant statement in the definitionally equal form `_ = μ' (b 0) * ν (resM F h₁ s)`.

Use `conv_lhs => rw [← b.sum_repr (resM F h₁ s)]`. Rewrite using `[Fin.sum_univ_one, μ'.map_smulₛₗ, hν, smul_eq_mul, mul_comm]`.
-/
theorem exists_isLineForm [IsLocalRing R] [F.IsQuasicoherent] (z : Sp R ⟶ X) (hV : IsAffineOpen V)
    (h : ⊤ ≤ z ⁻¹ᵁ V) {e : Fin 1 → Γ(F, W)} (he : IsFrame e) (hW : z (IsLocalRing.closedPoint R) ∈ W) :
    ∃ μ₀ : Γ(F, V) →ₛₗ[evz z h] R, IsLineForm μ₀ := by
  obtain ⟨T, hT, hx, hle⟩ := QCoh.exists_affine_mem_le (U := V ⊓ W) _ ⟨(top_le_preimage_iff z).1 h, hW⟩
  have hz := (top_le_preimage_iff z).2 hx
  have h₁ : T ≤ V := hle.trans inf_le_left
  let b := he.basis (hle.trans inf_le_right)
  let ν : Γ(F, T) →ₛₗ[evz z hz] R := (evz z hz).toSemilinearMap.comp (b.coord 0)
  have hν (t : Γ(F, T)) : ν t = evz z hz (b.repr t 0) := rfl
  refine ⟨resForm h₁ (evz_res z hz h h₁) ν, fun e0 => ?_, fun μ => ?_⟩
  · have : ν = 0 := form_ext hV hT h₁ fun s => LinearMap.congr_fun e0 s
    have h1 := hν (b 0)
    rw [this] at h1
    simp at h1
  · obtain ⟨μ', hμ'⟩ := exists_extend hV hT h₁ (evz_res z hz h h₁) μ
    refine ⟨μ' (b 0), LinearMap.ext fun s => ?_⟩
    rw [← hμ']
    change _ = μ' (b 0) * ν (resM F h₁ s)
    conv_lhs => rw [← b.sum_repr (resM F h₁ s)]
    rw [Fin.sum_univ_one, μ'.map_smulₛₗ, hν, smul_eq_mul, mul_comm]

end Value

/- English proof (translation)
Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := A) (M := M)`. Take `⟨m₀, -, hm₀⟩` from `(insert 0 S).exists_max_image (fun m => ‖ν m‖) ⟨0, Finset.mem_insert_self _ _⟩`. Use `⟨‖ν m₀‖, ⟨m₀, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`. Establish `hm : m ∈ Submodule.span A (S : Set M)` using `hS ▸ Submodule.mem_top`.

Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx => exact hm₀ x (Finset.mem_insert_of_mem hx)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [map_add]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`. Consider the case `smul a x _ hx`. Simplify using `only [ν.map_smulₛₗ, smul_eq_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hε a)).trans hx`.
-/
theorem exists_isGreatest {A M C : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [NormedField C] [IsUltrametricDist C] {ε : A →+* C} (hε : ∀ a, ‖ε a‖ ≤ 1) (ν : M →ₛₗ[ε] C) :
    ∃ c, IsGreatest (Set.range fun m => ‖ν m‖) c := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := M)
  obtain ⟨m₀, -, hm₀⟩ := (insert 0 S).exists_max_image (fun m => ‖ν m‖) ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨‖ν m₀‖, ⟨m₀, rfl⟩, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ Submodule.span A (S : Set M) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact hm₀ x (Finset.mem_insert_of_mem hx)
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    simp only [ν.map_smulₛₗ, smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hε a)).trans hx

/- English proof (translation)
Establish `key (a : intO C) (h : ‖(a : C)‖ = 1) : IsUnit a`. Establish `h0 : (a : C) ≠ 0` using `fun e => by simp [e] at h`. Conclude with `IsUnit.of_mul_eq_one ⟨(a : C)⁻¹, show ‖_‖ ≤ 1 by simp [h]⟩ (Subtype.ext (mul_inv_cancel₀ h0))`. Use `.of_isUnit_or_isUnit_one_sub_self fun a => ?_` and prove the remaining obligations. Break down `(show ‖(a : C)‖ ≤ 1 from a.2).eq_or_lt with h | h` into its components or cases.

Conclude with `.inl (key a h)`. Use `.inr (key _ ?_)` and prove the remaining obligations. Establish `: ‖(1 : C)‖ ≠ ‖-(a : C)‖` using `by simpa using h.ne'`. Rewrite using `[AddSubgroupClass.coe_sub, OneMemClass.coe_one, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this]`. Simplify using `using h.le`.
-/
theorem isLocalRing_intO (C : Type) [NormedField C] [IsUltrametricDist C] : IsLocalRing (intO C) := by
  have key (a : intO C) (h : ‖(a : C)‖ = 1) : IsUnit a := by
    have h0 : (a : C) ≠ 0 := fun e => by simp [e] at h
    exact IsUnit.of_mul_eq_one ⟨(a : C)⁻¹, show ‖_‖ ≤ 1 by simp [h]⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  refine .of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases (show ‖(a : C)‖ ≤ 1 from a.2).eq_or_lt with h | h
  · exact .inl (key a h)
  · refine .inr (key _ ?_)
    have : ‖(1 : C)‖ ≠ ‖-(a : C)‖ := by simpa using h.ne'
    rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this]
    simpa using h.le

section Norm

variable (X) in

abbrev gen (p : ℕ) : X.Opens := X.basicOpen ((p : ℕ) : Γ(X, ⊤))

def oneSec (V : X.Opens) : Γ(structureModule X, V) := (1 : Γ(X, V))

variable {p : ℕ} {C : SCF p} (z : Sp (intO C.S) ⟶ X)

def nrmSet (F : X.Modules) (f : Γ(F, gen X p)) : Set ℝ :=
  {r | ∃ (U : X.Opens) (_ : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U) (k : ℕ) (g : Γ(F, U))
    (lam : Γ(F, U) →ₛₗ[evz z h] ↥(intO ↥C.S)),
    resM F (inf_le_left : U ⊓ gen X p ≤ U) g = p ^ k • resM F (inf_le_right : U ⊓ gen X p ≤ gen X p) f ∧
    r = ‖((lam g : ↥(intO ↥C.S)) : ↥C.S)‖ * (p : ℝ) ^ k}

abbrev zq : Sp C.S ⟶ X := spMap (intO C.S).subtype ≫ z

/- English proof (translation)
Introduce and unpack `r ⟨U, hU, h, k, g, lam, hg, rfl⟩`. Use `⟨U, hU, h, k, φ.hom.app U g, lam.comp (appLinear φ.inv U), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← app_resM, ← app_resM, hg, map_nsmul]`. Establish `: φ.inv.app U (φ.hom.app U g) = g`. Rewrite using `[← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, φ.hom_inv_id]`.

Both sides reduce to the same expression. Rewrite using `[LinearMap.comp_apply, appLinear_apply, this]`.
-/
theorem nrmSet_subset (φ : F ≅ G) (f : Γ(F, gen X p)) : nrmSet z F f ⊆ nrmSet z G (φ.hom.app _ f) := by
  rintro r ⟨U, hU, h, k, g, lam, hg, rfl⟩
  refine ⟨U, hU, h, k, φ.hom.app U g, lam.comp (appLinear φ.inv U), ?_, ?_⟩
  · rw [← app_resM, ← app_resM, hg, map_nsmul]
  · have : φ.inv.app U (φ.hom.app U g) = g := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, φ.hom_inv_id]; rfl
    rw [LinearMap.comp_apply, appLinear_apply, this]

/- English proof (translation)
Use `Set.Subset.antisymm ?_ (nrmSet_subset z φ f)` and prove the remaining obligations. Establish `h` using `nrmSet_subset z φ.symm (φ.hom.app _ f)`. Establish `: φ.symm.hom.app _ (φ.hom.app _ f) = f`. Rewrite using `[← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.symm_hom, φ.hom_inv_id]`. Both sides reduce to the same expression.

Rewrite `h` using `[this]`. Then use the resulting hypothesis.
-/
theorem nrmSet_iso (φ : F ≅ G) (f : Γ(F, gen X p)) : nrmSet z G (φ.hom.app _ f) = nrmSet z F f := by
  refine Set.Subset.antisymm ?_ (nrmSet_subset z φ f)
  have h := nrmSet_subset z φ.symm (φ.hom.app _ f)
  have : φ.symm.hom.app _ (φ.hom.app _ f) = f := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.symm_hom, φ.hom_inv_id]; rfl
  rwa [this] at h

/- English proof (translation)
Rewrite using `[← X.basicOpen_res _ (homOfLE (le_top : U ≤ ⊤)).op, map_natCast]`.
-/
theorem inf_gen_eq (U : X.Opens) : U ⊓ gen X p = X.basicOpen ((p : ℕ) : Γ(X, U)) := by
  rw [← X.basicOpen_res _ (homOfLE (le_top : U ≤ ⊤)).op, map_natCast]

/- English proof (translation)
The claim follows from `inf_gen_eq (p := p) U ▸ hU.basicOpen _`.
-/
theorem isAffineOpen_inf_gen (hU : IsAffineOpen U) : IsAffineOpen (U ⊓ gen X p) :=
  inf_gen_eq (p := p) U ▸ hU.basicOpen _

variable (hp : p ≠ 0)
include hp

/- English proof (translation)
Rewrite using `[Scheme.preimage_basicOpen_top, map_natCast, Scheme.basicOpen_of_isUnit]`. Establish `: IsUnit ((p : ℕ) : C.S)` using `(Nat.cast_ne_zero.2 hp).isUnit`. Simplify using `using this.map (Scheme.ΓSpecIso (CommRingCat.of C.S)).inv.hom`.
-/
theorem zq_le_gen : ⊤ ≤ zq z ⁻¹ᵁ gen X p := by
  rw [Scheme.preimage_basicOpen_top, map_natCast, Scheme.basicOpen_of_isUnit]
  have : IsUnit ((p : ℕ) : C.S) := (Nat.cast_ne_zero.2 hp).isUnit
  simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of C.S)).inv.hom

/- English proof (translation)
Introduce `x _` and use `⟨h (Set.mem_univ _), zq_le_gen z hp (Set.mem_univ x)⟩`.
-/
theorem zq_le (h : ⊤ ≤ z ⁻¹ᵁ U) : ⊤ ≤ zq z ⁻¹ᵁ (U ⊓ gen X p) := fun x _ =>
  ⟨h (Set.mem_univ _), zq_le_gen z hp (Set.mem_univ x)⟩

abbrev evq (h : ⊤ ≤ z ⁻¹ᵁ U) : Γ(X, U ⊓ gen X p) →+* C.S := evz (zq z) (zq_le z hp h)

/- English proof (translation)
The claim follows from `(evz_res (zq z) _ (fun x _ => h (Set.mem_univ _)) _ a).trans (evz_comp _ z h _ a)`.
-/
theorem evq_res (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(X, U)) :
    evq z hp h (resG X inf_le_left a) = ((intO C.S).subtype.comp (evz z h)) a :=
  (evz_res (zq z) _ (fun x _ => h (Set.mem_univ _)) _ a).trans (evz_comp _ z h _ a)

def IsInt {h : ⊤ ≤ z ⁻¹ᵁ U} (μ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S) : Prop :=
  ∀ m : Γ(F, U), ‖μ (resM F inf_le_left m)‖ ≤ 1

/- English proof (translation)
Establish `: (p : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hp`. Rewrite using `[map_nsmul, nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow, C.norm_p, mul_right_comm, ← mul_pow, inv_mul_cancel₀ this, one_pow, one_mul]`.
-/
theorem norm_nsmul_mul {M A : Type} [CommRing A] [AddCommGroup M] [Module A M] {ε : A →+* C.S} (μ : M →ₛₗ[ε] C.S)
    (k : ℕ) (v : M) : ‖μ (p ^ k • v)‖ * (p : ℝ) ^ k = ‖μ v‖ := by
  have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [map_nsmul, nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow, C.norm_p, mul_right_comm, ← mul_pow,
    inv_mul_cancel₀ this, one_pow, one_mul]

/- English proof (translation)
Use `isLocalRing_intO C.S` as an intermediate fact. Use `Set.Subset.antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `r ⟨U', hU', h', k, g, lam, hg, rfl⟩`. Take `⟨T, hT, hx, hle⟩` from `QCoh.exists_affine_mem_le (U := U ⊓ U') _ ⟨(top_le_preimage_iff z).1 h, (top_le_preimage_iff z).1 h'⟩`. Establish `hz` using `(top_le_preimage_iff z).2 hx`.

Establish `h₁ : T ≤ U` using `hle.trans inf_le_left`. Establish `h₂ : T ≤ U'` using `hle.trans inf_le_right`. Take `⟨l₁, hl₁⟩` from `exists_extend hU' hT h₂ (evz_res z hz h' h₂) lam`. Take `⟨μ, hμ⟩` from `exists_extend hT (isAffineOpen_inf_gen (p := p) hT) inf_le_left (evq_res z hp hz) { toFun m := (l₁ m : C.S) map_add' a b := by rw [map_add]; rfl map_smul' a m := by rw [l₁.map_smulₛₗ]; rfl }`. Establish `h₃ : T ⊓ gen X p ≤ U ⊓ gen X p` using `inf_le_inf_right _ h₁`.

Use `⟨resForm h₃ (evz_res (zq z) _ _ h₃) μ, fun m => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖μ (resM F h₃ (resM F _ m))‖ ≤ 1`. Rewrite using `[resM_resM, ← resM_resM h₁ inf_le_left, hμ]`. Conclude with `(l₁ _).2`. Express the relevant statement in the definitionally equal form `_ = ‖μ (resM F h₃ (resM F _ f))‖`.

Establish `e` using `congrArg (resM F (inf_le_inf_right _ h₂ : T ⊓ gen X p ≤ U' ⊓ gen X p)) hg`. Rewrite `e` using `[map_nsmul, resM_resM, resM_resM]`. Rewrite using `[resM_resM, ← norm_nsmul_mul hp μ k, ← e, ← resM_resM h₂ inf_le_left, hμ, ← hl₁]`. Both sides reduce to the same expression. Introduce and unpack `r ⟨μ, hμ, rfl⟩`.

Take `⟨k, g, hg⟩` from `QCoh.exists_pow_smul_eq_res F hU ((p : ℕ) : Γ(X, U)) inf_le_left (inf_gen_eq U) (resM F inf_le_right f)`. Establish `hg' : resM F (inf_le_left : U ⊓ gen X p ≤ U) g = p ^ k • resM F inf_le_right f`. Rewrite `hg` using `[map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Conclude with `hg.symm`. Use `⟨U, hU, h, k, g, { toFun m := ⟨μ (resM F inf_le_left m), hμ m⟩ map_add' a b := Subtype.ext (by simp) map_smul' a m := Subtype.ext (by` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `μ _ = _`. Rewrite using `[resM_smul, μ.map_smulₛₗ, evq_res]`. Use the proof step `rfl) }, hg', ?_⟩`. Express the relevant statement in the definitionally equal form `_ = ‖μ (resM F _ g)‖ * _`. Rewrite using `[hg', norm_nsmul_mul hp]`.
-/
theorem nrmSet_eq [F.IsQuasicoherent] (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(F, gen X p)) :
    nrmSet z F f = {r | ∃ μ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S, IsInt z hp μ ∧ r = ‖μ (resM F inf_le_right f)‖} := by
  have := isLocalRing_intO C.S
  refine Set.Subset.antisymm ?_ ?_
  · rintro r ⟨U', hU', h', k, g, lam, hg, rfl⟩
    obtain ⟨T, hT, hx, hle⟩ := QCoh.exists_affine_mem_le (U := U ⊓ U') _
      ⟨(top_le_preimage_iff z).1 h, (top_le_preimage_iff z).1 h'⟩
    have hz := (top_le_preimage_iff z).2 hx
    have h₁ : T ≤ U := hle.trans inf_le_left
    have h₂ : T ≤ U' := hle.trans inf_le_right
    obtain ⟨l₁, hl₁⟩ := exists_extend hU' hT h₂ (evz_res z hz h' h₂) lam
    obtain ⟨μ, hμ⟩ := exists_extend hT (isAffineOpen_inf_gen (p := p) hT) inf_le_left (evq_res z hp hz)
      { toFun m := (l₁ m : C.S)
        map_add' a b := by rw [map_add]; rfl
        map_smul' a m := by rw [l₁.map_smulₛₗ]; rfl }
    have h₃ : T ⊓ gen X p ≤ U ⊓ gen X p := inf_le_inf_right _ h₁
    refine ⟨resForm h₃ (evz_res (zq z) _ _ h₃) μ, fun m => ?_, ?_⟩
    · change ‖μ (resM F h₃ (resM F _ m))‖ ≤ 1
      rw [resM_resM, ← resM_resM h₁ inf_le_left, hμ]
      exact (l₁ _).2
    · change _ = ‖μ (resM F h₃ (resM F _ f))‖
      have e := congrArg (resM F (inf_le_inf_right _ h₂ : T ⊓ gen X p ≤ U' ⊓ gen X p)) hg
      rw [map_nsmul, resM_resM, resM_resM] at e
      rw [resM_resM, ← norm_nsmul_mul hp μ k, ← e, ← resM_resM h₂ inf_le_left, hμ, ← hl₁]
      rfl
  · rintro r ⟨μ, hμ, rfl⟩
    obtain ⟨k, g, hg⟩ := QCoh.exists_pow_smul_eq_res F hU ((p : ℕ) : Γ(X, U)) inf_le_left (inf_gen_eq U)
      (resM F inf_le_right f)
    have hg' : resM F (inf_le_left : U ⊓ gen X p ≤ U) g = p ^ k • resM F inf_le_right f := by
      rw [map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hg
      exact hg.symm
    refine ⟨U, hU, h, k, g,
      { toFun m := ⟨μ (resM F inf_le_left m), hμ m⟩
        map_add' a b := Subtype.ext (by simp)
        map_smul' a m := Subtype.ext (by
          change μ _ = _
          rw [resM_smul, μ.map_smulₛₗ, evq_res]; rfl) }, hg', ?_⟩
    change _ = ‖μ (resM F _ g)‖ * _
    rw [hg', norm_nsmul_mul hp]

variable {h : ⊤ ≤ z ⁻¹ᵁ U}

def vals (μ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S) : Set ℝ :=
  Set.range fun m : Γ(F, U) => ‖μ (resM F inf_le_left m)‖

/- English proof (translation)
The claim follows from `have := QCoh.finite_sections F hU exists_isGreatest (fun a => (evz z h a).2) (resForm inf_le_left (evq_res z hp h) μ)`.
-/
theorem exists_isGreatest_vals [IsFiniteQC F] (hU : IsAffineOpen U) (μ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S) :
    ∃ c, IsGreatest (vals z hp μ) c :=
  have := QCoh.finite_sections F hU
  exists_isGreatest (fun a => (evz z h a).2) (resForm inf_le_left (evq_res z hp h) μ)

section Line

variable [F.IsQuasicoherent] (hU : IsAffineOpen U) {μ₀ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S}
  (h₀ : IsLineForm μ₀) {c : ℝ} (hc : IsGreatest (vals z hp μ₀) c)
include hU h₀ hc

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `h₀.1 (form_ext hU (isAffineOpen_inf_gen hU) inf_le_left fun s => ?_)` and prove the remaining obligations. Conclude with `norm_le_zero_iff.1 ((hc.2 ⟨s, rfl⟩).trans (not_lt.1 hn))`.
-/
theorem pos_of_isGreatest : 0 < c := by
  by_contra hn
  refine h₀.1 (form_ext hU (isAffineOpen_inf_gen hU) inf_le_left fun s => ?_)
  exact norm_le_zero_iff.1 ((hc.2 ⟨s, rfl⟩).trans (not_lt.1 hn))

/- English proof (translation)
Take `⟨t, rfl⟩` from `h₀.2 μ`. Take `⟨m, hm⟩` from `hc.1`. Establish `h1` using `hμ m`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, norm_mul] at h1 hm ⊢`. Rewrite `h1` using `[hm]`.

Rewrite using `[le_div_iff₀ (pos_of_isGreatest z hp hU h₀ hc)]`. Use polynomial arithmetic with `[norm_nonneg (μ₀ v)]`.
-/
theorem norm_le_of_isInt {μ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S} (hμ : IsInt z hp μ) (v : Γ(F, U ⊓ gen X p)) :
    ‖μ v‖ ≤ ‖μ₀ v‖ / c := by
  obtain ⟨t, rfl⟩ := h₀.2 μ
  obtain ⟨m, hm⟩ := hc.1
  have h1 := hμ m
  simp only [LinearMap.smul_apply, smul_eq_mul, norm_mul] at h1 hm ⊢
  rw [hm] at h1
  rw [le_div_iff₀ (pos_of_isGreatest z hp hU h₀ hc)]
  nlinarith [norm_nonneg (μ₀ v)]

/- English proof (translation)
Take `⟨m, hm⟩` from `hc.1`. Establish `key (v) : ‖((μ₀ (resM F inf_le_left m))⁻¹ • μ₀) v‖ = ‖μ₀ v‖ / c`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, norm_mul, norm_inv] at hm ⊢`. Rewrite using `[hm, div_eq_inv_mul]`. Conclude with `⟨_, fun n => (key _).trans_le ((div_le_one (pos_of_isGreatest z hp hU h₀ hc)).2 (hc.2 ⟨n, rfl⟩)), key⟩`.
-/
theorem exists_isInt : ∃ μ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S, IsInt z hp μ ∧ ∀ v, ‖μ v‖ = ‖μ₀ v‖ / c := by
  obtain ⟨m, hm⟩ := hc.1
  have key (v) : ‖((μ₀ (resM F inf_le_left m))⁻¹ • μ₀) v‖ = ‖μ₀ v‖ / c := by
    simp only [LinearMap.smul_apply, smul_eq_mul, norm_mul, norm_inv] at hm ⊢
    rw [hm, div_eq_inv_mul]
  exact ⟨_, fun n => (key _).trans_le ((div_le_one (pos_of_isGreatest z hp hU h₀ hc)).2 (hc.2 ⟨n, rfl⟩)), key⟩

/- English proof (translation)
Rewrite using `[nrmSet_eq z hp hU h]`. Take `⟨μ, hμ, e⟩` from `exists_isInt z hp hU h₀ hc`. Use `⟨⟨μ, hμ, (e _).symm⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `r ⟨μ, hμ, rfl⟩`. Conclude with `norm_le_of_isInt z hp hU h₀ hc hμ _`.
-/
theorem isGreatest_nrmSet (f : Γ(F, gen X p)) : IsGreatest (nrmSet z F f) (‖μ₀ (resM F inf_le_right f)‖ / c) := by
  rw [nrmSet_eq z hp hU h]
  obtain ⟨μ, hμ, e⟩ := exists_isInt z hp hU h₀ hc
  refine ⟨⟨μ, hμ, (e _).symm⟩, ?_⟩
  rintro r ⟨μ, hμ, rfl⟩
  exact norm_le_of_isInt z hp hU h₀ hc hμ _

/- English proof (translation)
Rewrite using `[nrmSet_eq z hp hU h]`. Establish `hpos` using `pos_of_isGreatest z hp hU h₀ hc`. Take `⟨μ, hμ, e₀⟩` from `exists_isInt z hp hU h₀ hc`. Take `⟨m, hm⟩` from `hc₁.1`. Use `⟨⟨μ.comp (homEval F (resM G inf_le_left m)), fun χ => ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, homEval_apply, homApp_res, homApp_resM χ le_rfl]`. Conclude with `hμ _`. Rewrite using `[LinearMap.comp_apply, homEval_apply, homApp_res, e₀, ← hm]`. Both sides reduce to the same expression. Introduce and unpack `r ⟨Λ, hΛ, rfl⟩`.

Rewrite using `[← sum_homIns he inf_le_left (resM _ inf_le_right ψ), map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg (hm ▸ norm_nonneg _) hpos.le) fun i _ => ?_` and prove the remaining obligations. Establish `hi : IsInt z hp (Λ.comp (homIns he inf_le_left i))` using `fun n => by`. Establish `: homIns he inf_le_left i (resM F (inf_le_left : U ⊓ gen X p ≤ U) n) = resM _ inf_le_left (homIns he le_rfl i n)` using `VB.hom_ext fun W hW s => by`. Rewrite using `[homApp_res, homApp_homIns, homApp_homIns, resM_resM]`.

Rewrite using `[LinearMap.comp_apply, this]`. Conclude with `hΛ _`. Use `(norm_le_of_isInt z hp hU h₀ hc hi _).trans (div_le_div_of_nonneg_right ?_ hpos.le)` and prove the remaining obligations. Conclude with `hc₁.2 ⟨e i, rfl⟩`.
-/
theorem isGreatest_nrmSet_hom [(homMod G F).IsQuasicoherent] {e : ι → Γ(G, U)} (he : IsFrame e)
    (ψ : Γ(homMod G F, gen X p)) {c₁ : ℝ} (hc₁ : IsGreatest (vals z hp (μ₀.comp (homApp ψ inf_le_right))) c₁) :
    IsGreatest (nrmSet z (homMod G F) ψ) (c₁ / c) := by
  rw [nrmSet_eq z hp hU h]
  have hpos := pos_of_isGreatest z hp hU h₀ hc
  obtain ⟨μ, hμ, e₀⟩ := exists_isInt z hp hU h₀ hc
  obtain ⟨m, hm⟩ := hc₁.1
  refine ⟨⟨μ.comp (homEval F (resM G inf_le_left m)), fun χ => ?_, ?_⟩, ?_⟩
  · rw [LinearMap.comp_apply, homEval_apply, homApp_res, homApp_resM χ le_rfl]
    exact hμ _
  · rw [LinearMap.comp_apply, homEval_apply, homApp_res, e₀, ← hm]
    rfl
  · rintro r ⟨Λ, hΛ, rfl⟩
    rw [← sum_homIns he inf_le_left (resM _ inf_le_right ψ), map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (div_nonneg (hm ▸ norm_nonneg _) hpos.le) fun i _ => ?_
    have hi : IsInt z hp (Λ.comp (homIns he inf_le_left i)) := fun n => by
      have : homIns he inf_le_left i (resM F (inf_le_left : U ⊓ gen X p ≤ U) n) =
          resM _ inf_le_left (homIns he le_rfl i n) := VB.hom_ext fun W hW s => by
        rw [homApp_res, homApp_homIns, homApp_homIns, resM_resM]
      rw [LinearMap.comp_apply, this]
      exact hΛ _
    refine (norm_le_of_isInt z hp hU h₀ hc hi _).trans (div_le_div_of_nonneg_right ?_ hpos.le)
    exact hc₁.2 ⟨e i, rfl⟩

end Line

def compSec {E : X.Modules} (π : E ⟶ F) (φ : F.restrict U.ι ⟶ G.restrict U.ι) : Γ(homMod E G, U) :=
  (homMap π (𝟙 G)).app U (homOfRestrict φ)

/- English proof (translation)
Use `(isFiniteQC_homMod (G := G) hE).isQuasicoherent` as an intermediate fact. Use `hE.isQuasicoherent` as an intermediate fact. Use `isGreatest_nrmSet_hom z hp hU hμ hc₂ he _ ?_` and prove the remaining obligations. Use `hc₁ using 1` and compare the differences between its conclusion and the goal. Use `Eq.trans ?_ ((QCoh.surjective_app_of_epi π hU).range_comp _)` and prove the remaining obligations.

Use `congrArg Set.range (funext fun m => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, ← app_resM]`. Both sides reduce to the same expression.
-/
theorem isGreatest_nrmSet_compSec {E : X.Modules} {r : ℕ} (hE : IsVB E r) (π : E ⟶ F) [Epi π] [IsFiniteQC F]
    [IsFiniteQC G] (hU : IsAffineOpen U) {e : ι → Γ(E, U)} (he : IsFrame e)
    (φ : F.restrict (gen X p).ι ≅ G.restrict (gen X p).ι) {μ : Γ(G, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S}
    (hμ : IsLineForm μ) {c₁ c₂ : ℝ}
    (hc₁ : IsGreatest (vals z hp (μ.comp (equivOfRestrict φ inf_le_right).toLinearMap)) c₁)
    (hc₂ : IsGreatest (vals z hp μ) c₂) : IsGreatest (nrmSet z (homMod E G) (compSec π φ.hom)) (c₁ / c₂) := by
  have := (isFiniteQC_homMod (G := G) hE).isQuasicoherent
  have := hE.isQuasicoherent
  refine isGreatest_nrmSet_hom z hp hU hμ hc₂ he _ ?_
  convert hc₁ using 1
  refine Eq.trans ?_ ((QCoh.surjective_app_of_epi π hU).range_comp _)
  refine congrArg Set.range (funext fun m => ?_)
  simp only [Function.comp_apply, ← app_resM]
  rfl

/- English proof (translation)
Take `⟨T, e, hx, he⟩` from `hF ⟨zq z (IsLocalRing.closedPoint _), zq_le_gen z hp (Set.mem_univ _)⟩`. Conclude with `exists_isLineForm (zq z) (isAffineOpen_inf_gen hU) _ ((isFrame_restrict_iff _ e).1 he) ⟨_, hx, rfl⟩`.
-/
theorem exists_isLineForm_gen [F.IsQuasicoherent] (hF : IsVB (F.restrict (gen X p).ι) 1) (hU : IsAffineOpen U) :
    ∃ μ : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S, IsLineForm μ := by
  obtain ⟨T, e, hx, he⟩ := hF ⟨zq z (IsLocalRing.closedPoint _), zq_le_gen z hp (Set.mem_univ _)⟩
  exact exists_isLineForm (zq z) (isAffineOpen_inf_gen hU) _ ((isFrame_restrict_iff _ e).1 he) ⟨_, hx, rfl⟩

/- English proof (translation)
Use `isLocalRing_intO C.S` as an intermediate fact. Take `⟨T, e, hx, he⟩` from `hE (z (IsLocalRing.closedPoint _))`. Take `⟨U, e', hU, hx', hle, he'⟩` from `hE'.exists_affine hx`. Establish `h` using `(top_le_preimage_iff z).2 hx'`. Take `⟨μ, hμ⟩` from `exists_isLineForm_gen z hp (h := h) hG hU`.

Establish `hμ'` using `hμ.comp (equivOfRestrict φ inf_le_right)`. Take `⟨c₁, hc₁⟩` from `exists_isGreatest_vals z hp hU (μ.comp (equivOfRestrict φ inf_le_right).toLinearMap)`. Take `⟨c₂, hc₂⟩` from `exists_isGreatest_vals z hp hU μ`. Establish `e₀ : (μ.comp (equivOfRestrict φ inf_le_right).toLinearMap).comp (equivOfRestrict φ.symm inf_le_right).toLinearMap = μ` using `LinearMap.ext fun s => congrArg μ ((equivOfRestrict φ inf_le_right).apply_symm_apply s)`. Rewrite using `[(isGreatest_nrmSet_compSec z hp hE π hU (he.res hle) φ hμ hc₁ hc₂).csSup_eq, inv_div]`.

Conclude with `⟨div_pos (pos_of_isGreatest z hp hU hμ' hc₁) (pos_of_isGreatest z hp hU hμ hc₂), (isGreatest_nrmSet_compSec z hp hE' π' hU he' φ.symm hμ' (e₀.symm ▸ hc₂) hc₁).csSup_eq⟩`.
-/
theorem sSup_compSec_mul {E E' : X.Modules} {r r' : ℕ} (hE : IsVB E r) (hE' : IsVB E' r') (π : E ⟶ F) [Epi π]
    (π' : E' ⟶ G) [Epi π'] [IsFiniteQC F] [IsFiniteQC G] (hG : IsVB (G.restrict (gen X p).ι) 1)
    (φ : F.restrict (gen X p).ι ≅ G.restrict (gen X p).ι) :
    0 < sSup (nrmSet z (homMod E G) (compSec π φ.hom)) ∧
      sSup (nrmSet z (homMod E' F) (compSec π' φ.inv)) = (sSup (nrmSet z (homMod E G) (compSec π φ.hom)))⁻¹ := by
  have := isLocalRing_intO C.S
  obtain ⟨T, e, hx, he⟩ := hE (z (IsLocalRing.closedPoint _))
  obtain ⟨U, e', hU, hx', hle, he'⟩ := hE'.exists_affine hx
  have h := (top_le_preimage_iff z).2 hx'
  obtain ⟨μ, hμ⟩ := exists_isLineForm_gen z hp (h := h) hG hU
  have hμ' := hμ.comp (equivOfRestrict φ inf_le_right)
  obtain ⟨c₁, hc₁⟩ := exists_isGreatest_vals z hp hU (μ.comp (equivOfRestrict φ inf_le_right).toLinearMap)
  obtain ⟨c₂, hc₂⟩ := exists_isGreatest_vals z hp hU μ
  have e₀ : (μ.comp (equivOfRestrict φ inf_le_right).toLinearMap).comp
      (equivOfRestrict φ.symm inf_le_right).toLinearMap = μ :=
    LinearMap.ext fun s => congrArg μ ((equivOfRestrict φ inf_le_right).apply_symm_apply s)
  rw [(isGreatest_nrmSet_compSec z hp hE π hU (he.res hle) φ hμ hc₁ hc₂).csSup_eq, inv_div]
  exact ⟨div_pos (pos_of_isGreatest z hp hU hμ' hc₁) (pos_of_isGreatest z hp hU hμ hc₂),
    (isGreatest_nrmSet_compSec z hp hE' π' hU he' φ.symm hμ' (e₀.symm ▸ hc₂) hc₁).csSup_eq⟩

/- English proof (translation)
Use `isLocalRing_intO C.S` as an intermediate fact. Establish `hF : IsVB F 1` using `by simpa using hu.isVB`. Use `hF.isFiniteQC` as an intermediate fact. Take `⟨U, e, hU, hx, -, he⟩` from `hE.exists_affine (V := ⊤) (x := z (IsLocalRing.closedPoint _)) trivial`. Establish `h` using `(top_le_preimage_iff z).2 hx`.

Take `⟨μ, hμ⟩` from `exists_isLineForm_gen z hp (h := h) ((hF.restrict _).of_iso φ) hU`. Take `⟨c₂, hc₂⟩` from `exists_isGreatest_vals z hp hU μ`. Use `set ν := μ.comp (equivOfRestrict φ (inf_le_right : U ⊓ gen X p ≤ _)).toLinearMap with hν`. Establish `hc₁ : IsGreatest (vals z hp ν) ‖ν (resM F le_top u)‖`. Use `⟨⟨resM F le_top u, by simp only [resM_resM]⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨m, rfl⟩`. Establish `hm` using `(hu.basis (le_top : U ≤ ⊤)).sum_repr m`. Rewrite `hm` using `[Fin.sum_univ_one, IsFrame.basis_apply]`. Simplify using `only`. Rewrite using `[← hm, resM_smul, resM_resM, ν.map_smulₛₗ, evq_res, smul_eq_mul, norm_mul]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) (evz z h _).2`. Rewrite using `[(isGreatest_nrmSet_compSec z hp hE π hU he φ hμ hc₁ hc₂).csSup_eq, (isGreatest_nrmSet z hp hU hμ hc₂ _).csSup_eq, ← homApp_resM, resM_resM]`. Both sides reduce to the same expression.
-/
theorem sSup_compSec_eq {E : X.Modules} {r : ℕ} (hE : IsVB E r) (π : E ⟶ F) [Epi π] [IsFiniteQC G]
    {u : Γ(F, ⊤)} (hu : IsFrame fun _ : Fin 1 => u) (φ : F.restrict (gen X p).ι ≅ G.restrict (gen X p).ι) :
    sSup (nrmSet z G (homApp (homOfRestrict φ.hom) le_rfl (resM F le_top u))) =
      sSup (nrmSet z (homMod E G) (compSec π φ.hom)) := by
  have := isLocalRing_intO C.S
  have hF : IsVB F 1 := by simpa using hu.isVB
  have := hF.isFiniteQC
  obtain ⟨U, e, hU, hx, -, he⟩ := hE.exists_affine (V := ⊤) (x := z (IsLocalRing.closedPoint _)) trivial
  have h := (top_le_preimage_iff z).2 hx
  obtain ⟨μ, hμ⟩ := exists_isLineForm_gen z hp (h := h) ((hF.restrict _).of_iso φ) hU
  obtain ⟨c₂, hc₂⟩ := exists_isGreatest_vals z hp hU μ
  set ν := μ.comp (equivOfRestrict φ (inf_le_right : U ⊓ gen X p ≤ _)).toLinearMap with hν
  have hc₁ : IsGreatest (vals z hp ν) ‖ν (resM F le_top u)‖ := by
    refine ⟨⟨resM F le_top u, by simp only [resM_resM]⟩, ?_⟩
    rintro _ ⟨m, rfl⟩
    have hm := (hu.basis (le_top : U ≤ ⊤)).sum_repr m
    rw [Fin.sum_univ_one, IsFrame.basis_apply] at hm
    simp only
    rw [← hm, resM_smul, resM_resM, ν.map_smulₛₗ, evq_res, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (evz z h _).2
  rw [(isGreatest_nrmSet_compSec z hp hE π hU he φ hμ hc₁ hc₂).csSup_eq, (isGreatest_nrmSet z hp hU hμ hc₂ _).csSup_eq,
    ← homApp_resM, resM_resM]
  rfl

end Norm

end GlobalTheory.PtNorm
