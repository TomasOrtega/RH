import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Amp
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

variable {Z : Scheme.{0}} {T : Type} [CommRing T]

def ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(Z, U) ⟶ CommRingCat.of T :=
  x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom

/- English proof (translation)
Establish `: ev x U h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).inv = x.appLE U ⊤ h`. Rewrite using `[ev, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Conclude with `congrArg (fun q => q.hom a) this`.
-/
theorem inv_ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((ev x U h).hom a) = (x.appLE U ⊤ h).hom a := by
  have : ev x U h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).inv = x.appLE U ⊤ h := by
    rw [ev, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun q => q.hom a) this

/- English proof (translation)
Use `eq_of_baseRingHom_top ?_` and prove the remaining obligations. Rewrite using `[← baseRingHom_appLE s x U ⊤ h, baseRingHom_top, spMap, CommRingCat.ofHom_hom, ← Scheme.ΓSpecIso_inv_naturality, ev]`. Simplify using `only [Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
theorem comp_str {R : Type} [CommRing R] (s : Z ⟶ Sp R) (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x ≫ s = spMap (baseRingHom s U ≫ ev x U h).hom := by
  refine eq_of_baseRingHom_top ?_
  rw [← baseRingHom_appLE s x U ⊤ h, baseRingHom_top, spMap, CommRingCat.ofHom_hom,
    ← Scheme.ΓSpecIso_inv_naturality, ev]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Rewrite using `[Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ev, Spec.map_comp, ← Spec.map_comp (U.topIso.inv)]`. Use `congr 2`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.
-/
theorem comp_toSpecΓ (U : Z.Opens) (y : Sp T ⟶ U.toScheme) (h : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U) :
    y ≫ U.toSpecΓ = Spec.map (ev (y ≫ U.ι) U h) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ev, Spec.map_comp,
    ← Spec.map_comp (U.topIso.inv)]
  congr 2
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

/- English proof (translation)
Use `ext_germ fun z hz => ?_` and prove the remaining obligations. Establish `ht : ⊤ ≤ Z.fromSpecStalk z ⁻¹ᵁ U` using `fun p _ => by`. Establish `: Z.fromSpecStalk z p ∈ Set.range (Z.fromSpecStalk z)` using `⟨p, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Conclude with `this.mem_open U.isOpen hz`.

Establish `e : ev (T` using `Z.presheaf.stalk z) (Z.fromSpecStalk z) U ht = Z.presheaf.germ U z hz := by`. Express the relevant statement in the definitionally equal form `(Z.fromSpecStalk z).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk z)).hom = _`. Rewrite using `[Scheme.Hom.appLE, Scheme.fromSpecStalk_app hz]`. Simplify using `only [Category.assoc]`. Establish `e : (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE (le_top : Z.fromSpecStalk z ⁻¹ᵁ U ≤ ⊤)).op ≫ (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE ht).op = 𝟙 _`.

Rewrite using `[← Functor.map_comp]`. Conclude with `CategoryTheory.Functor.map_id _ _`. Rewrite using `[reassoc_of% e, Iso.inv_hom_id, Category.comp_id]`. Rewrite using `[map_zero, ← e]`. Conclude with `H _ _ ht`.
-/
theorem eq_zero_of_ev {U : Z.Opens} (a : Γ(Z, U))
    (H : ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z) (h : ⊤ ≤ x ⁻¹ᵁ U), (ev x U h).hom a = 0) : a = 0 := by
  refine ext_germ fun z hz => ?_
  have ht : ⊤ ≤ Z.fromSpecStalk z ⁻¹ᵁ U := fun p _ => by
    have : Z.fromSpecStalk z p ∈ Set.range (Z.fromSpecStalk z) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hz
  have e : ev (T := Z.presheaf.stalk z) (Z.fromSpecStalk z) U ht = Z.presheaf.germ U z hz := by
    change (Z.fromSpecStalk z).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk z)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hz]
    simp only [Category.assoc]
    have e : (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE (le_top : Z.fromSpecStalk z ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  rw [map_zero, ← e]
  exact H _ _ ht

variable {M : LB Z} {σ : Type} {th : σ → M.Sec}

/- English proof (translation)
Establish `hu : ∀ k, IsUnit ((secPull (th i) x).f k)` using `fun k => by`. Use `isUnit_resG_sec (secPull (th i) x) k (le_top.trans (h.trans (nonzeroLocus_secPull (th i) x).ge)) le_rfl` as an intermediate fact. Rewrite `this` using `[resG_self]`. Then use the resulting hypothesis. Use `⟨⟨fun k => (hu k).unit⟩, fun k l => Units.ext ((secPull (th i) x).compat k l), fun j k e => ?_⟩` and prove the remaining obligations. Establish `e' : (M.pull x).U k ≤ x ⁻¹ᵁ (nonzeroLocus (th i) ⊓ M.U (k ⟨⟩))` using `le_inf (le_top.trans h) e`.

Use `congrArg (x.appLE _ _ e').hom (secRatio_spec (th i) (th j) (k ⟨⟩))` as an intermediate fact. Rewrite `this` using `[map_mul, appLE_resG, appLE_resG, appLE_resG]`. Rewrite using `[inv_ev, resG_appLE]`. Conclude with `this`.
-/
theorem secCoord_ratio (x : Sp T ⟶ Z) (i : σ) (h : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (th i)) :
    SecCoord M th x fun j => (ev x _ h).hom (secRatio (th i) (th j)) := by
  have hu : ∀ k, IsUnit ((secPull (th i) x).f k) := fun k => by
    have := isUnit_resG_sec (secPull (th i) x) k
      (le_top.trans (h.trans (nonzeroLocus_secPull (th i) x).ge)) le_rfl
    rwa [resG_self] at this
  refine ⟨⟨fun k => (hu k).unit⟩, fun k l => Units.ext ((secPull (th i) x).compat k l), fun j k e => ?_⟩
  have e' : (M.pull x).U k ≤ x ⁻¹ᵁ (nonzeroLocus (th i) ⊓ M.U (k ⟨⟩)) := le_inf (le_top.trans h) e
  have := congrArg (x.appLE _ _ e').hom (secRatio_spec (th i) (th j) (k ⟨⟩))
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  rw [inv_ev, resG_appLE]
  exact this

/- English proof (translation)
Establish `hle : ∀ l : PUnit → M.ι, (M.pull x).U l ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U k)` using `fun l => le_inf (pull_U M x l).le (le_top.trans h)`. Use `⟨⟨fun l => Units.map (x.appLE _ _ (hle l)).hom.toMonoidHom (M.g (l ⟨⟩) k)⟩, (RepBC.isGen_val _).2 fun l l' => ?_, fun j l e => ?_⟩` and prove the remaining obligations. Establish `e' : (M.pull x).U l ⊓ (M.pull x).U l' ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U (l' ⟨⟩) ⊓ M.U k)` using `le_inf (RepBC.pull_inf_le M x l l') (le_top.trans h)`. Use `congrArg (fun u => (x.appLE _ _ e').hom (Units.val u)) (hM.cocycle (l ⟨⟩) (l' ⟨⟩) k)` as an intermediate fact. Simplify using `only [Units.val_mul, val_res, map_mul] at this`.

Rewrite `this` using `[appLE_resG, appLE_resG, appLE_resG]`. Rewrite using `[RepBC.pull_g M x l l' (RepBC.pull_inf_le M x l l')]`. Conclude with `(resG_appLE x (hle l) _ _).trans (this.symm.trans (congrArg _ (resG_appLE x (hle l') _ _).symm))`. Use `congrArg (x.appLE _ _ (hle l)).hom ((th j).compat (l ⟨⟩) k)` as an intermediate fact. Rewrite `this` using `[map_mul]`.

Use `erw [appLE_resG, appLE_resG] at this`. Rewrite using `[inv_ev, resG_appLE, mul_comm]`. Conclude with `this`.
-/
theorem secCoord_chart (hM : M.IsLB) (x : Sp T ⟶ Z) (k : M.ι) (h : ⊤ ≤ x ⁻¹ᵁ M.U k) :
    SecCoord M th x fun j => (ev x _ h).hom ((th j).f k) := by
  have hle : ∀ l : PUnit → M.ι, (M.pull x).U l ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U k) := fun l =>
    le_inf (pull_U M x l).le (le_top.trans h)
  refine ⟨⟨fun l => Units.map (x.appLE _ _ (hle l)).hom.toMonoidHom (M.g (l ⟨⟩) k)⟩,
    (RepBC.isGen_val _).2 fun l l' => ?_, fun j l e => ?_⟩
  · have e' : (M.pull x).U l ⊓ (M.pull x).U l' ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U (l' ⟨⟩) ⊓ M.U k) :=
      le_inf (RepBC.pull_inf_le M x l l') (le_top.trans h)
    have := congrArg (fun u => (x.appLE _ _ e').hom (Units.val u)) (hM.cocycle (l ⟨⟩) (l' ⟨⟩) k)
    simp only [Units.val_mul, val_res, map_mul] at this
    rw [appLE_resG, appLE_resG, appLE_resG] at this
    rw [RepBC.pull_g M x l l' (RepBC.pull_inf_le M x l l')]
    exact (resG_appLE x (hle l) _ _).trans (this.symm.trans (congrArg _ (resG_appLE x (hle l') _ _).symm))
  · have := congrArg (x.appLE _ _ (hle l)).hom ((th j).compat (l ⟨⟩) k)
    rw [map_mul] at this
    erw [appLE_resG, appLE_resG] at this
    rw [inv_ev, resG_appLE, mul_comm]
    exact this

/- English proof (translation)
Take `⟨τ, -, h⟩` from `h`. Take `⟨k, hk⟩` from `exists_chart hM (x p)`. Establish `e` using `congrArg (Sp T).basicOpen (h i (fun _ => k) (pull_U M x _).le)`. Rewrite `e` using `[Scheme.basicOpen_appLE, Scheme.basicOpen_mul, Scheme.basicOpen_res, (Sp T).basicOpen_of_isUnit (Units.isUnit _)]`. Establish `hp' : p ∈ (M.pull x).U fun _ => k` using `(pull_U M x fun _ => k).ge hk`.

Establish `h2 : p ∈ (Sp T).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i))` using `(basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).ge hp`. Conclude with `Opens.mem_iSup.2 ⟨k, (e.ge ⟨⟨hp', h2⟩, hp'⟩).2⟩`.
-/
theorem mem_locus (hM : M.IsLB) {x : Sp T ⟶ Z} {v : σ → T} (h : SecCoord M th x v) {i : σ} {p : Sp T}
    (hp : v i ∉ p.asIdeal) : x p ∈ nonzeroLocus (th i) := by
  obtain ⟨τ, -, h⟩ := h
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  have e := congrArg (Sp T).basicOpen (h i (fun _ => k) (pull_U M x _).le)
  rw [Scheme.basicOpen_appLE, Scheme.basicOpen_mul, Scheme.basicOpen_res,
    (Sp T).basicOpen_of_isUnit (Units.isUnit _)] at e
  have hp' : p ∈ (M.pull x).U fun _ => k := (pull_U M x fun _ => k).ge hk
  have h2 : p ∈ (Sp T).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) :=
    (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).ge hp
  exact Opens.mem_iSup.2 ⟨k, (e.ge ⟨⟨hp', h2⟩, hp'⟩).2⟩

variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : Z ⟶ Sp R}

/- English proof (translation)
Use `top_le_iff.1 fun z _ => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_chart H.1 z`. Establish `ht : ⊤ ≤ Z.fromSpecResidueField z ⁻¹ᵁ M.U k` using `fun p _ => by`. Express the relevant statement in the definitionally equal form `Z.fromSpecResidueField z p ∈ M.U k`. Rewrite using `[Scheme.fromSpecResidueField_apply]` and apply the resulting hypothesis.

Establish `hc` using `secCoord_chart (th := th) (T := Z.residueField z) H.1 (Z.fromSpecResidueField z) k ht`. Establish `hs` using `(H.2.1 _ _ _ _ (comp_str s _ _ ht) hc).1`. Set `p : Sp (Z.residueField z)` to `IsLocalRing.closedPoint (Z.residueField z)`. Assume the negation of the conclusion as `hz`. Use `p.isPrime.ne_top (top_le_iff.1 (hs.ge.trans (Ideal.span_le.2 ?_)))` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Assume the negation of the conclusion as `hi`. Use `mem_locus H.1 hc hi` as an intermediate fact. Use `erw [Scheme.fromSpecResidueField_apply] at this`. Conclude with `hz (Opens.mem_iSup.2 ⟨i, this⟩)`.
-/
theorem iSup_locus (H : ProjRep I s M th) : ⨆ i, nonzeroLocus (th i) = ⊤ := by
  refine top_le_iff.1 fun z _ => ?_
  obtain ⟨k, hk⟩ := exists_chart H.1 z
  have ht : ⊤ ≤ Z.fromSpecResidueField z ⁻¹ᵁ M.U k := fun p _ => by
    change Z.fromSpecResidueField z p ∈ M.U k
    rwa [Scheme.fromSpecResidueField_apply]
  have hc := secCoord_chart (th := th) (T := Z.residueField z) H.1 (Z.fromSpecResidueField z) k ht
  have hs := (H.2.1 _ _ _ _ (comp_str s _ _ ht) hc).1
  let p : Sp (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  by_contra hz
  refine p.isPrime.ne_top (top_le_iff.1 (hs.ge.trans (Ideal.span_le.2 ?_)))
  rintro _ ⟨i, rfl⟩
  by_contra hi
  have := mem_locus H.1 hc hi
  erw [Scheme.fromSpecResidueField_apply] at this
  exact hz (Opens.mem_iSup.2 ⟨i, this⟩)

/- English proof (translation)
Use `set D := nonzeroLocus (th i) with hD`. Set `c : MvPolynomial σ R →+* Γ(Z, D)` to `MvPolynomial.eval₂Hom (baseRingHom s D).hom fun j => secRatio (th i) (th j)`. Set `J : Ideal (MvPolynomial σ R)` to `I ⊔ Ideal.span {MvPolynomial.X i - 1}`. Establish `hJ : ∀ F ∈ J, c F = 0`. Express the relevant statement in the definitionally equal form `J ≤ RingHom.ker c`.

Use `sup_le (fun F hF => eq_zero_of_ev _ fun T _ x h => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)` and prove the remaining obligations. Use `(H.2.1 _ _ _ _ (comp_str s x D h) (secCoord_ratio x i h)).2 F hF` as an intermediate fact. Conclude with `(MvPolynomial.eval₂_comp_left (ev x D h).hom _ _ F).trans this`. Simplify using `[c, RingHom.mem_ker]`. Set `ρ : CommRingCat.of (MvPolynomial σ R ⧸ J) ⟶ Γ(Z, D)` to `CommRingCat.ofHom (Ideal.Quotient.lift J c hJ)`.

Establish `hXi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1` using `Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))`. Take `⟨φ, ⟨hφ, hv⟩, -⟩` from `H.2.2 _ ((Ideal.Quotient.mk J).comp MvPolynomial.C) (fun j => Ideal.Quotient.mk J (MvPolynomial.X j)) ((Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨i, hXi⟩)) fun F hF => by`. Use `MvPolynomial.eval₂_comp_left (Ideal.Quotient.mk J) MvPolynomial.C MvPolynomial.X F` as an intermediate fact. Rewrite `this` using `[MvPolynomial.eval₂_eta]`. Conclude with `this.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))`.

Establish `hφD : ⊤ ≤ φ ⁻¹ᵁ D` using `fun p _ => mem_locus H.1 hv (by`. Rewrite using `[hXi]`. Conclude with `(Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)`. Set `φ' : Sp (MvPolynomial σ R ⧸ J) ⟶ D.toScheme` to `IsOpenImmersion.lift D.ι φ (by`. Introduce and unpack `_ ⟨p, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hφD trivial)`. Establish `hφ' : φ' ≫ D.ι = φ` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hin : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme), ⊤ ≤ (y ≫ D.ι) ⁻¹ᵁ D` using `fun T _ y p _ => (y p).2`. Establish `e₁ : φ' ≫ D.toSpecΓ ≫ Spec.map ρ = 𝟙 _`.

Rewrite using `[← Category.assoc, comp_toSpecΓ D φ' (hin _ φ'), ← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Establish `hc` using `secCoord_ratio (φ' ≫ D.ι) i (hin _ φ')`. Establish `hs` using `comp_str s (φ' ≫ D.ι) D (hin _ φ')`. Generalize the expression as in `hin _ φ' = w at hc hs ⊢`.

Rewrite `w` using `[hφ']`. Simplify using `only [hφ'] at hc hs ⊢`. Take `⟨u, hu⟩` from `Coord.unique H.1 hv hc`. Establish `hu1 : (u : MvPolynomial σ R ⧸ J) = 1`. Use `hu i` as an intermediate fact.

Rewrite `this` using `[secRatio_self, map_one, hXi, _root_.mul_one]`. Conclude with `this.symm`. Establish `hb` using `congrArg CommRingCat.Hom.hom (Spec.map_injective (hs.symm.trans hφ))`. Use `CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun j => ?_))` and prove the remaining obligations. Conclude with `(congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_C _ _ a)).trans (DFunLike.congr_fun hb a)`.

Conclude with `(congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_X' _ _ j)).trans ((hu j).trans (by rw [hu1, _root_.one_mul]; rfl))`. Establish `e₂ : (D.toSpecΓ ≫ Spec.map ρ) ≫ φ' = 𝟙 _`. Rewrite using `[← cancel_mono D.ι, Category.assoc, hφ', Category.id_comp]`. Use `D.toScheme.affineCover.hom_ext _ _ fun a => ?_` and prove the remaining obligations. Establish `key : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme), y ≫ (D.toSpecΓ ≫ Spec.map ρ) ≫ φ = y ≫ D.ι` using `fun T _ y => by`.

Establish `hc` using `secCoord_ratio (y ≫ D.ι) i (hin _ y)`. Establish `hs` using `comp_str s (y ≫ D.ι) D (hin _ y)`. Take `⟨h₁, h₂⟩` from `H.2.1 _ _ _ _ hs hc`. Use `(H.2.2 _ _ _ h₁ h₂).unique ?_ ⟨hs, hc⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc, comp_toSpecΓ D y (hin _ y), ← Spec.map_comp]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Category.assoc, hφ, ← Spec.map_comp]`. Use `congr 1`. Use `CommRingCat.hom_ext (RingHom.ext fun a => ?_)` and prove the remaining obligations. Conclude with `congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_C _ _ a)`.

Establish `e : (fun j => (ev (y ≫ D.ι) D (hin _ y)).hom (secRatio (th i) (th j))) = fun j => (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom (Ideal.Quotient.mk J (MvPolynomial.X j))` using `funext fun j => congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_X' (baseRingHom s D).hom (fun j => secRatio (th i) (th j)) j).symm`. Conclude with `e ▸ Coord.baseChange hv (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom`. Conclude with `key _ (D.toScheme.affineCover.f a)`. Establish `hiso : IsIso (D.toSpecΓ ≫ Spec.map ρ)` using `⟨φ', e₂, e₁⟩`. Establish `ha : IsAffine D.toScheme` using `.of_isIso (D.toSpecΓ ≫ Spec.map ρ)`.

Establish `ha' : IsAffineOpen D` using `ha`. Use `⟨ha', ?_⟩` and prove the remaining obligations. Establish `h1 : IsIso D.toSpecΓ` using `inferInstanceAs (IsIso ha'.isoSpec.hom)`. Establish `h2 : IsIso (Spec.map ρ)` using `IsIso.of_isIso_comp_left D.toSpecΓ _`. Conclude with `(isIso_SpecMap_iff.1 h2).2.comp Ideal.Quotient.mk_surjective`.
-/
theorem chart_affine (H : ProjRep I s M th) (i : σ) : IsAffineOpen (nonzeroLocus (th i)) ∧ Function.Surjective
    (MvPolynomial.eval₂Hom (baseRingHom s (nonzeroLocus (th i))).hom fun j => secRatio (th i) (th j)) := by
  set D := nonzeroLocus (th i) with hD
  let c : MvPolynomial σ R →+* Γ(Z, D) :=
    MvPolynomial.eval₂Hom (baseRingHom s D).hom fun j => secRatio (th i) (th j)
  let J : Ideal (MvPolynomial σ R) := I ⊔ Ideal.span {MvPolynomial.X i - 1}
  have hJ : ∀ F ∈ J, c F = 0 := by
    change J ≤ RingHom.ker c
    refine sup_le (fun F hF => eq_zero_of_ev _ fun T _ x h => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    · have := (H.2.1 _ _ _ _ (comp_str s x D h) (secCoord_ratio x i h)).2 F hF
      exact (MvPolynomial.eval₂_comp_left (ev x D h).hom _ _ F).trans this
    · simp [c, RingHom.mem_ker]
  let ρ : CommRingCat.of (MvPolynomial σ R ⧸ J) ⟶ Γ(Z, D) := CommRingCat.ofHom (Ideal.Quotient.lift J c hJ)
  have hXi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1 :=
    Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨φ, ⟨hφ, hv⟩, -⟩ := H.2.2 _ ((Ideal.Quotient.mk J).comp MvPolynomial.C)
    (fun j => Ideal.Quotient.mk J (MvPolynomial.X j))
    ((Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨i, hXi⟩)) fun F hF => by
      have := MvPolynomial.eval₂_comp_left (Ideal.Quotient.mk J) MvPolynomial.C MvPolynomial.X F
      rw [MvPolynomial.eval₂_eta] at this
      exact this.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))
  have hφD : ⊤ ≤ φ ⁻¹ᵁ D := fun p _ => mem_locus H.1 hv (by
    rw [hXi]; exact (Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)
  let φ' : Sp (MvPolynomial σ R ⧸ J) ⟶ D.toScheme := IsOpenImmersion.lift D.ι φ (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hφD trivial)
  have hφ' : φ' ≫ D.ι = φ := IsOpenImmersion.lift_fac _ _ _
  have hin : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme), ⊤ ≤ (y ≫ D.ι) ⁻¹ᵁ D := fun T _ y p _ => (y p).2
  have e₁ : φ' ≫ D.toSpecΓ ≫ Spec.map ρ = 𝟙 _ := by
    rw [← Category.assoc, comp_toSpecΓ D φ' (hin _ φ'), ← Spec.map_comp, ← Spec.map_id]
    congr 1
    have hc := secCoord_ratio (φ' ≫ D.ι) i (hin _ φ')
    have hs := comp_str s (φ' ≫ D.ι) D (hin _ φ')
    generalize hin _ φ' = w at hc hs ⊢
    rw [hφ'] at w
    simp only [hφ'] at hc hs ⊢
    obtain ⟨u, hu⟩ := Coord.unique H.1 hv hc
    have hu1 : (u : MvPolynomial σ R ⧸ J) = 1 := by
      have := hu i
      rw [secRatio_self, map_one, hXi, _root_.mul_one] at this
      exact this.symm
    have hb := congrArg CommRingCat.Hom.hom (Spec.map_injective (hs.symm.trans hφ))
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun j => ?_))
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_C _ _ a)).trans (DFunLike.congr_fun hb a)
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_X' _ _ j)).trans
        ((hu j).trans (by rw [hu1, _root_.one_mul]; rfl))
  have e₂ : (D.toSpecΓ ≫ Spec.map ρ) ≫ φ' = 𝟙 _ := by
    rw [← cancel_mono D.ι, Category.assoc, hφ', Category.id_comp]
    refine D.toScheme.affineCover.hom_ext _ _ fun a => ?_
    have key : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme),
        y ≫ (D.toSpecΓ ≫ Spec.map ρ) ≫ φ = y ≫ D.ι := fun T _ y => by
      have hc := secCoord_ratio (y ≫ D.ι) i (hin _ y)
      have hs := comp_str s (y ≫ D.ι) D (hin _ y)
      obtain ⟨h₁, h₂⟩ := H.2.1 _ _ _ _ hs hc
      refine (H.2.2 _ _ _ h₁ h₂).unique ?_ ⟨hs, hc⟩
      rw [← Category.assoc, ← Category.assoc, comp_toSpecΓ D y (hin _ y), ← Spec.map_comp]
      constructor
      · rw [Category.assoc, hφ, ← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
        exact congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_C _ _ a)
      · have e : (fun j => (ev (y ≫ D.ι) D (hin _ y)).hom (secRatio (th i) (th j))) = fun j =>
            (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom (Ideal.Quotient.mk J (MvPolynomial.X j)) := funext fun j =>
          congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_X' (baseRingHom s D).hom (fun j => secRatio (th i) (th j)) j).symm
        exact e ▸ Coord.baseChange hv (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom
    exact key _ (D.toScheme.affineCover.f a)
  have hiso : IsIso (D.toSpecΓ ≫ Spec.map ρ) := ⟨φ', e₂, e₁⟩
  have ha : IsAffine D.toScheme := .of_isIso (D.toSpecΓ ≫ Spec.map ρ)
  have ha' : IsAffineOpen D := ha
  refine ⟨ha', ?_⟩
  have h1 : IsIso D.toSpecΓ := inferInstanceAs (IsIso ha'.isoSpec.hom)
  have h2 : IsIso (Spec.map ρ) := IsIso.of_isIso_comp_left D.toSpecΓ _
  exact (isIso_SpecMap_iff.1 h2).2.comp Ideal.Quotient.mk_surjective

end GlobalTheory.ZM.Amp

namespace GlobalTheory.ZM
open GlobalTheory.ProjSpace Amp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

/- English proof (translation)
Introduce `R σ _ _ I Z M th H`. Establish `hp : IsProjOver Z.hom`. Consider the cases of `isEmpty_or_nonempty σ with`. Consider the case `inl h => exact isProjOver_of_disjoint_cover Z.hom _ (iSup_locus H) (fun i => isEmptyElim i) fun i => isEmptyElim i`. Consider the case `inr h`.

Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin σ`. Take `_ | m` from `n`. Conclude with `(h.elim fun i => (e i).elim0)`. Establish `hs : ⨆ i, nonzeroLocus (th (e.symm i)) = ⊤` using `(e.symm.iSup_comp (g := fun i => nonzeroLocus (th i))).trans (iSup_locus H)`. Use `⟨m, toProj Z.hom (fun i => th (e.symm i)) hs, (isClosedImmersion_toProj_iff _ _ hs).2 fun i => ⟨(chart_affine H _).1, fun a => ?_⟩, toProj_str _ _ _⟩` and prove the remaining obligations.

Take `⟨F, hF⟩` from `(chart_affine H (e.symm i)).2 a`. Use `⟨MvPolynomial.rename e F, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂Hom_rename, ← hF]`. Use `congr 2`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Establish `hpr : IsProper Z.hom` using `((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1`. Use `⟨hp, hpr, (relAmple_iff_isAmpleLB_of_isAffine Z H.1).2 ?_⟩` and prove the remaining obligations. Establish `e : ∀ i, nonzeroLocus (secToPow (th i) 1) = nonzeroLocus (th i)` using `fun i => nonzeroLocus_secToPow (th i) le_rfl`. Conclude with `isAmpleLB_of_cover H.1 le_rfl (fun i => secToPow (th i) 1) ((iSup_congr e).trans (iSup_locus H)) fun i => (e i).symm ▸ (chart_affine H i).1`.
-/
theorem projRep_projective_ample : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  intro R σ _ _ I Z M th H
  have hp : IsProjOver Z.hom := by
    cases isEmpty_or_nonempty σ with
    | inl h => exact isProjOver_of_disjoint_cover Z.hom _ (iSup_locus H) (fun i => isEmptyElim i) fun i => isEmptyElim i
    | inr h =>
      obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
      obtain _ | m := n
      · exact (h.elim fun i => (e i).elim0)
      have hs : ⨆ i, nonzeroLocus (th (e.symm i)) = ⊤ :=
        (e.symm.iSup_comp (g := fun i => nonzeroLocus (th i))).trans (iSup_locus H)
      refine ⟨m, toProj Z.hom (fun i => th (e.symm i)) hs, (isClosedImmersion_toProj_iff _ _ hs).2 fun i =>
        ⟨(chart_affine H _).1, fun a => ?_⟩, toProj_str _ _ _⟩
      obtain ⟨F, hF⟩ := (chart_affine H (e.symm i)).2 a
      refine ⟨MvPolynomial.rename e F, ?_⟩
      rw [MvPolynomial.eval₂Hom_rename, ← hF]
      congr 2
      funext j
      simp
  have hpr : IsProper Z.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨hp, hpr, (relAmple_iff_isAmpleLB_of_isAffine Z H.1).2 ?_⟩
  have e : ∀ i, nonzeroLocus (secToPow (th i) 1) = nonzeroLocus (th i) := fun i =>
    nonzeroLocus_secToPow (th i) le_rfl
  exact isAmpleLB_of_cover H.1 le_rfl (fun i => secToPow (th i) 1) ((iSup_congr e).trans (iSup_locus H))
    fun i => (e i).symm ▸ (chart_affine H i).1

end GlobalTheory.ZM
end
