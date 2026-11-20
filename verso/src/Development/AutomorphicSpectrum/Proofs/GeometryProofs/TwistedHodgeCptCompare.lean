import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieTw

section Rings

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

/- English proof (translation)
Unfold `spMap`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem sp_comp (f : R' →+* R'') (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dual_comp_alg (i : R →+* R') :
    (dualMap i).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp i := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply the tactic sequence `ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dual_comp_eps (i : R →+* R') (a : R) :
    (dualMap i).comp (epsMul a) = (epsMul (i a)).comp (dualMap i) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply the tactic sequence `ext s <;> simp [dualMap, h]`.
-/
theorem dual_comp_id (i : R →+* R') (j : R' →+* R) (h : ∀ a, j (i a) = a) :
    (dualMap j).comp (dualMap i) = RingHom.id _ := by
  ext s <;> simp [dualMap, h]

/- English proof (translation)
Rewrite using `[sp_comp, sp_comp, dual_comp_eps]`.
-/
theorem sp_eps_dual (i : R →+* R') (a : R) :
    spMap (epsMul (i a)) ≫ spMap (dualMap i) = spMap (dualMap i) ≫ spMap (epsMul a) := by
  rw [sp_comp, sp_comp, dual_comp_eps]

/- English proof (translation)
Rewrite using `[sp_comp, sp_comp, dual_comp_alg]`.
-/
theorem sp_dual_alg (i : R →+* R') :
    spMap (dualMap i) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap i := by
  rw [sp_comp, sp_comp, dual_comp_alg]

/- English proof (translation)
The claim follows from `LieMove.epsMul_comp_alg c`.
-/
theorem sp_eps_alg (c : R) :
    spMap (epsMul c) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) :=
  LieMove.epsMul_comp_alg c

/- English proof (translation)
Establish `e'` using `congrArg (fun w => spMap (dualMap i) ≫ w) e`. Simplify using `only [← Category.assoc, sp_comp, dual_comp_id j i h] at e'`. Establish `hid : spMap (RingHom.id (DualNumber R')) = 𝟙 _`. Unfold `spMap`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`.

Simplify `e'` using `[hid]`.
-/
theorem sp_dual_cancel (i : R →+* R') (j : R' →+* R) (h : ∀ a, i (j a) = a) {T : Scheme.{0}}
    {p q : Sp (DualNumber R') ⟶ T} (e : spMap (dualMap j) ≫ p = spMap (dualMap j) ≫ q) : p = q := by
  have e' := congrArg (fun w => spMap (dualMap i) ≫ w) e
  simp only [← Category.assoc, sp_comp, dual_comp_id j i h] at e'
  have hid : spMap (RingHom.id (DualNumber R')) = 𝟙 _ := by
    unfold spMap
    rw [CommRingCat.ofHom_id, Spec.map_id]
  simpa [hid] using e'

end Rings

section Epi

variable {K L : Type} [Field K] [Field L]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `h0`. Establish `hu : IsUnit x` using `TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h0)`. Conclude with `p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)`.

Introduce `h0`. Establish `h2 : x * x = 0`. Apply the tactic sequence `ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]`. Establish `: x * x ∈ p.asIdeal` using `by rw [h2]; exact p.asIdeal.zero_mem`. Apply the tactic sequence `rcases p.2.mem_or_mem this with h | h <;> exact h`.
-/
theorem mem_iff_fst (p : PrimeSpectrum (DualNumber K)) (x : DualNumber K) :
    x ∈ p.asIdeal ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h0)
    exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  · intro h0
    have h2 : x * x = 0 := by
      ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    have : x * x ∈ p.asIdeal := by rw [h2]; exact p.asIdeal.zero_mem
    rcases p.2.mem_or_mem this with h | h <;> exact h

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => by rw [mem_iff_fst p, mem_iff_fst q])⟩`.
-/
theorem dual_sub : Subsingleton (PrimeSpectrum (DualNumber K)) :=
  ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => by rw [mem_iff_fst p, mem_iff_fst q])⟩

/- English proof (translation)
Use `⟨fun {W} u v h => ?_⟩` and prove the remaining obligations. Use `haveI : Subsingleton (Sp (DualNumber K)) := (dual_sub : Subsingleton (PrimeSpectrum (DualNumber K)))`. Take `⟨y⟩ : Nonempty (PrimeSpectrum (DualNumber L))` from `inferInstance`. Set `y' : Sp (DualNumber L)` to `y`. Set `pt : Sp (DualNumber K)` to `spMap (dualMap f) y'`.

Establish `huv : u pt = v pt`. Use `congrArg (fun w => w y') h` as an intermediate fact. Simplify using `using this`. Take `⟨U, hU, hmem, -⟩` from `exists_isAffineOpen_mem_and_subset (x := u pt) (U := ⊤) trivial`. Establish `hu : Set.range u ⊆ Set.range U.ι`.

Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Subsingleton.elim z pt]`. Simplify using `using hmem`. Establish `hv : Set.range v ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨z, rfl⟩`.

Rewrite using `[Subsingleton.elim z pt, ← huv]`. Simplify using `using hmem`. Use `haveI : IsAffine U.toScheme := hU`. Establish `hu'` using `IsOpenImmersion.lift_fac U.ι u hu`. Establish `hv'` using `IsOpenImmersion.lift_fac U.ι v hv`.

Rewrite using `[← hu', ← hv']`. Use `congr 1`. Apply `ext_of_isAffine` to reduce the goal to its premises. Establish `e : spMap (dualMap f) ≫ IsOpenImmersion.lift U.ι u hu = spMap (dualMap f) ≫ IsOpenImmersion.lift U.ι v hv`. Rewrite using `[← cancel_mono U.ι, Category.assoc, Category.assoc, hu', hv', h]`.

Establish `e'` using `congrArg Scheme.Hom.appTop e`. Rewrite `e'` using `[Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]`. Establish `hinj : Mono (spMap (dualMap f)).appTop`. Establish `hn` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap f))`. Establish `hm : Mono (CommRingCat.ofHom (dualMap f))`.

Apply `ConcreteCategory.mono_of_injective` to reduce the goal to its premises. Introduce `a b hab`. Establish `h1` using `congrArg TrivSqZeroExt.fst hab`. Establish `h2` using `congrArg TrivSqZeroExt.snd hab`. Use `ext`.

Conclude with `f.injective (by simpa [dualMap] using h1)`. Conclude with `f.injective (by simpa [dualMap] using h2)`. Establish `hm2 : Mono ((spMap (dualMap f)).appTop ≫ (Scheme.ΓSpecIso _).hom)`. Rewrite using `[show (spMap (dualMap f)).appTop ≫ (Scheme.ΓSpecIso _).hom = _ from hn]`. Conclude with `mono_comp _ _`.

Conclude with `mono_of_mono _ (Scheme.ΓSpecIso _).hom`. Conclude with `(cancel_mono _).1 e'`.
-/
theorem dual_epi (f : K →+* L) : Epi (spMap (dualMap f)) := by
  refine ⟨fun {W} u v h => ?_⟩
  haveI : Subsingleton (Sp (DualNumber K)) := (dual_sub : Subsingleton (PrimeSpectrum (DualNumber K)))
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum (DualNumber L)) := inferInstance
  let y' : Sp (DualNumber L) := y
  let pt : Sp (DualNumber K) := spMap (dualMap f) y'
  have huv : u pt = v pt := by
    have := congrArg (fun w => w y') h
    simpa using this
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (x := u pt) (U := ⊤) trivial
  have hu : Set.range u ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z pt]
    simpa using hmem
  have hv : Set.range v ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z pt, ← huv]
    simpa using hmem
  haveI : IsAffine U.toScheme := hU
  have hu' := IsOpenImmersion.lift_fac U.ι u hu
  have hv' := IsOpenImmersion.lift_fac U.ι v hv
  rw [← hu', ← hv']
  congr 1
  apply ext_of_isAffine
  have e : spMap (dualMap f) ≫ IsOpenImmersion.lift U.ι u hu = spMap (dualMap f) ≫ IsOpenImmersion.lift U.ι v hv := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hu', hv', h]
  have e' := congrArg Scheme.Hom.appTop e
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e'
  have hinj : Mono (spMap (dualMap f)).appTop := by
    have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap f))
    have hm : Mono (CommRingCat.ofHom (dualMap f)) := by
      apply ConcreteCategory.mono_of_injective
      intro a b hab
      have h1 := congrArg TrivSqZeroExt.fst hab
      have h2 := congrArg TrivSqZeroExt.snd hab
      ext
      · exact f.injective (by simpa [dualMap] using h1)
      · exact f.injective (by simpa [dualMap] using h2)
    have hm2 : Mono ((spMap (dualMap f)).appTop ≫ (Scheme.ΓSpecIso _).hom) := by
      rw [show (spMap (dualMap f)).appTop ≫ (Scheme.ΓSpecIso _).hom = _ from hn]
      exact mono_comp _ _
    exact mono_of_mono _ (Scheme.ΓSpecIso _).hom
  exact (cancel_mono _).1 e'

end Epi

section Models

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {G : Over S} [GrpObj G]

def castPt {x y : Sp R ⟶ S} {L : Type} [AddCommGroup L] [Module R L] (h : x = y) (M : LieModel G x L) :
    LieModel G y L := h ▸ M

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem castPt_left {x y : Sp R ⟶ S} {L : Type} [AddCommGroup L] [Module R L] (h : x = y) (M : LieModel G x L)
    (e : L) : ((castPt h M).pt e).left = (M.pt e).left := by
  subst h
  rfl

/- English proof (translation)
Use `choose f hf using fun e => M'.onto (M.pt e) (M.tan e)`. Use `choose g hg using fun e => M.onto (M'.pt e) (M'.tan e)`. Use `⟨{ toFun := f, invFun := g, left_inv := fun e => M.inj (by rw [hg, hf]), right_inv := fun e => M'.inj (by rw [hf, hg]), map_add' := fun a b => M'.inj (by rw [hf, M'.add, hf, hf, M.add]) }, fun a e => ?_, hf⟩` and prove the remaining obligations. Use `show f (a • e) = a • f e`. Apply `M'.inj` to reduce the goal to its premises.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hf, M.smul, M'.smul, hf]`.
-/
theorem exists_equiv {x : Sp R ⟶ S} {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (M : LieModel G x L) (M' : LieModel G x L') :
    ∃ θ : L ≃+ L', (∀ (a : R) e, θ (a • e) = a • θ e) ∧ ∀ e, M'.pt (θ e) = M.pt e := by
  choose f hf using fun e => M'.onto (M.pt e) (M.tan e)
  choose g hg using fun e => M.onto (M'.pt e) (M'.tan e)
  refine ⟨{ toFun := f, invFun := g, left_inv := fun e => M.inj (by rw [hg, hf]),
            right_inv := fun e => M'.inj (by rw [hf, hg]),
            map_add' := fun a b => M'.inj (by rw [hf, M'.add, hf, hf, M.add]) }, fun a e => ?_, hf⟩
  show f (a • e) = a • f e
  apply M'.inj
  apply Over.OverMorphism.ext
  rw [hf, M.smul, M'.smul, hf]

variable (ψ : R' ≃+* R) (x' : Sp R' ⟶ S)

/- English proof (translation)
Rewrite using `[← Category.assoc, sp_comp]`. Establish `: ψ.symm.toRingHom.comp ψ.toRingHom = RingHom.id R'`. Use extensionality with `a`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Establish `hid : spMap (RingHom.id R') = 𝟙 _`. Unfold `spMap`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`. Rewrite using `[hid, Category.id_comp]`.
-/
theorem symm_sp : x' = spMap ψ.symm.toRingHom ≫ spMap ψ.toRingHom ≫ x' := by
  rw [← Category.assoc, sp_comp]
  have : ψ.symm.toRingHom.comp ψ.toRingHom = RingHom.id R' := by
    ext a
    simp
  rw [this]
  have hid : spMap (RingHom.id R') = 𝟙 _ := by
    unfold spMap
    rw [CommRingCat.ofHom_id, Spec.map_id]
  rw [hid, Category.id_comp]

def toEps : epsAt x' ⟶ epsAt (spMap ψ.toRingHom ≫ x') :=
  LieJ.epsOver (spMap ψ.toRingHom ≫ x') x' ψ.symm.toRingHom (symm_sp ψ x')

def ofEps : epsAt (spMap ψ.toRingHom ≫ x') ⟶ epsAt x' :=
  LieJ.epsOver x' (spMap ψ.toRingHom ≫ x') ψ.toRingHom rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toEps_left : (toEps ψ x').left = spMap (dualMap ψ.symm.toRingHom) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofEps_left : (ofEps ψ x').left = spMap (dualMap ψ.toRingHom) := rfl

/- English proof (translation)
Substitute `h` using the available equality. Unfold `spMap`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`.
-/
theorem sp_id_of {A : Type} [CommRing A] {f : A →+* A} (h : f = RingHom.id A) : spMap f = 𝟙 _ := by
  subst h
  unfold spMap
  rw [CommRingCat.ofHom_id, Spec.map_id]

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, toEps_left, ofEps_left, sp_comp, sp_id_of (dual_comp_id ψ.toRingHom ψ.symm.toRingHom (fun a => by simp))]`. Both sides reduce to the same expression.
-/
theorem to_of : toEps ψ x' ≫ ofEps ψ x' = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, toEps_left, ofEps_left, sp_comp,
    sp_id_of (dual_comp_id ψ.toRingHom ψ.symm.toRingHom (fun a => by simp))]
  rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, toEps_left, ofEps_left, sp_comp, sp_id_of (dual_comp_id ψ.symm.toRingHom ψ.toRingHom (fun a => by simp))]`. Both sides reduce to the same expression.
-/
theorem of_to : ofEps ψ x' ≫ toEps ψ x' = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, toEps_left, ofEps_left, sp_comp,
    sp_id_of (dual_comp_id ψ.symm.toRingHom ψ.toRingHom (fun a => by simp))]
  rfl

def ringModel {L : Type} [AddCommGroup L] [Module R L] [Module R' L] (hL : ∀ (a : R') (e : L), a • e = ψ a • e)
    (M : LieModel G (spMap ψ.toRingHom ≫ x') L) : LieModel G x' L where
  pt e := toEps ψ x' ≫ M.pt e
  tan e := LieJ.isTanAt_epsOver G _ _ _ _ _ (M.tan e)
  inj a b e := M.inj (by
    have h2 : ofEps ψ x' ≫ toEps ψ x' ≫ M.pt a = ofEps ψ x' ≫ toEps ψ x' ≫ M.pt b :=
      congrArg (fun w => ofEps ψ x' ≫ w) e
    rwa [← Category.assoc, ← Category.assoc, of_to, Category.id_comp, Category.id_comp] at h2)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto (ofEps ψ x' ≫ v) (LieJ.isTanAt_epsOver G _ _ _ _ _ t)
    exact ⟨e, by rw [he, ← Category.assoc, to_of, Category.id_comp]⟩
  add a b := by rw [M.add, comp_mul]
  smul c e := by
    rw [hL, Over.comp_left, Over.comp_left, M.smul, toEps_left]
    have h := sp_eps_dual ψ.symm.toRingHom (ψ c)
    have hc : ψ.symm.toRingHom (ψ c) = c := by simp
    rw [hc] at h
    show spMap _ ≫ spMap _ ≫ _ = spMap _ ≫ spMap _ ≫ _
    rw [← Category.assoc, ← h, Category.assoc]

/- English proof (translation)
Establish `: ofEps ψ x' ≫ (ringModel ψ x' hL M).pt e = M.pt e` using `by show ofEps ψ x' ≫ toEps ψ x' ≫ M.pt e = _`. Rewrite using `[← Category.assoc, of_to, Category.id_comp]`. Conclude with `congrArg (fun w => w.left) this`.
-/
theorem ringModel_left {L : Type} [AddCommGroup L] [Module R L] [Module R' L]
    (hL : ∀ (a : R') (e : L), a • e = ψ a • e) (M : LieModel G (spMap ψ.toRingHom ≫ x') L) (e : L) :
    spMap (dualMap ψ.toRingHom) ≫ ((ringModel ψ x' hL M).pt e).left = (M.pt e).left := by
  have : ofEps ψ x' ≫ (ringModel ψ x' hL M).pt e = M.pt e := by
    show ofEps ψ x' ≫ toEps ψ x' ≫ M.pt e = _
    rw [← Category.assoc, of_to, Category.id_comp]
  exact congrArg (fun w => w.left) this

end Models

section Cart

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[Category.assoc, ← ha, ← Category.assoc, h, Category.assoc]`. Introduce `h`. Use `hp.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, ha, Category.assoc, ← Category.assoc, h]`. Rewrite using `[Category.assoc, Over.w a₁, Category.assoc, hr]`.
-/
theorem cart_eig {S₁ S₂ : Scheme.{0}} {G₁ : Over S₁} {G₂ : Over S₂} {f : S₁ ⟶ S₂} {φ : G₁.left ⟶ G₂.left}
    (hp : IsPullback φ G₁.hom G₂.hom f) {T : Scheme.{0}} (a₁ : G₁ ⟶ G₁) (a₂ : G₂.left ⟶ G₂.left)
    (ha : a₁.left ≫ φ = φ ≫ a₂) (p : T ⟶ G₁.left) (r : T ⟶ T) (hr : r ≫ p ≫ G₁.hom = p ≫ G₁.hom) :
    p ≫ a₁.left = r ≫ p ↔ (p ≫ φ) ≫ a₂ = r ≫ p ≫ φ := by
  constructor
  · intro h
    rw [Category.assoc, ← ha, ← Category.assoc, h, Category.assoc]
  · intro h
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, ha, Category.assoc, ← Category.assoc, h]
    · rw [Category.assoc, Over.w a₁, Category.assoc, hr]

/- English proof (translation)
Rewrite using `[hp, ← Category.assoc, sp_eps_alg]`.
-/
theorem eps_base {R : Type} [CommRing R] {T B : Scheme.{0}} (p : Sp (DualNumber R) ⟶ T) (h : T ⟶ B) (y : Sp R ⟶ B)
    (hp : p ≫ h = spMap (algebraMap R (DualNumber R)) ≫ y) (c : R) :
    spMap (epsMul c) ≫ p ≫ h = p ≫ h := by
  rw [hp, ← Category.assoc, sp_eps_alg]

end Cart

section Geo

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem sp_inj {R R' : Type} [CommRing R] [CommRing R'] {f g : R →+* R'} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage w).hom, by unfold spMap; simp⟩`.
-/
theorem exists_sp {R R' : Type} [CommRing R] [CommRing R'] (w : Sp R ⟶ Sp R') : ∃ f : R' →+* R, spMap f = w :=
  ⟨(Spec.preimage w).hom, by unfold spMap; simp⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

/- English proof (translation)
Substitute `hξ hξ'` using the available equality. Establish `hY : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ` using `Y.m.cart`. Establish `hY' : IsGrpPullback Y'.oF.t.G Y'.t.G Y'.j Y'.m.φ` using `Y'.m.cart`. Establish `c1` using `Y.m0.toSABMap.cart`. Establish `c2 : IsGrpPullback Xo.univ.t.G Xo.univ.t.G Φ.hom n.φ` using `n.cart`.

Establish `c3` using `Y'.m0.toSABMap.cart`. Set `N` to `LieMove.pullModel hY M`. Set `N1` to `LieMove.pushModel c1 N`. Set `N2` to `LieMove.pushModel c2 N1`. Establish `hz : (x₀ ≫ pullback.fst _ _) ≫ Φ.hom = (spMap ψ.toRingHom ≫ x₀') ≫ pullback.fst _ _`.

Rewrite using `[Category.assoc, Category.assoc, h1]`. Set `N2'` to `castPt hz N2`. Set `N3` to `LieMove.pullModel c3 N2'`. Use `letI : Module R' L := Module.compHom L ψ.toRingHom`. Set `N4` to `ringModel ψ x₀' (fun _ _ => rfl) N3`.

Set `N5` to `LieMove.pushModel hY' N4`. Take `⟨θ, hθ, hp⟩` from `exists_equiv N5 M'`. Use `⟨θ, fun a e => hθ a e, fun e => ⟨(N.pt e).left, (N4.pt e).left, LieMove.liftEps_left hY _, ?_, Over.w (N.pt e), Over.w (N4.pt e), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hp]`. Both sides reduce to the same expression.

Establish `e2 : spMap (dualMap ψ.toRingHom) ≫ (N4.pt e).left = (N3.pt e).left` using `ringModel_left ψ x₀' _ N3 e`. Rewrite using `[← Category.assoc, e2]`. Establish `e1 : (N3.pt e).left ≫ Y'.m0.toSABMap.φ = (N2'.pt e).left` using `LieMove.liftEps_left c3 _`. Rewrite using `[e1, castPt_left]`. Both sides reduce to the same expression.
-/
theorem core (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) {R R' : Type} [CommRing R] [CommRing R'] (ψ : R' ≃+* R)
    (x₀ : Sp R ⟶ Xo.XF c) (x₀' : Sp R' ⟶ Xo.XF c) (ξ : Sp R ⟶ Y.X) (ξ' : Sp R' ⟶ Y'.X)
    (hξ : ξ = x₀ ≫ Y.j) (hξ' : ξ' = x₀' ≫ Y'.j)
    (h1 : spMap ψ.toRingHom ≫ x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _ ≫ Φ.hom)
    {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R' L']
    (M : LieModel Y.t.G ξ L) (M' : LieModel Y'.t.G ξ' L') :
    ∃ θ : L ≃+ L', (∀ (a : R') e, θ (ψ a • e) = a • θ e) ∧ ∀ e,
      ∃ (u : Sp (DualNumber R) ⟶ Y.oF.t.G.left) (u₃ : Sp (DualNumber R') ⟶ Y'.oF.t.G.left),
        u ≫ Y.m.φ = (M.pt e).left ∧ u₃ ≫ Y'.m.φ = (M'.pt (θ e)).left ∧
        u ≫ Y.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x₀ ∧
        u₃ ≫ Y'.oF.t.G.hom = spMap (algebraMap R' (DualNumber R')) ≫ x₀' ∧
        spMap (dualMap ψ.toRingHom) ≫ u₃ ≫ Y'.m0.toSABMap.φ = u ≫ Y.m0.toSABMap.φ ≫ n.φ := by
  subst hξ hξ'
  have hY : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hY' : IsGrpPullback Y'.oF.t.G Y'.t.G Y'.j Y'.m.φ := Y'.m.cart
  have c1 := Y.m0.toSABMap.cart
  have c2 : IsGrpPullback Xo.univ.t.G Xo.univ.t.G Φ.hom n.φ := n.cart
  have c3 := Y'.m0.toSABMap.cart
  let N := LieMove.pullModel hY M
  let N1 := LieMove.pushModel c1 N
  let N2 := LieMove.pushModel c2 N1
  have hz : (x₀ ≫ pullback.fst _ _) ≫ Φ.hom = (spMap ψ.toRingHom ≫ x₀') ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, h1]
  let N2' := castPt hz N2
  let N3 := LieMove.pullModel c3 N2'
  letI : Module R' L := Module.compHom L ψ.toRingHom
  let N4 := ringModel ψ x₀' (fun _ _ => rfl) N3
  let N5 := LieMove.pushModel hY' N4
  obtain ⟨θ, hθ, hp⟩ := exists_equiv N5 M'
  refine ⟨θ, fun a e => hθ a e, fun e => ⟨(N.pt e).left, (N4.pt e).left, LieMove.liftEps_left hY _, ?_, Over.w (N.pt e),
    Over.w (N4.pt e), ?_⟩⟩
  · rw [hp]
    rfl
  · have e2 : spMap (dualMap ψ.toRingHom) ≫ (N4.pt e).left = (N3.pt e).left := ringModel_left ψ x₀' _ N3 e
    rw [← Category.assoc, e2]
    have e1 : (N3.pt e).left ≫ Y'.m0.toSABMap.φ = (N2'.pt e).left := LieMove.liftEps_left c3 _
    rw [e1, castPt_left]
    rfl

/- English proof (translation)
Establish `hm : ∀ b, ((u ≫ Y.m.φ) ≫ (Y.t.act.act b).left = spMap (epsMul (t b)) ≫ u ≫ Y.m.φ) ↔ (u ≫ Y.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act b).left = spMap (epsMul (t b)) ≫ u ≫ Y.m0.toSABMap.φ` using `fun b => (cart_eig Y.m.cart.1 (Y.oF.t.act.act b) _ (Y.m.act b) u _ (eps_base u _ x₀ hu _)).symm.trans (cart_eig Y.m0.toSABMap.cart.1 (Y.oF.t.act.act b) _ (Y.m0.toSABMap.act b) u _ (eps_base u _ x₀ hu _))`. Establish `hm' : ∀ a d, ((u₃ ≫ Y'.m.φ) ≫ (Y'.t.act.act a).left = spMap (epsMul d) ≫ u₃ ≫ Y'.m.φ) ↔ (u₃ ≫ Y'.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul d) ≫ u₃ ≫ Y'.m0.toSABMap.φ` using `fun a d => (cart_eig Y'.m.cart.1 (Y'.oF.t.act.act a) _ (Y'.m.act a) u₃ _ (eps_base u₃ _ x₀' hu₃ _)).symm.trans (cart_eig Y'.m0.toSABMap.cart.1 (Y'.oF.t.act.act a) _ (Y'.m0.toSABMap.act a) u₃ _ (eps_base u₃ _ x₀' hu₃ _))`. Establish `hb : (u ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x₀ ≫ pullback.fst _ _`. Rewrite using `[Category.assoc, Y.m0.toSABMap.cart.1.w, ← Category.assoc, hu, Category.assoc]`. Establish `hn : ∀ a d, ((u ≫ Y.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act (g.s a)).left = spMap (epsMul d) ≫ u ≫ Y.m0.toSABMap.φ) ↔ ((u ≫ Y.m0.toSABMap.φ) ≫ n.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul d) ≫ (u ≫ Y.m0.toSABMap.φ) ≫ n.φ` using `fun a d => cart_eig (G₁ := Xo.univ.t.G) (G₂ := Xo.univ.t.G) n.cart.1 (Xo.univ.t.act.act (g.s a)) _ (n.act a) _ _ (eps_base _ _ _ hb _)`.

Establish `hk : ∀ a d, (((u ≫ Y.m0.toSABMap.φ) ≫ n.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (ψ d)) ≫ (u ≫ Y.m0.toSABMap.φ) ≫ n.φ) ↔ (u₃ ≫ Y'.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul d) ≫ u₃ ≫ Y'.m0.toSABMap.φ`. Introduce `a d`. Establish `e0 : (u ≫ Y.m0.toSABMap.φ) ≫ n.φ = spMap (dualMap ψ.toRingHom) ≫ u₃ ≫ Y'.m0.toSABMap.φ`. Rewrite using `[hc]`. Conclude with `Category.assoc _ _ _`.

Establish `e1 : spMap (epsMul (ψ d)) ≫ spMap (dualMap ψ.toRingHom) ≫ u₃ ≫ Y'.m0.toSABMap.φ = spMap (dualMap ψ.toRingHom) ≫ spMap (epsMul d) ≫ u₃ ≫ Y'.m0.toSABMap.φ`. Establish `e2 : spMap (epsMul (ψ d)) ≫ spMap (dualMap ψ.toRingHom) = spMap (dualMap ψ.toRingHom) ≫ spMap (epsMul d)` using `sp_eps_dual ψ.toRingHom d`. Rewrite using `[← Category.assoc, e2, Category.assoc]`. Rewrite using `[e0, e1, Category.assoc (spMap (dualMap ψ.toRingHom))]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `sp_dual_cancel ψ.symm.toRingHom ψ.toRingHom (fun a => by simp) h`. Introduce `h`. Rewrite using `[h]`. Prove the components needed by the constructor for the conclusion.

Introduce `h a`. Establish `h1` using `(hm (g.s a)).1 (h (g.s a))`. Rewrite `h1` using `[← ht a]`. Conclude with `(hm' a _).2 ((hk a _).1 ((hn a _).1 h1))`. Introduce `h b`.

Take `⟨a, rfl⟩` from `g.s.surjective b`. Use `(hm _).2 ?_` and prove the remaining obligations. Rewrite using `[← ht a]`. Conclude with `(hn a _).2 ((hk a _).2 ((hm' a _).1 (h a)))`.
-/
theorem eig_iff (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) {R R' : Type} [CommRing R] [CommRing R'] (ψ : R' ≃+* R)
    (x₀ : Sp R ⟶ Xo.XF c) (x₀' : Sp R' ⟶ Xo.XF c)
    (u : Sp (DualNumber R) ⟶ Y.oF.t.G.left) (u₃ : Sp (DualNumber R') ⟶ Y'.oF.t.G.left)
    (hu : u ≫ Y.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x₀)
    (hu₃ : u₃ ≫ Y'.oF.t.G.hom = spMap (algebraMap R' (DualNumber R')) ≫ x₀')
    (hc : spMap (dualMap ψ.toRingHom) ≫ u₃ ≫ Y'.m0.toSABMap.φ = u ≫ Y.m0.toSABMap.φ ≫ n.φ)
    (t : 𝓞 E → R) (t' : 𝓞 E → R') (ht : ∀ a, ψ (t' a) = t (g.s a)) :
    (∀ a, (u ≫ Y.m.φ) ≫ (Y.t.act.act a).left = spMap (epsMul (t a)) ≫ u ≫ Y.m.φ) ↔
      ∀ a, (u₃ ≫ Y'.m.φ) ≫ (Y'.t.act.act a).left = spMap (epsMul (t' a)) ≫ u₃ ≫ Y'.m.φ := by
  have hm : ∀ b, ((u ≫ Y.m.φ) ≫ (Y.t.act.act b).left = spMap (epsMul (t b)) ≫ u ≫ Y.m.φ) ↔
      (u ≫ Y.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act b).left = spMap (epsMul (t b)) ≫ u ≫ Y.m0.toSABMap.φ := fun b =>
    (cart_eig Y.m.cart.1 (Y.oF.t.act.act b) _ (Y.m.act b) u _ (eps_base u _ x₀ hu _)).symm.trans
      (cart_eig Y.m0.toSABMap.cart.1 (Y.oF.t.act.act b) _ (Y.m0.toSABMap.act b) u _ (eps_base u _ x₀ hu _))
  have hm' : ∀ a d, ((u₃ ≫ Y'.m.φ) ≫ (Y'.t.act.act a).left = spMap (epsMul d) ≫ u₃ ≫ Y'.m.φ) ↔
      (u₃ ≫ Y'.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul d) ≫ u₃ ≫ Y'.m0.toSABMap.φ := fun a d =>
    (cart_eig Y'.m.cart.1 (Y'.oF.t.act.act a) _ (Y'.m.act a) u₃ _ (eps_base u₃ _ x₀' hu₃ _)).symm.trans
      (cart_eig Y'.m0.toSABMap.cart.1 (Y'.oF.t.act.act a) _ (Y'.m0.toSABMap.act a) u₃ _ (eps_base u₃ _ x₀' hu₃ _))
  have hb : (u ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom =
      spMap (algebraMap R (DualNumber R)) ≫ x₀ ≫ pullback.fst _ _ := by
    rw [Category.assoc, Y.m0.toSABMap.cart.1.w, ← Category.assoc, hu, Category.assoc]
  have hn : ∀ a d, ((u ≫ Y.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act (g.s a)).left =
        spMap (epsMul d) ≫ u ≫ Y.m0.toSABMap.φ) ↔
      ((u ≫ Y.m0.toSABMap.φ) ≫ n.φ) ≫ (Xo.univ.t.act.act a).left =
        spMap (epsMul d) ≫ (u ≫ Y.m0.toSABMap.φ) ≫ n.φ := fun a d =>
    cart_eig (G₁ := Xo.univ.t.G) (G₂ := Xo.univ.t.G) n.cart.1 (Xo.univ.t.act.act (g.s a)) _ (n.act a) _ _
      (eps_base _ _ _ hb _)
  have hk : ∀ a d, (((u ≫ Y.m0.toSABMap.φ) ≫ n.φ) ≫ (Xo.univ.t.act.act a).left =
        spMap (epsMul (ψ d)) ≫ (u ≫ Y.m0.toSABMap.φ) ≫ n.φ) ↔
      (u₃ ≫ Y'.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul d) ≫ u₃ ≫ Y'.m0.toSABMap.φ := by
    intro a d
    have e0 : (u ≫ Y.m0.toSABMap.φ) ≫ n.φ = spMap (dualMap ψ.toRingHom) ≫ u₃ ≫ Y'.m0.toSABMap.φ := by
      rw [hc]
      exact Category.assoc _ _ _
    have e1 : spMap (epsMul (ψ d)) ≫ spMap (dualMap ψ.toRingHom) ≫ u₃ ≫ Y'.m0.toSABMap.φ =
        spMap (dualMap ψ.toRingHom) ≫ spMap (epsMul d) ≫ u₃ ≫ Y'.m0.toSABMap.φ := by
      have e2 : spMap (epsMul (ψ d)) ≫ spMap (dualMap ψ.toRingHom) =
          spMap (dualMap ψ.toRingHom) ≫ spMap (epsMul d) := sp_eps_dual ψ.toRingHom d
      rw [← Category.assoc, e2, Category.assoc]
    rw [e0, e1, Category.assoc (spMap (dualMap ψ.toRingHom))]
    constructor
    · intro h
      exact sp_dual_cancel ψ.symm.toRingHom ψ.toRingHom (fun a => by simp) h
    · intro h
      rw [h]
  constructor
  · intro h a
    have h1 := (hm (g.s a)).1 (h (g.s a))
    rw [← ht a] at h1
    exact (hm' a _).2 ((hk a _).1 ((hn a _).1 h1))
  · intro h b
    obtain ⟨a, rfl⟩ := g.s.surjective b
    refine (hm _).2 ?_
    rw [← ht a]
    exact (hn a _).2 ((hk a _).2 ((hm' a _).1 (h a)))

variable {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

/- English proof (translation)
Establish `e₁ : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β`. Unfold `Model.j`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`. Establish `e₂ : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀` using `A.fn_over`. Apply `sp_inj` to reduce the goal to its premises.

Rewrite using `[← cancel_mono (spMap β), sp_comp, ← A.cst_over, ← sp_comp A.fn c₀, hc₀, ← Category.assoc A.ξ, e₂, h]`. Simplify using `only [Category.assoc]`. Rewrite using `[e₁]`.
-/
theorem cst_eq (A : HodgeCpt Y S y) (hm : Mono (spMap β)) (x₀ : Sp A.Ω₀ ⟶ Xo.XF c) (h : A.ξ₀ = x₀ ≫ Y.j)
    (c₀ : c.F →+* A.Ω₀) (hc₀ : spMap c₀ = x₀ ≫ pullback.snd _ _) : A.cst = A.fn.comp c₀ := by
  have e₁ : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    unfold Model.j
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have e₂ : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀ := A.fn_over
  apply sp_inj
  rw [← cancel_mono (spMap β), sp_comp, ← A.cst_over, ← sp_comp A.fn c₀, hc₀, ← Category.assoc A.ξ, e₂, h]
  simp only [Category.assoc]
  rw [e₁]

/- English proof (translation)
Rewrite using `[Fl.V₀_mem]`. Establish `key : ∀ a, (A.ρ a (Fl.j e) = A.emb s a • Fl.j e) ↔ (Fl.M₀.pt e).left ≫ (Y.t.act.act a).left = spMap (epsMul (c₀ (labelEmb c s a))) ≫ (Fl.M₀.pt e).left`. Introduce `a`. Establish `hσ : A.emb s a = A.fn (c₀ (labelEmb c s a))` using `by show A.cst (labelEmb c s a) = _`. Rewrite using `[hc]`.

Both sides reduce to the same expression. Establish `s1 : (A.ρ a (Fl.j e) = A.emb s a • Fl.j e) ↔ (A.M.pt (Fl.j e)).left ≫ (A.t.act.act a).left = spMap (epsMul (A.emb s a)) ≫ (A.M.pt (Fl.j e)).left`. Establish `ha : A.M.pt (A.ρ a (Fl.j e)) = A.M.pt (Fl.j e) ≫ A.t.act.act a` using `A.act a (Fl.j e)`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite `ha` using `[h]`. Use `congrArg (fun w => w.left) ha` as an intermediate fact. Rewrite using `[← Over.comp_left]`. Conclude with `this.symm.trans (A.M.smul _ _)`. Introduce `h`.

Apply `A.M.inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[ha, A.M.smul, Over.comp_left]`. Conclude with `h`. Establish `hq` using `Fl.j_pt e`.

Establish `s2` using `cart_eig A.m.cart.1 (A.t.act.act a) _ (A.m.act a) (A.M.pt (Fl.j e)).left (spMap (epsMul (A.emb s a))) (eps_base _ _ A.ξ (Over.w (A.M.pt (Fl.j e))) _)`. Establish `e3 : spMap (epsMul (A.fn (c₀ (labelEmb c s a)))) ≫ spMap (dualMap A.fn) ≫ (Fl.M₀.pt e).left = spMap (dualMap A.fn) ≫ spMap (epsMul (c₀ (labelEmb c s a))) ≫ (Fl.M₀.pt e).left`. Rewrite using `[← Category.assoc, sp_eps_dual A.fn, Category.assoc]`. Rewrite using `[s1, s2, hq, hσ, e3, Category.assoc]`. Use `haveI := dual_epi A.fn`.

Conclude with `cancel_epi (spMap (dualMap A.fn))`. Prove the components needed by the constructor for the conclusion. Introduce `h a`. Use `(key a).1 ?_` and prove the remaining obligations. Use `(Submodule.mem_iInf _).1 h a` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker]`. Simplify `this` using `[sub_eq_zero]`. Introduce `h`. Use `(Submodule.mem_iInf _).2 fun a => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`.

Simplify `(key a).2 (h a)` using `[sub_eq_zero]`.
-/
theorem flag_eig (A : HodgeCpt Y S y) (Fl : A.Flag) (c₀ : c.F →+* A.Ω₀) (hc : A.cst = A.fn.comp c₀)
    (s : CMType H ⊕ CMType H) (e : Fl.Li₀) : e ∈ Fl.V₀ s ↔
      ∀ a, (Fl.M₀.pt e).left ≫ (Y.t.act.act a).left =
        spMap (epsMul (c₀ (labelEmb c s a))) ≫ (Fl.M₀.pt e).left := by
  rw [Fl.V₀_mem]
  have key : ∀ a, (A.ρ a (Fl.j e) = A.emb s a • Fl.j e) ↔ (Fl.M₀.pt e).left ≫ (Y.t.act.act a).left =
      spMap (epsMul (c₀ (labelEmb c s a))) ≫ (Fl.M₀.pt e).left := by
    intro a
    have hσ : A.emb s a = A.fn (c₀ (labelEmb c s a)) := by
      show A.cst (labelEmb c s a) = _
      rw [hc]
      rfl
    have s1 : (A.ρ a (Fl.j e) = A.emb s a • Fl.j e) ↔ (A.M.pt (Fl.j e)).left ≫ (A.t.act.act a).left =
        spMap (epsMul (A.emb s a)) ≫ (A.M.pt (Fl.j e)).left := by
      have ha : A.M.pt (A.ρ a (Fl.j e)) = A.M.pt (Fl.j e) ≫ A.t.act.act a := A.act a (Fl.j e)
      constructor
      · intro h
        rw [h] at ha
        have := congrArg (fun w => w.left) ha
        rw [← Over.comp_left]
        exact this.symm.trans (A.M.smul _ _)
      · intro h
        apply A.M.inj
        apply Over.OverMorphism.ext
        rw [ha, A.M.smul, Over.comp_left]
        exact h
    have hq := Fl.j_pt e
    have s2 := cart_eig A.m.cart.1 (A.t.act.act a) _ (A.m.act a) (A.M.pt (Fl.j e)).left
      (spMap (epsMul (A.emb s a))) (eps_base _ _ A.ξ (Over.w (A.M.pt (Fl.j e))) _)
    have e3 : spMap (epsMul (A.fn (c₀ (labelEmb c s a)))) ≫ spMap (dualMap A.fn) ≫ (Fl.M₀.pt e).left =
        spMap (dualMap A.fn) ≫ spMap (epsMul (c₀ (labelEmb c s a))) ≫ (Fl.M₀.pt e).left := by
      rw [← Category.assoc, sp_eps_dual A.fn, Category.assoc]
    rw [s1, s2, hq, hσ, e3, Category.assoc]
    haveI := dual_epi A.fn
    exact cancel_epi (spMap (dualMap A.fn))
  constructor
  · intro h a
    refine (key a).1 ?_
    have := (Submodule.mem_iInf _).1 h a
    rw [LinearMap.mem_ker] at this
    simpa [sub_eq_zero] using this
  · intro h
    refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker]
    simpa [sub_eq_zero] using (key a).2 (h a)

end Geo

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω Ω' _ _ K K' _ _ J J' _ _ y y' A A' Fl Fl' ψ x₀ x₀' mβ mβ' hξ hξ' h1 h2`. Take `⟨θ, hθ, hpts⟩` from `core Y Y' g Φ n ψ x₀ x₀' A.ξ₀ A'.ξ₀ hξ hξ' h1 Fl.M₀ Fl'.M₀`. Take `⟨c₀, hc₀⟩` from `exists_sp (x₀ ≫ pullback.snd _ _)`. Take `⟨c₀', hc₀'⟩` from `exists_sp (x₀' ≫ pullback.snd _ _)`. Establish `hcst` using `cst_eq A mβ x₀ hξ c₀ hc₀`.

Establish `hcst'` using `cst_eq A' mβ' x₀' hξ' c₀' hc₀'`. Establish `hψ : c₀ = ψ.toRingHom.comp c₀'` using `sp_inj (by`. Rewrite using `[hc₀, ← sp_comp, hc₀', h2])`. Use `⟨θ, hθ, fun e => ?_, fun s s' hs e => ?_⟩` and prove the remaining obligations. Take `⟨u, u₃, a1, a2, a3, a4, a5⟩` from `hpts e`.

Use `⟨u, spMap (dualMap ψ.toRingHom) ≫ u₃, a1, by rw [Category.assoc, a2], ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans a5`. Establish `e1 : (spMap (dualMap ψ.toRingHom) ≫ u₃) ≫ Y'.oF.t.G.hom = spMap (algebraMap A.Ω₀ (DualNumber A.Ω₀)) ≫ spMap ψ.toRingHom ≫ x₀'`. Rewrite using `[Category.assoc, a4, ← Category.assoc, sp_dual_alg, Category.assoc]`. Rewrite using `[← Category.assoc _ Y'.oF.t.G.hom, e1, ← Category.assoc u, a3]`.

Simplify using `only [Category.assoc]`. Rewrite using `[h2]`. Rewrite using `[flag_eig A Fl c₀ hcst, flag_eig A' Fl' c₀' hcst']`. Take `⟨u, u₃, a1, a2, a3, a4, a5⟩` from `hpts e`. Rewrite using `[← a1, ← a2]`.

Use `eig_iff Y Y' g Φ n ψ x₀ x₀' u u₃ a3 a4 a5 (fun a => c₀ (labelEmb c s a)) (fun a => c₀' (labelEmb c s' a)) ?_` and prove the remaining obligations. Introduce `a`. Rewrite using `[hs, hψ]`. Both sides reduce to the same expression.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y') (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (x₀ : Sp A.Ω₀ ⟶ Xo.XF c) (x₀' : Sp A'.Ω₀ ⟶ Xo.XF c), Mono (spMap β) → Mono (spMap β') → A.ξ₀ = x₀ ≫ Y.j → A'.ξ₀ = x₀' ≫ Y'.j → spMap ψ.toRingHom ≫ x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _ ≫ Φ.hom → spMap ψ.toRingHom ≫ x₀' ≫ pullback.snd _ _ = x₀ ≫ pullback.snd _ _ → ∃ θ : Fl.Li₀ ≃+ Fl'.Li₀, (∀ (a : A'.Ω₀) e, θ (ψ a • e) = a • θ e) ∧ (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) ∧ ∀ s s', labelEmb c s' = (labelEmb c s).comp g.s.toRingHom → ∀ e, e ∈ Fl.V₀ s ↔ θ e ∈ Fl'.V₀ s' := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω Ω' _ _ K K' _ _ J J' _ _ y y' A A' Fl Fl' ψ x₀ x₀' mβ mβ' hξ hξ' h1 h2
  obtain ⟨θ, hθ, hpts⟩ := core Y Y' g Φ n ψ x₀ x₀' A.ξ₀ A'.ξ₀ hξ hξ' h1 Fl.M₀ Fl'.M₀
  obtain ⟨c₀, hc₀⟩ := exists_sp (x₀ ≫ pullback.snd _ _)
  obtain ⟨c₀', hc₀'⟩ := exists_sp (x₀' ≫ pullback.snd _ _)
  have hcst := cst_eq A mβ x₀ hξ c₀ hc₀
  have hcst' := cst_eq A' mβ' x₀' hξ' c₀' hc₀'
  have hψ : c₀ = ψ.toRingHom.comp c₀' := sp_inj (by
    rw [hc₀, ← sp_comp, hc₀', h2])
  refine ⟨θ, hθ, fun e => ?_, fun s s' hs e => ?_⟩
  · obtain ⟨u, u₃, a1, a2, a3, a4, a5⟩ := hpts e
    refine ⟨u, spMap (dualMap ψ.toRingHom) ≫ u₃, a1, by rw [Category.assoc, a2], ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans a5
    · have e1 : (spMap (dualMap ψ.toRingHom) ≫ u₃) ≫ Y'.oF.t.G.hom =
          spMap (algebraMap A.Ω₀ (DualNumber A.Ω₀)) ≫ spMap ψ.toRingHom ≫ x₀' := by
        rw [Category.assoc, a4, ← Category.assoc, sp_dual_alg, Category.assoc]
      rw [← Category.assoc _ Y'.oF.t.G.hom, e1, ← Category.assoc u, a3]
      simp only [Category.assoc]
      rw [h2]
  · rw [flag_eig A Fl c₀ hcst, flag_eig A' Fl' c₀' hcst']
    obtain ⟨u, u₃, a1, a2, a3, a4, a5⟩ := hpts e
    rw [← a1, ← a2]
    refine eig_iff Y Y' g Φ n ψ x₀ x₀' u u₃ a3 a4 a5 (fun a => c₀ (labelEmb c s a)) (fun a => c₀' (labelEmb c s' a)) ?_
    intro a
    rw [hs, hψ]
    rfl

end GlobalTheory.CompanionTheory.Ar.LieTw
