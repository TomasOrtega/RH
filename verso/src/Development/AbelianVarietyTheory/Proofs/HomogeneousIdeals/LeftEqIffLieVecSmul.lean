import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.Diag

section Act

variable (S : Scheme.{0}) (O : Type) [CommRing O] (X : Type) [AddCommGroup X] [Module O X]

def diagAct : OAct O (splitTorus S X) where
  act a := diagMap S (DistribSMul.toAddMonoidHom X a)
  hom _ := inferInstance
  one := by
    rw [← diagMap_id]; congr 1; ext x; simp
  mul a b := by
    rw [← diagMap_comp]; congr 1; ext x; simp [mul_smul]
  add a b := by
    rw [← diagMap_add]; congr 1; ext x; simp [add_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagAct_act (a : O) :
    (diagAct S O X).act a = diagMap S (DistribSMul.toAddMonoidHom X a) := rfl

end Act

section Val

variable {S : Scheme.{0}} {A : Type} [CommRing A] {g : Sp A ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def charVal (w : Over.mk g ⟶ splitTorus S X) (x : X) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (w.left.appTop.hom (chi X x))

/- English proof (translation)
Simplify using `[charVal, chi, coord]`. Both sides reduce to the same expression.
-/
theorem charVal_eq_coord (w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal w x = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((coord w).hom (AddMonoidAlgebra.single x 1)) := by
  simp [charVal, chi, coord]
  rfl

/- English proof (translation)
Use `hom_ext fun x => ?_` and prove the remaining obligations. Establish `e` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (h x)`. Simplify `e` using `[charVal_eq_coord]`.
-/
theorem charVal_ext {v w : Over.mk g ⟶ splitTorus S X} (h : ∀ x, charVal v x = charVal w x) :
    v = w := by
  refine hom_ext fun x => ?_
  have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (h x)
  simpa [charVal_eq_coord] using e

/- English proof (translation)
Rewrite using `[charVal_eq_coord, coord_one, map_one]`.
-/
theorem charVal_one (x : X) : charVal (1 : Over.mk g ⟶ splitTorus S X) x = 1 := by
  rw [charVal_eq_coord, coord_one, map_one]

/- English proof (translation)
Rewrite using `[charVal_eq_coord, charVal_eq_coord, charVal_eq_coord, coord_mul, map_mul]`.
-/
theorem charVal_mul (v w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal (v * w) x = charVal v x * charVal w x := by
  rw [charVal_eq_coord, charVal_eq_coord, charVal_eq_coord, coord_mul, map_mul]

/- English proof (translation)
Rewrite using `[charVal_eq_coord, coord_single_zero, map_one]`.
-/
theorem charVal_zero (w : Over.mk g ⟶ splitTorus S X) : charVal w 0 = 1 := by
  rw [charVal_eq_coord, coord_single_zero, map_one]

/- English proof (translation)
Rewrite using `[charVal_eq_coord, charVal_eq_coord, charVal_eq_coord, coord_single_add, map_mul]`.
-/
theorem charVal_add (w : Over.mk g ⟶ splitTorus S X) (x y : X) :
    charVal w (x + y) = charVal w x * charVal w y := by
  rw [charVal_eq_coord, charVal_eq_coord, charVal_eq_coord, coord_single_add, map_mul]

/- English proof (translation)
Rewrite using `[charVal_eq_coord, charVal_eq_coord, coord_comp_diagMap_single]`.
-/
theorem charVal_comp_diagMap (w : Over.mk g ⟶ splitTorus S X) (u : Y →+ X) (y : Y) :
    charVal (w ≫ diagMap S u) y = charVal w (u y) := by
  rw [charVal_eq_coord, charVal_eq_coord, coord_comp_diagMap_single]

/- English proof (translation)
Take `⟨φ, hφ⟩ : ∃ φ, Spec.map φ = w.left ≫ torusFst S X` from `⟨_, Spec.map_preimage _⟩`. Rewrite using `[charVal_eq_coord]`. Unfold `coord`. Rewrite using `[← hφ, Spec.preimage_map]`. Establish `e` using `congrArg (fun k => k.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single x 1))) (Scheme.ΓSpecIso_naturality φ)`.

Use `e.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem charVal_eq_torusFst (w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal w x = (Spec.preimage (w.left ≫ torusFst S X)).hom (AddMonoidAlgebra.single x 1) := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = w.left ≫ torusFst S X := ⟨_, Spec.map_preimage _⟩
  rw [charVal_eq_coord]
  unfold coord
  rw [← hφ, Spec.preimage_map]
  have e := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single x 1)))
    (Scheme.ΓSpecIso_naturality φ)
  refine e.trans ?_
  simp

/- English proof (translation)
Take `⟨φ1, h1⟩ : ∃ φ1, Spec.map φ1 = w'.left ≫ torusFst S' X` from `⟨_, Spec.map_preimage _⟩`. Take `⟨φ2, h2⟩ : ∃ φ2, Spec.map φ2 = w.left ≫ torusFst S X` from `⟨_, Spec.map_preimage _⟩`. Simplify using `only [charVal_eq_torusFst, ← h1, ← h2, Spec.preimage_map, spMap, ← Spec.map_comp]`. Rewrite using `[Spec.map_inj]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x`. Rewrite using `[h]`. Both sides reduce to the same expression. Introduce `h ext1`. Apply `AddMonoidAlgebra.ringHom_ext` to reduce the goal to its premises.

Introduce `b`. Use `RingHom.congr_fun (RingHom.ext_int ((φ1.hom.comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom) (((φ2 ≫ CommRingCat.ofHom φ).hom.comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom)) b.down` as an intermediate fact. Conclude with `this`. Introduce `x`. Simplify using `using h x`.
-/
theorem torusFst_eq_iff {S' : Scheme.{0}} {A' : Type} [CommRing A'] {g' : Sp A' ⟶ S'} (φ : A →+* A')
    (w' : Over.mk g' ⟶ splitTorus S' X) (w : Over.mk g ⟶ splitTorus S X) :
    w'.left ≫ torusFst S' X = spMap φ ≫ w.left ≫ torusFst S X ↔
      ∀ x, charVal w' x = φ (charVal w x) := by
  obtain ⟨φ1, h1⟩ : ∃ φ1, Spec.map φ1 = w'.left ≫ torusFst S' X := ⟨_, Spec.map_preimage _⟩
  obtain ⟨φ2, h2⟩ : ∃ φ2, Spec.map φ2 = w.left ≫ torusFst S X := ⟨_, Spec.map_preimage _⟩
  simp only [charVal_eq_torusFst, ← h1, ← h2, Spec.preimage_map, spMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  constructor
  · intro h x
    rw [h]
    rfl
  · intro h
    ext1
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      have := RingHom.congr_fun (RingHom.ext_int
        ((φ1.hom.comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom)
        (((φ2 ≫ CommRingCat.ofHom φ).hom.comp AddMonoidAlgebra.singleZeroRingHom).comp
          (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom)) b.down
      exact this
    · intro x
      simpa using h x

/- English proof (translation)
Rewrite using `[← torusFst_eq_iff φ w' w]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, Category.assoc]`. Introduce `h`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite `h` using `[← Category.assoc]`. Conclude with `h`. Establish `e1` using `Over.w w'`. Establish `e2` using `Over.w w`.

Simplify using `only [Over.mk_hom] at e1 e2`. Express the relevant statement in the definitionally equal form `w'.left ≫ (splitTorus S X).hom = (spMap φ ≫ w.left) ≫ (splitTorus S X).hom`. Rewrite using `[e1, Category.assoc, e2, hg]`.
-/
theorem left_eq_iff {A' : Type} [CommRing A'] {g' : Sp A' ⟶ S} (φ : A →+* A') (hg : g' = spMap φ ≫ g)
    (w' : Over.mk g' ⟶ splitTorus S X) (w : Over.mk g ⟶ splitTorus S X) :
    w'.left = spMap φ ≫ w.left ↔ ∀ x, charVal w' x = φ (charVal w x) := by
  rw [← torusFst_eq_iff φ w' w]
  constructor
  · intro h
    rw [h, Category.assoc]
  · intro h
    apply pullback.hom_ext
    · rw [← Category.assoc] at h
      exact h
    · have e1 := Over.w w'
      have e2 := Over.w w
      simp only [Over.mk_hom] at e1 e2
      change w'.left ≫ (splitTorus S X).hom = (spMap φ ≫ w.left) ≫ (splitTorus S X).hom
      rw [e1, Category.assoc, e2, hg]

variable (g) in

def ofVal (f : Multiplicative X →* A) : Over.mk g ⟶ splitTorus S X :=
  ofChar _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom.comp f)

/- English proof (translation)
Rewrite using `[charVal_eq_coord, ofVal, coord_ofChar]`. Simplify using the standard rewrite rules.
-/
theorem charVal_ofVal (f : Multiplicative X →* A) (x : X) :
    charVal (ofVal g f) x = f (Multiplicative.ofAdd x) := by
  rw [charVal_eq_coord, ofVal, coord_ofChar]
  simp

end Val

section Eps

variable {S : Scheme.{0}} {R : Type} [CommRing R] {g : Sp (DualNumber R) ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

variable (g) in

def epsVec (c : X →+ R) : Over.mk g ⟶ splitTorus S X :=
  ofVal g
    { toFun := fun x => 1 + inr (c x.toAdd)
      map_one' := by simp
      map_mul' := fun x y => by ext <;> simp [add_comm] }

/- English proof (translation)
Rewrite using `[epsVec, charVal_ofVal]`. Both sides reduce to the same expression.
-/
theorem charVal_epsVec (c : X →+ R) (x : X) : charVal (epsVec g c) x = 1 + inr (c x) := by
  rw [epsVec, charVal_ofVal]
  rfl

/- English proof (translation)
Introduce `c d h`. Use extensionality with `x`. Establish `e` using `congrArg (fun w => (charVal w x).snd) h`. Simplify `e` using `[charVal_epsVec]`.
-/
theorem epsVec_injective : Function.Injective (epsVec g : (X →+ R) → _) := by
  intro c d h
  ext x
  have e := congrArg (fun w => (charVal w x).snd) h
  simpa [charVal_epsVec] using e

/- English proof (translation)
Use `charVal_ext fun x => ?_` and prove the remaining obligations. Simplify using `[charVal_epsVec, charVal_one]`.
-/
theorem epsVec_zero : epsVec g (0 : X →+ R) = 1 := by
  refine charVal_ext fun x => ?_
  simp [charVal_epsVec, charVal_one]

/- English proof (translation)
Use `charVal_ext fun x => ?_` and prove the remaining obligations. Rewrite using `[charVal_mul, charVal_epsVec, charVal_epsVec, charVal_epsVec]`. Apply the tactic sequence `ext <;> simp [add_comm]`.
-/
theorem epsVec_add (c d : X →+ R) : epsVec g (c + d) = epsVec g c * epsVec g d := by
  refine charVal_ext fun x => ?_
  rw [charVal_mul, charVal_epsVec, charVal_epsVec, charVal_epsVec]
  ext <;> simp [add_comm]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [epsVec_zero]`. Consider the case `succ n ih`. Rewrite using `[Fin.sum_univ_succ, epsVec_add, List.ofFn_succ, List.prod_cons, ih]`.
-/
theorem epsVec_sum {n : ℕ} (c : Fin n → (X →+ R)) :
    epsVec g (∑ i, c i) = (List.ofFn fun i => epsVec g (c i)).prod := by
  induction n with
  | zero => simp [epsVec_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, epsVec_add, List.ofFn_succ, List.prod_cons, ih]

/- English proof (translation)
Use `charVal_ext fun y => ?_` and prove the remaining obligations. Rewrite using `[charVal_comp_diagMap, charVal_epsVec, charVal_epsVec]`. Both sides reduce to the same expression.
-/
theorem epsVec_comp_diagMap (c : X →+ R) (u : Y →+ X) :
    epsVec g c ≫ diagMap S u = epsVec g (c.comp u) := by
  refine charVal_ext fun y => ?_
  rw [charVal_comp_diagMap, charVal_epsVec, charVal_epsVec]
  rfl

def epsCoeff (w : Over.mk g ⟶ splitTorus S X) (hw : ∀ x, (charVal w x).fst = 1) : X →+ R where
  toFun x := (charVal w x).snd
  map_zero' := by rw [charVal_zero]; rfl
  map_add' x y := by rw [charVal_add]; simp [hw, add_comm]

/- English proof (translation)
Use `charVal_ext fun x => ?_` and prove the remaining obligations. Rewrite using `[charVal_epsVec]`. Use `ext`. Simplify using `[hw x]`. Simplify using `[epsCoeff]`.
-/
theorem epsVec_epsCoeff (w : Over.mk g ⟶ splitTorus S X) (hw : ∀ x, (charVal w x).fst = 1) :
    epsVec g (epsCoeff w hw) = w := by
  refine charVal_ext fun x => ?_
  rw [charVal_epsVec]
  ext
  · simp [hw x]
  · simp [epsCoeff]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩ x`. Simplify using `[charVal_epsVec]`. Introduce `h`. Conclude with `⟨epsCoeff w h, epsVec_epsCoeff w h⟩`.
-/
theorem exists_epsVec_iff (w : Over.mk g ⟶ splitTorus S X) :
    (∃ c, epsVec g c = w) ↔ ∀ x, (charVal w x).fst = 1 := by
  constructor
  · rintro ⟨c, rfl⟩ x
    simp [charVal_epsVec]
  · intro h
    exact ⟨epsCoeff w h, epsVec_epsCoeff w h⟩

/- English proof (translation)
Rewrite using `[eq_comm, left_eq_iff _ ht]`. Simplify using `[charVal_one, eq_comm]`.
-/
theorem reduces_iff {t : Sp R ⟶ S} (ht : t = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g)
    (w : Over.mk g ⟶ splitTorus S X) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = (1 : Over.mk t ⟶ splitTorus S X).left ↔
      ∀ x, (charVal w x).fst = 1 := by
  rw [eq_comm, left_eq_iff _ ht]
  simp [charVal_one, eq_comm]

/- English proof (translation)
Rewrite using `[left_eq_iff _ hg]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `charVal_ext fun x => ?_` and prove the remaining obligations. Rewrite using `[h, charVal_epsVec, charVal_epsVec]`.

Apply the tactic sequence `ext <;> simp [epsScaleR, mul_comm]`. Introduce and unpack `rfl x`. Rewrite using `[charVal_epsVec, charVal_epsVec]`. Apply the tactic sequence `ext <;> simp [epsScaleR, mul_comm]`.
-/
theorem left_eq_epsScaleR_iff (a : R) (hg : g = spMap (epsScaleR a) ≫ g) (c : X →+ R)
    (u : Over.mk g ⟶ splitTorus S X) :
    u.left = spMap (epsScaleR a) ≫ (epsVec g c).left ↔ u = epsVec g (a • c) := by
  rw [left_eq_iff _ hg]
  constructor
  · intro h
    refine charVal_ext fun x => ?_
    rw [h, charVal_epsVec, charVal_epsVec]
    ext <;> simp [epsScaleR, mul_comm]
  · rintro rfl x
    rw [charVal_epsVec, charVal_epsVec]
    ext <;> simp [epsScaleR, mul_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Establish `hu' : ∀ i, u i = epsVec g (a i • c i)` using `fun i => (left_eq_epsScaleR_iff (a i) (hg (a i)) (c i) (u i)).1 (hu i)`. Rewrite using `[epsVec_sum]`. Conclude with `congrArg (fun f => (List.ofFn f).prod) (funext hu')`.

Introduce and unpack `rfl`. Conclude with `⟨fun i => epsVec g (a i • c i), fun i => (left_eq_epsScaleR_iff (a i) (hg (a i)) (c i) _).2 rfl, epsVec_sum _⟩`.
-/
theorem exists_prod_iff (hg : ∀ a : R, g = spMap (epsScaleR a) ≫ g) {n : ℕ} (a : Fin n → R)
    (c : Fin n → (X →+ R)) (w : Over.mk g ⟶ splitTorus S X) :
    (∃ u : Fin n → (Over.mk g ⟶ splitTorus S X),
      (∀ i, (u i).left = spMap (epsScaleR (a i)) ≫ (epsVec g (c i)).left) ∧ w = (List.ofFn u).prod) ↔
      w = epsVec g (∑ i, a i • c i) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : ∀ i, u i = epsVec g (a i • c i) := fun i =>
      (left_eq_epsScaleR_iff (a i) (hg (a i)) (c i) (u i)).1 (hu i)
    rw [epsVec_sum]
    exact congrArg (fun f => (List.ofFn f).prod) (funext hu')
  · rintro rfl
    exact ⟨fun i => epsVec g (a i • c i),
      fun i => (left_eq_epsScaleR_iff (a i) (hg (a i)) (c i) _).2 rfl, epsVec_sum _⟩

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem epsScaleR_base (a : R) :
    spMap (algebraMap R (DualNumber R)) = spMap (epsScaleR a) ≫ spMap (algebraMap R (DualNumber R)) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `Spec.map_id (CommRingCat.of R)` and compare the differences between its conclusion and the goal. Use extensionality with `r`. Simplify using the standard rewrite rules.
-/
theorem fstHom_base :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp

end Eps

section Lie

variable {R : Type} [CommRing R] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def lieVec (c : X →+ R) : epsR R ⟶ splitTorus (Sp R) X := epsVec _ c

/- English proof (translation)
The claim follows from `charVal_epsVec c x`.
-/
theorem charVal_lieVec (c : X →+ R) (x : X) : charVal (lieVec c) x = 1 + inr (c x) := charVal_epsVec c x

/- English proof (translation)
Unfold `IsTangent`. Use `reduces_iff (t := 𝟙 _) fstHom_base.symm w using 2` and compare the differences between its conclusion and the goal. Use `show _ = Over.Hom.left (toUnit (Over.mk (𝟙 (Sp R))) ≫ η)`. Rewrite using `[Over.comp_left]`. Conclude with `(Category.id_comp _).symm`.
-/
theorem isTangent_iff_charVal (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsTangent w ↔ ∀ x, (charVal w x).fst = 1 := by
  unfold IsTangent
  convert reduces_iff (t := 𝟙 _) fstHom_base.symm w using 2
  show _ = Over.Hom.left (toUnit (Over.mk (𝟙 (Sp R))) ≫ η)
  rw [Over.comp_left]
  exact (Category.id_comp _).symm

/- English proof (translation)
Rewrite using `[isTangent_iff_charVal]`. Conclude with `(exists_epsVec_iff w).symm`.
-/
theorem isTangent_iff_exists (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsTangent w ↔ ∃ c, lieVec c = w := by
  rw [isTangent_iff_charVal]
  exact (exists_epsVec_iff w).symm

/- English proof (translation)
The claim follows from `(isTangent_iff_exists _).2 ⟨c, rfl⟩`.
-/
theorem isTangent_lieVec (c : X →+ R) : IsTangent (lieVec c) := (isTangent_iff_exists _).2 ⟨c, rfl⟩

/- English proof (translation)
The claim follows from `epsVec_injective`.
-/
theorem lieVec_injective : Function.Injective (lieVec : (X →+ R) → _) := epsVec_injective

/- English proof (translation)
The claim follows from `epsVec_add c d`.
-/
theorem lieVec_add (c d : X →+ R) : lieVec (c + d) = lieVec c * lieVec d := epsVec_add c d

/- English proof (translation)
The claim follows from `left_eq_epsScaleR_iff a (epsScaleR_base a) c u`.
-/
theorem left_eq_iff_lieVec_smul (a : R) (c : X →+ R) (u : epsR R ⟶ splitTorus (Sp R) X) :
    u.left = spMap (epsScaleR a) ≫ (lieVec c).left ↔ u = lieVec (a • c) := left_eq_epsScaleR_iff a (epsScaleR_base a) c u

/- English proof (translation)
The claim follows from `(left_eq_iff_lieVec_smul a c _).2 rfl`.
-/
theorem lieVec_smul_left (a : R) (c : X →+ R) :
    (lieVec (a • c)).left = spMap (epsScaleR a) ≫ (lieVec c).left := (left_eq_iff_lieVec_smul a c _).2 rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[lieVec_smul_left, Over.comp_left]`. Both sides reduce to the same expression.
-/
theorem lieVec_smul (a : R) (c : X →+ R) : lieVec (a • c) = GrpTangent.epsScale a ≫ lieVec c := by
  apply Over.OverMorphism.ext
  rw [lieVec_smul_left, Over.comp_left]
  rfl

/- English proof (translation)
The claim follows from `epsVec_comp_diagMap c u`.
-/
theorem lieVec_comp_diagMap (c : X →+ R) (u : Y →+ X) :
    lieVec c ≫ diagMap (Sp R) u = lieVec (c.comp u) := epsVec_comp_diagMap c u

/- English proof (translation)
Unfold `IsLieComb`. Conclude with `exists_prod_iff (fun b => epsScaleR_base b) a c w`.
-/
theorem isLieComb_iff {n : ℕ} (a : Fin n → R) (c : Fin n → (X →+ R))
    (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsLieComb a (fun i => lieVec (c i)) w ↔ w = lieVec (∑ i, a i • c i) := by
  unfold IsLieComb
  exact exists_prod_iff (fun b => epsScaleR_base b) a c w

variable (R X) in

def lieEquiv : {w : epsR R ⟶ splitTorus (Sp R) X // IsTangent w} ≃ (X →+ R) where
  toFun w := epsCoeff w.1 ((isTangent_iff_charVal _).1 w.2)
  invFun c := ⟨lieVec c, isTangent_lieVec c⟩
  left_inv _ := Subtype.ext (epsVec_epsCoeff _ _)
  right_inv _ := epsVec_injective (epsVec_epsCoeff _ _)

/- English proof (translation)
Establish `key : IsLieBasis (fun i => lieVec (c i)) ↔ ∀ d : X →+ R, ∃! a : Fin n → R, d = ∑ i, a i • c i`. Unfold `IsLieBasis`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ d`. Take `⟨a, ha, hu⟩` from `h (lieVec d) (isTangent_lieVec d)`.

Conclude with `⟨a, lieVec_injective ((isLieComb_iff a c _).1 ha), fun b hb => hu b ((isLieComb_iff b c _).2 (congrArg lieVec hb))⟩`. Introduce `h`. Use `⟨fun i => isTangent_lieVec _, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl⟩` from `(isTangent_iff_exists w).1 hw`. Take `⟨a, ha, hu⟩` from `h d`.

Conclude with `⟨a, (isLieComb_iff a c _).2 (congrArg lieVec ha), fun b hb => hu b (lieVec_injective ((isLieComb_iff b c _).1 hb))⟩`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha i`. Take `⟨z, -, hz⟩` from `h 0`. Establish `h0 : a = z` using `hz a ha.symm`. Establish `h1 : (0 : Fin n → R) = z` using `hz 0 (by simp)`.

Rewrite using `[h0, ← h1]`. Both sides reduce to the same expression. Introduce and unpack `d -`. Take `⟨a, ha, -⟩` from `h d`. Rewrite using `[ha]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce and unpack `⟨hli, hsp⟩ d`. Establish `hd : d ∈ Submodule.span R (Set.range c)` using `hsp Submodule.mem_top`. Rewrite `hd` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨a, ha⟩` from `hd`.

Use `⟨a, ha.symm, fun b hb => ?_⟩` and prove the remaining obligations. Establish `h0` using `Fintype.linearIndependent_iff.1 hli (b - a) (by simp [sub_smul, Finset.sum_sub_distrib, ← hb, ha])`. Use function extensionality and compare the values at `i`. Simplify `h0 i` using `[sub_eq_zero]`.
-/
theorem isLieBasis_iff {n : ℕ} (c : Fin n → (X →+ R)) :
    IsLieBasis (fun i => lieVec (c i)) ↔
      LinearIndependent R c ∧ ⊤ ≤ Submodule.span R (Set.range c) := by
  have key : IsLieBasis (fun i => lieVec (c i)) ↔ ∀ d : X →+ R, ∃! a : Fin n → R, d = ∑ i, a i • c i := by
    unfold IsLieBasis
    constructor
    · rintro ⟨-, h⟩ d
      obtain ⟨a, ha, hu⟩ := h (lieVec d) (isTangent_lieVec d)
      exact ⟨a, lieVec_injective ((isLieComb_iff a c _).1 ha),
        fun b hb => hu b ((isLieComb_iff b c _).2 (congrArg lieVec hb))⟩
    · intro h
      refine ⟨fun i => isTangent_lieVec _, fun w hw => ?_⟩
      obtain ⟨d, rfl⟩ := (isTangent_iff_exists w).1 hw
      obtain ⟨a, ha, hu⟩ := h d
      exact ⟨a, (isLieComb_iff a c _).2 (congrArg lieVec ha),
        fun b hb => hu b (lieVec_injective ((isLieComb_iff b c _).1 hb))⟩
  rw [key]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro a ha i
      obtain ⟨z, -, hz⟩ := h 0
      have h0 : a = z := hz a ha.symm
      have h1 : (0 : Fin n → R) = z := hz 0 (by simp)
      rw [h0, ← h1]
      rfl
    · rintro d -
      obtain ⟨a, ha, -⟩ := h d
      rw [ha]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro ⟨hli, hsp⟩ d
    have hd : d ∈ Submodule.span R (Set.range c) := hsp Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hd
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, ha.symm, fun b hb => ?_⟩
    have h0 := Fintype.linearIndependent_iff.1 hli (b - a)
      (by simp [sub_smul, Finset.sum_sub_distrib, ← hb, ha])
    funext i
    simpa [sub_eq_zero] using h0 i

/- English proof (translation)
The claim follows from `(isLieBasis_iff _).2 ⟨b.linearIndependent, b.span_eq.ge⟩`.
-/
theorem isLieBasis_of_basis {n : ℕ} (b : Module.Basis (Fin n) R (X →+ R)) :
    IsLieBasis (fun i => lieVec (b i)) := (isLieBasis_iff _).2 ⟨b.linearIndependent, b.span_eq.ge⟩

def transpose (R : Type) [CommRing R] (u : Y →+ X) : (X →+ R) →ₗ[R] (Y →+ R) where
  toFun c := c.comp u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem transpose_apply (u : Y →+ X) (c : X →+ R) : transpose R u c = c.comp u := rfl

section Basis

variable {I J : Type} [Fintype I] [Fintype J]

variable (R) in

def dualBasis (b : Module.Basis I ℤ X) : Module.Basis I R (X →+ R) :=
  Module.Basis.ofEquivFun
    { toFun := fun c i => c (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => (b.constr ℤ f).toAddMonoidHom
      left_inv := fun c => congrArg LinearMap.toAddMonoidHom
        (b.constr_eq (S := ℤ) (f := c.toIntLinearMap) fun _ => rfl)
      right_inv := fun f => funext fun i => b.constr_basis ℤ f i }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualBasis_repr (b : Module.Basis I ℤ X) (c : X →+ R) (i : I) :
    (dualBasis R b).repr c i = c (b i) := rfl

/- English proof (translation)
Establish `key : ∀ j, dualBasis R b i (b j) = (b.repr (b j) i : R)`. Introduce `j`. Rewrite using `[← dualBasis_repr, Module.Basis.repr_self, Module.Basis.repr_self]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Establish `e : (dualBasis R b i).toIntLinearMap = (Int.castAddHom R).toIntLinearMap.comp (b.coord i)` using `b.ext fun j => by simpa using key j`. Simplify using `using congrArg (fun f => f x) e`.
-/
theorem dualBasis_apply (b : Module.Basis I ℤ X) (i : I) (x : X) :
    dualBasis R b i x = (b.repr x i : R) := by
  have key : ∀ j, dualBasis R b i (b j) = (b.repr (b j) i : R) := by
    intro j
    rw [← dualBasis_repr, Module.Basis.repr_self, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have e : (dualBasis R b i).toIntLinearMap = (Int.castAddHom R).toIntLinearMap.comp (b.coord i) :=
    b.ext fun j => by simpa using key j
  simpa using congrArg (fun f => f x) e

/- English proof (translation)
Use extensionality with `j i`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix_apply, dualBasis_repr, transpose_apply, AddMonoidHom.comp_apply, dualBasis_apply]`. Both sides reduce to the same expression.
-/
theorem toMatrix_transpose [DecidableEq I] [DecidableEq J] (b : Module.Basis I ℤ X)
    (b' : Module.Basis J ℤ Y) (u : Y →+ X) :
    LinearMap.toMatrix (dualBasis R b) (dualBasis R b') (transpose R u) =
      ((LinearMap.toMatrix b' b u.toIntLinearMap).map (Int.castRingHom R)).transpose := by
  ext j i
  rw [LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    dualBasis_repr, transpose_apply, AddMonoidHom.comp_apply, dualBasis_apply]
  rfl

/- English proof (translation)
Use `conv_lhs => rw [← (dualBasis R b').sum_repr ((dualBasis R b i).comp u)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[dualBasis_repr, AddMonoidHom.comp_apply, dualBasis_apply, LinearMap.toMatrix_apply]`. Both sides reduce to the same expression.
-/
theorem dualBasis_comp [DecidableEq J] (b : Module.Basis I ℤ X)
    (b' : Module.Basis J ℤ Y) (u : Y →+ X) (i : I) :
    (dualBasis R b i).comp u =
      ∑ j, (LinearMap.toMatrix b' b u.toIntLinearMap i j : R) • dualBasis R b' j := by
  conv_lhs => rw [← (dualBasis R b').sum_repr ((dualBasis R b i).comp u)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dualBasis_repr, AddMonoidHom.comp_apply, dualBasis_apply, LinearMap.toMatrix_apply]
  rfl

end Basis

instance free_addHom [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Free R (X →+ R) :=
  Module.Free.of_basis (dualBasis R (Module.Free.chooseBasis ℤ X))

instance finite_addHom [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Finite R (X →+ R) :=
  Module.Finite.of_basis (dualBasis R (Module.Free.chooseBasis ℤ X))

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ X`. Rewrite using `[← LinearMap.charpoly_toMatrix (transpose R u) (dualBasis R b), toMatrix_transpose b b u, Matrix.charpoly_transpose, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]`.
-/
theorem charpoly_transpose [Module.Free ℤ X] [Module.Finite ℤ X] (u : X →+ X) :
    (transpose R u).charpoly = u.toIntLinearMap.charpoly.map (Int.castRingHom R) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  rw [← LinearMap.charpoly_toMatrix (transpose R u) (dualBasis R b), toMatrix_transpose b b u,
    Matrix.charpoly_transpose, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

/- English proof (translation)
The claim follows from `isLieBasis_of_basis (dualBasis R b)`.
-/
theorem isLieBasis_dualBasis {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    IsLieBasis (fun i => lieVec (dualBasis R b i)) := isLieBasis_of_basis (dualBasis R b)

/- English proof (translation)
Rewrite using `[lieVec_comp_diagMap, isLieComb_iff, dualBasis_comp b b' u i]`.
-/
theorem isLieComb_comp_diagMap {n m : ℕ} (b : Module.Basis (Fin n) ℤ X) (b' : Module.Basis (Fin m) ℤ Y)
    (u : Y →+ X) (i : Fin n) :
    IsLieComb (fun j => (LinearMap.toMatrix b' b u.toIntLinearMap i j : R))
      (fun j => lieVec (dualBasis R b' j)) (lieVec (dualBasis R b i) ≫ diagMap (Sp R) u) := by
  rw [lieVec_comp_diagMap, isLieComb_iff, dualBasis_comp b b' u i]

end Lie

section Fibre

variable {S : Scheme.{0}} {k : Type} [Field k] (t : Sp k ⟶ S) {O : Type} [CommRing O]
  {X : Type} [AddCommGroup X] [Module O X] (τ : O →+* k)

/- English proof (translation)
Rewrite using `[← Category.assoc, ← epsScaleR_base]`.
-/
theorem epsScaleR_base_comp (a : k) : spMap (algebraMap k (DualNumber k)) ≫ t =
    spMap (epsScaleR a) ≫ spMap (algebraMap k (DualNumber k)) ≫ t := by
  rw [← Category.assoc, ← epsScaleR_base]

/- English proof (translation)
Unfold `IsLieEigen`. Establish `ht : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) ≫ t`. Rewrite using `[← Category.assoc, fstHom_base, Category.id_comp]`. Rewrite using `[reduces_iff ht v, ← exists_epsVec_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨c, rfl⟩, h2⟩`. Use `⟨c, rfl, fun a x => ?_⟩` and prove the remaining obligations. Establish `h` using `(left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).1 (h2 a)`. Rewrite `h` using `[diagAct_act, epsVec_comp_diagMap]`. Use `congrArg (fun f => f x) (epsVec_injective h)` as an intermediate fact.

Simplify using `using this`. Introduce and unpack `⟨c, rfl, hc⟩`. Use `⟨⟨c, rfl⟩, fun a => ?_⟩` and prove the remaining obligations. Use `(left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).2 ?_` and prove the remaining obligations. Rewrite using `[diagAct_act, epsVec_comp_diagMap]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `using hc a x`.
-/
theorem isLieEigen_iff (v : epsPt t ⟶ splitTorus S X) :
    IsLieEigen (diagAct S O X) t τ v ↔
      ∃ c : X →+ k, epsVec _ c = v ∧ ∀ (a : O) (x : X), c (a • x) = τ a * c x := by
  unfold IsLieEigen
  have ht : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) ≫ t := by
    rw [← Category.assoc, fstHom_base, Category.id_comp]
  rw [reduces_iff ht v, ← exists_epsVec_iff]
  constructor
  · rintro ⟨⟨c, rfl⟩, h2⟩
    refine ⟨c, rfl, fun a x => ?_⟩
    have h := (left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).1 (h2 a)
    rw [diagAct_act, epsVec_comp_diagMap] at h
    have := congrArg (fun f => f x) (epsVec_injective h)
    simpa using this
  · rintro ⟨c, rfl, hc⟩
    refine ⟨⟨c, rfl⟩, fun a => ?_⟩
    refine (left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).2 ?_
    rw [diagAct_act, epsVec_comp_diagMap]
    congr 1
    ext x
    simpa using hc a x

variable (X) in

def eigenHom {k : Type} [CommRing k] (τ : O →+* k) : Submodule k (X →+ k) where
  carrier := {c | ∀ (a : O) (x : X), c (a • x) = τ a * c x}
  add_mem' hc hd a x := by simp [hc a x, hd a x, mul_add]
  zero_mem' a x := by simp
  smul_mem' r c hc a x := by simp [hc a x, mul_left_comm]

/- English proof (translation)
Establish `hg : ∀ a : k, spMap (algebraMap k (DualNumber k)) ≫ t = spMap (epsScaleR a) ≫ spMap (algebraMap k (DualNumber k)) ≫ t` using `epsScaleR_base_comp t`. Establish `key : LieMult (diagAct S O X) t τ n ↔ ∃ e : Fin n → eigenHom X τ, ∀ d : eigenHom X τ, ∃! c : Fin n → k, d = ∑ i, c i • e i`. Unfold `LieMult`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, h⟩ choose e he hce using fun i => (isLieEigen_iff t τ (v i)).1 (hv i)`.

Use `⟨fun i => ⟨e i, hce i⟩, fun d => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hu⟩` from `h (epsVec _ d.1) ((isLieEigen_iff t τ _).2 ⟨d.1, rfl, d.2⟩)`. Establish `hv' : v = fun i => epsVec _ (e i)` using `funext fun i => (he i).symm`. Substitute `hv'` using the available equality. Use `⟨c, ?_, fun c' hc' => hu c' ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `(exists_prod_iff hg c e _).1 hc` as an intermediate fact. Simplify using `using epsVec_injective this`. Use `(exists_prod_iff hg c' e _).2 ?_` and prove the remaining obligations. Rewrite using `[hc']`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨e, h⟩`. Use `⟨fun i => epsVec _ (e i).1, fun i => (isLieEigen_iff t τ _).2 ⟨_, rfl, (e i).2⟩, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl, hd⟩` from `(isLieEigen_iff t τ w).1 hw`. Take `⟨c, hc, hu⟩` from `h ⟨d, hd⟩`.

Use `⟨c, (exists_prod_iff hg c (fun i => (e i).1) _).2 ?_, fun c' hc' => hu c' ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hc` as an intermediate fact. Simplify using `at this`. Rewrite using `[this]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `epsVec_injective ((exists_prod_iff hg c' (fun i => (e i).1) _).1 hc')` as an intermediate fact. Simplify using `using this`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, h⟩`.

Establish `hli : LinearIndependent k e`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha i`. Take `⟨z, -, hz⟩` from `h 0`. Establish `h0 : a = z` using `hz a ha.symm`.

Establish `h1 : (0 : Fin n → k) = z` using `hz 0 (by simp)`. Rewrite using `[h0, ← h1]`. Both sides reduce to the same expression. Establish `hsp : ⊤ ≤ Submodule.span k (Set.range e)`. Introduce and unpack `d -`.

Take `⟨a, ha, -⟩` from `h d`. Rewrite using `[ha]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Conclude with `⟨Module.Basis.mk hli hsp⟩`. Introduce and unpack `⟨b⟩`.

Conclude with `⟨b, fun d => ⟨b.repr d, (b.sum_repr d).symm, fun c hc => by rw [hc, b.repr_sum_self]⟩⟩`.
-/
theorem lieMult_iff (n : ℕ) :
    LieMult (diagAct S O X) t τ n ↔ Nonempty (Module.Basis (Fin n) k (eigenHom X τ)) := by
  have hg : ∀ a : k, spMap (algebraMap k (DualNumber k)) ≫ t =
      spMap (epsScaleR a) ≫ spMap (algebraMap k (DualNumber k)) ≫ t := epsScaleR_base_comp t
  have key : LieMult (diagAct S O X) t τ n ↔
      ∃ e : Fin n → eigenHom X τ, ∀ d : eigenHom X τ, ∃! c : Fin n → k, d = ∑ i, c i • e i := by
    unfold LieMult
    constructor
    · rintro ⟨v, hv, h⟩
      choose e he hce using fun i => (isLieEigen_iff t τ (v i)).1 (hv i)
      refine ⟨fun i => ⟨e i, hce i⟩, fun d => ?_⟩
      obtain ⟨c, hc, hu⟩ := h (epsVec _ d.1) ((isLieEigen_iff t τ _).2 ⟨d.1, rfl, d.2⟩)
      have hv' : v = fun i => epsVec _ (e i) := funext fun i => (he i).symm
      subst hv'
      refine ⟨c, ?_, fun c' hc' => hu c' ?_⟩
      · apply Subtype.ext
        have := (exists_prod_iff hg c e _).1 hc
        simpa using epsVec_injective this
      · refine (exists_prod_iff hg c' e _).2 ?_
        rw [hc']
        simp
    · rintro ⟨e, h⟩
      refine ⟨fun i => epsVec _ (e i).1, fun i => (isLieEigen_iff t τ _).2 ⟨_, rfl, (e i).2⟩,
        fun w hw => ?_⟩
      obtain ⟨d, rfl, hd⟩ := (isLieEigen_iff t τ w).1 hw
      obtain ⟨c, hc, hu⟩ := h ⟨d, hd⟩
      refine ⟨c, (exists_prod_iff hg c (fun i => (e i).1) _).2 ?_, fun c' hc' => hu c' ?_⟩
      · have := congrArg Subtype.val hc
        simp at this
        rw [this]
      · apply Subtype.ext
        have := epsVec_injective ((exists_prod_iff hg c' (fun i => (e i).1) _).1 hc')
        simpa using this
  rw [key]
  constructor
  · rintro ⟨e, h⟩
    have hli : LinearIndependent k e := by
      rw [Fintype.linearIndependent_iff]
      intro a ha i
      obtain ⟨z, -, hz⟩ := h 0
      have h0 : a = z := hz a ha.symm
      have h1 : (0 : Fin n → k) = z := hz 0 (by simp)
      rw [h0, ← h1]
      rfl
    have hsp : ⊤ ≤ Submodule.span k (Set.range e) := by
      rintro d -
      obtain ⟨a, ha, -⟩ := h d
      rw [ha]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact ⟨Module.Basis.mk hli hsp⟩
  · rintro ⟨b⟩
    exact ⟨b, fun d => ⟨b.repr d, (b.sum_repr d).symm, fun c hc => by rw [hc, b.repr_sum_self]⟩⟩

end Fibre

end GlobalTheory.Diag

namespace GlobalTheory

open Diag

end GlobalTheory
