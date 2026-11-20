import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.SubOrder

noncomputable def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

/- English proof (translation)
Establish `e` using `IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h`. Rewrite `e` using `[IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]`. Establish `: CommRingCat.ofHom (valHom x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom` using `rfl`. Rewrite using `[this, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp]`. Simplify using the standard rewrite rules.
-/
theorem spec_valHom_fromSpec {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (valHom x U h)) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : CommRingCat.ofHom (valHom x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom := rfl
  rw [this, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp]
  simp

/- English proof (translation)
Establish `e1` using `spec_valHom_fromSpec (Spec.map (CommRingCat.ofHom φ) ≫ x) hU h'`. Establish `e2` using `spec_valHom_fromSpec x hU h`. Establish `: Spec.map (CommRingCat.ofHom (valHom (Spec.map (CommRingCat.ofHom φ) ≫ x) U h')) = Spec.map (CommRingCat.ofHom (φ.comp (valHom x U h)))`. Rewrite using `[← cancel_mono hU.fromSpec, e1, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, e2]`. Use `Spec.map_injective this` as an intermediate fact.

Use `congrArg (fun f => f.hom s) this` as an intermediate fact. Simplify using `using this`.
-/
theorem valHom_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) (φ : B →+* C)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valHom (Spec.map (CommRingCat.ofHom φ) ≫ x) U h' s = φ (valHom x U h s) := by
  have e1 := spec_valHom_fromSpec (Spec.map (CommRingCat.ofHom φ) ≫ x) hU h'
  have e2 := spec_valHom_fromSpec x hU h
  have : Spec.map (CommRingCat.ofHom (valHom (Spec.map (CommRingCat.ofHom φ) ≫ x) U h')) =
      Spec.map (CommRingCat.ofHom (φ.comp (valHom x U h))) := by
    rw [← cancel_mono hU.fromSpec, e1, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, e2]
  have := Spec.map_injective this
  have := congrArg (fun f => f.hom s) this
  simpa using this

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

/- English proof (translation)
Use `hF.finite` as an intermediate fact. Establish `: IsAffineHom (U.ι ≫ Γ.G.hom)` using `inferInstance`. Conclude with `isAffine_of_isAffineHom (U.ι ≫ Γ.G.hom)`.
-/
theorem isAffineOpen_of_fin (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U) : IsAffineOpen U := by
  have := hF.finite
  have : IsAffineHom (U.ι ≫ Γ.G.hom) := inferInstance
  exact isAffine_of_isAffineHom (U.ι ≫ Γ.G.hom)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h z => h (Set.mem_univ z), fun h z _ => h z⟩`.
-/
theorem top_le_iff_mem {X Y : Scheme.{0}} (x : Y ⟶ X) (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ ∀ z, x z ∈ U :=
  ⟨fun h z => h (Set.mem_univ z), fun h z _ => h z⟩

def subH (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U) : Subgroup T where
  carrier := {t | ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, top_le_iff_mem] at *
    have := hF.mul _ (Γ.pt a) (Γ.pt b) ha hb
    rwa [← map_mul] at this
  one_mem' := by
    simp only [Set.mem_ofPred_eq, top_le_iff_mem] at *
    intro z
    rw [map_one, Hom.one_def]
    simpa using hF.one _
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, top_le_iff_mem] at *
    have := hF.inv _ (Γ.pt a) ha
    rwa [← map_inv] at this

end GlobalTheory.CompanionTheory.Ar.BT.SubOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.SubOrder

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem valHom_congr {B : Type} [CommRing B] {X : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) : valHom x U h = valHom y U h' := by
  subst e; rfl

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec]`. Conclude with `⟨z, rfl⟩`.
-/
theorem fromSpec_mem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (z) : hU.fromSpec z ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨z, rfl⟩

section sec

variable (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hU : IsAffineOpen U)

noncomputable def secRho : R →+* Γ(Γ.G.left, U) :=
  (Spec.preimage (hU.fromSpec ≫ Γ.G.hom)).hom

/- English proof (translation)
Simplify using `[secRho]`.
-/
theorem fromSpec_hom : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (secRho Γ hU)) := by
  simp [secRho]

variable {Γ hU}
variable [Algebra R Γ(Γ.G.left, U)]
  (hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))))

include hρ

/- English proof (translation)
Establish `e1` using `spec_valHom_fromSpec (Γ.pt t).left hU h`. Establish `e2 : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))` using `Over.w (Γ.pt t)`. Rewrite `e2` using `[← e1, Category.assoc, hρ, ← Spec.map_comp]`. Use `congrArg (fun f => f.hom r) (Spec.map_injective e2)` as an intermediate fact. Simplify using `using this`.
-/
theorem val_algebraMap (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (r : R) :
    valHom (Γ.pt t).left U h (algebraMap R _ r) = algebraMap R (FractionRing R) r := by
  have e1 := spec_valHom_fromSpec (Γ.pt t).left hU h
  have e2 : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    Over.w (Γ.pt t)
  rw [← e1, Category.assoc, hρ, ← Spec.map_comp] at e2
  have := congrArg (fun f => f.hom r) (Spec.map_injective e2)
  simpa using this

noncomputable def valAlg (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) : Γ(Γ.G.left, U) →ₐ[R] FractionRing R :=
  { valHom (Γ.pt t).left U h with commutes' := val_algebraMap hρ t h }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valAlg_apply (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (s) :
    valAlg hρ t h s = valAt (Γ.pt t).left U h s := rfl

/- English proof (translation)
Use `hF.finite` as an intermediate fact. Establish `h : IsFinite (hU.fromSpec ≫ Γ.G.hom)`. Rewrite using `[← hU.isoSpec_inv_ι, Category.assoc]`. Use `infer_instance`. Rewrite `h` using `[hρ]`.

Conclude with `RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h)`.
-/
theorem sec_finite (hF : Γ.IsFinOpenSub U) : Module.Finite R Γ(Γ.G.left, U) := by
  have := hF.finite
  have h : IsFinite (hU.fromSpec ≫ Γ.G.hom) := by
    rw [← hU.isoSpec_inv_ι, Category.assoc]
    infer_instance
  rw [hρ] at h
  exact RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h)

/- English proof (translation)
Use `Γ.flat` as an intermediate fact. Use `Γ.finPres` as an intermediate fact. Use `sec_finite hρ hF` as an intermediate fact. Establish `h : Flat (hU.fromSpec ≫ Γ.G.hom)` using `inferInstance`. Establish `h' : LocallyOfFinitePresentation (hU.fromSpec ≫ Γ.G.hom)` using `inferInstance`.

Rewrite `h`, `h'` using `[hρ]`. Establish `: Module.Flat R Γ(Γ.G.left, U)` using `RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h)`. Establish `: Algebra.FinitePresentation R Γ(Γ.G.left, U)` using `RingHom.finitePresentation_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h')`. Use `Module.FinitePresentation.of_finite_of_finitePresentation R Γ(Γ.G.left, U)` as an intermediate fact. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem sec_projective (hF : Γ.IsFinOpenSub U) : Module.Projective R Γ(Γ.G.left, U) := by
  have := Γ.flat
  have := Γ.finPres
  have := sec_finite hρ hF
  have h : Flat (hU.fromSpec ≫ Γ.G.hom) := inferInstance
  have h' : LocallyOfFinitePresentation (hU.fromSpec ≫ Γ.G.hom) := inferInstance
  rw [hρ] at h h'
  have : Module.Flat R Γ(Γ.G.left, U) := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h)
  have : Algebra.FinitePresentation R Γ(Γ.G.left, U) :=
    RingHom.finitePresentation_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h')
  have := Module.FinitePresentation.of_finite_of_finitePresentation R Γ(Γ.G.left, U)
  exact Module.Flat.projective_of_finitePresentation

end sec

end GlobalTheory.CompanionTheory.Ar.BT.SubOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.SubOrder

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

section sec

variable {Γ : QFGroup R T} {U : Γ.G.left.Opens} {hU : IsAffineOpen U}
variable [Algebra R Γ(Γ.G.left, U)]
  (hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))))

include hρ

/- English proof (translation)
Set `B` to `Γ(Γ.G.left, U)`. Set `Q : Over (Spec (CommRingCat.of R))` to `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B))))`. Set `iL : B →+* B ⊗[R] B` to `(Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom`. Set `iR : B →+* B ⊗[R] B` to `(Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom`. Set `x : Q ⟶ Γ.G` to `Over.homMk (Spec.map (CommRingCat.ofHom iL) ≫ hU.fromSpec) (by`.

Simplify using `only [Category.assoc, Q, Over.mk_hom]`. Rewrite using `[hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2)`. Set `y : Q ⟶ Γ.G` to `Over.homMk (Spec.map (CommRingCat.ofHom iR) ≫ hU.fromSpec) (by`. Simplify using `only [Category.assoc, Q, Over.mk_hom]`.

Rewrite using `[hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `r`. Simplify using `[iR, Algebra.TensorProduct.algebraMap_apply'])`. Establish `hx : ∀ z, x.left z ∈ U` using `fun z => by`.

Simplify `fromSpec_mem hU _` using `[x]`. Establish `hy : ∀ z, y.left z ∈ U` using `fun z => by`. Simplify `fromSpec_mem hU _` using `[y]`. Establish `hm` using `hF.mul Q x y hx hy`. Use `⟨valHom (x * y).left U ((top_le_iff_mem _ _).2 hm) s, ?_⟩` and prove the remaining obligations.

Introduce `a b ha hb hab`. Set `φ : B ⊗[R] B →+* FractionRing R` to `(Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb)).toRingHom`. Set `w : genPt R ⟶ Q` to `Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by`. Simplify using `only [Q, Over.mk_hom, genPt]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use extensionality with `r`. Simplify using `[φ])`. Establish `hwx : w ≫ x = Γ.pt a`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Simplify using `only [Over.comp_left, w, x, Over.homMk_left]`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: φ.comp iL = valHom (Γ.pt a).left U ha`. Use extensionality with `r`. Simplify using `[φ, iL]`.

Apply the tactic sequence `try rfl`. Rewrite using `[this]`. Conclude with `spec_valHom_fromSpec _ hU ha`. Establish `hwy : w ≫ y = Γ.pt b`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Simplify using `only [Over.comp_left, w, y, Over.homMk_left]`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: φ.comp iR = valHom (Γ.pt b).left U hb`. Use extensionality with `r`. Simplify using `[φ, iR]`.

Apply the tactic sequence `try rfl`. Rewrite using `[this]`. Conclude with `spec_valHom_fromSpec _ hU hb`. Establish `hw : w ≫ (x * y) = Γ.pt (a * b)`. Rewrite using `[MonObj.comp_mul, hwx, hwy, map_mul]`.

Establish `e : (Γ.pt (a * b)).left = Spec.map (CommRingCat.ofHom φ) ≫ (x * y).left`. Rewrite using `[← hw]`. Both sides reduce to the same expression. Establish `h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ (x * y).left) ⁻¹ᵁ U` using `e ▸ hab`. Rewrite using `[← valHom_apply, valHom_congr e U hab h', valHom_comp (x * y).left hU ((top_le_iff_mem _ _).2 hm) φ h' s]`.

Both sides reduce to the same expression.
-/
theorem exists_tensor (hF : Γ.IsFinOpenSub U) (s : Γ(Γ.G.left, U)) :
    ∃ c : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∀ (a b : T) (ha : ⊤ ≤ (Γ.pt a).left ⁻¹ᵁ U)
      (hb : ⊤ ≤ (Γ.pt b).left ⁻¹ᵁ U) (hab : ⊤ ≤ (Γ.pt (a * b)).left ⁻¹ᵁ U),
      valAt (Γ.pt (a * b)).left U hab s =
        Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb) c := by
  let B := Γ(Γ.G.left, U)
  let Q : Over (Spec (CommRingCat.of R)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B))))
  let iL : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom
  let iR : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom
  let x : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iL) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2)
  let y : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iR) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [iR, Algebra.TensorProduct.algebraMap_apply'])
  have hx : ∀ z, x.left z ∈ U := fun z => by
    simpa [x] using fromSpec_mem hU _
  have hy : ∀ z, y.left z ∈ U := fun z => by
    simpa [y] using fromSpec_mem hU _
  have hm := hF.mul Q x y hx hy
  refine ⟨valHom (x * y).left U ((top_le_iff_mem _ _).2 hm) s, ?_⟩
  intro a b ha hb hab
  let φ : B ⊗[R] B →+* FractionRing R :=
    (Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb)).toRingHom
  let w : genPt R ⟶ Q := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    simp only [Q, Over.mk_hom, genPt]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [φ])
  have hwx : w ≫ x = Γ.pt a := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, x, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iL = valHom (Γ.pt a).left U ha := by
      ext r
      simp [φ, iL]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU ha
  have hwy : w ≫ y = Γ.pt b := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, y, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iR = valHom (Γ.pt b).left U hb := by
      ext r
      simp [φ, iR]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU hb
  have hw : w ≫ (x * y) = Γ.pt (a * b) := by
    rw [MonObj.comp_mul, hwx, hwy, map_mul]
  have e : (Γ.pt (a * b)).left = Spec.map (CommRingCat.ofHom φ) ≫ (x * y).left := by
    rw [← hw]; rfl
  have h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ (x * y).left) ⁻¹ᵁ U := e ▸ hab
  rw [← valHom_apply, valHom_congr e U hab h',
    valHom_comp (x * y).left hU ((top_le_iff_mem _ _).2 hm) φ h' s]
  rfl

/- English proof (translation)
Set `B` to `Γ(Γ.G.left, U)`. Set `Q : Over (Spec (CommRingCat.of R))` to `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))`. Set `x : Q ⟶ Γ.G` to `Over.homMk hU.fromSpec hρ`. Establish `hx : ∀ z, x.left z ∈ U` using `fun z => fromSpec_mem hU _`. Establish `hm` using `hF.inv Q x hx`.

Use `⟨valHom (x⁻¹).left U ((top_le_iff_mem _ _).2 hm) s, ?_⟩` and prove the remaining obligations. Introduce `a ha ha'`. Set `φ : B →+* FractionRing R` to `(valAlg hρ a ha).toRingHom`. Set `w : genPt R ⟶ Q` to `Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by`. Simplify using `only [Q, Over.mk_hom, genPt]`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `r`. Simplify using `[φ])`. Establish `hwx : w ≫ x = Γ.pt a`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `spec_valHom_fromSpec _ hU ha`. Establish `hw : w ≫ x⁻¹ = Γ.pt a⁻¹`. Rewrite using `[GrpObj.comp_inv, hwx, map_inv]`. Establish `e : (Γ.pt a⁻¹).left = Spec.map (CommRingCat.ofHom φ) ≫ (x⁻¹).left`.

Rewrite using `[← hw]`. Both sides reduce to the same expression. Establish `h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ (x⁻¹).left) ⁻¹ᵁ U` using `e ▸ ha'`. Rewrite using `[← valHom_apply, valHom_congr e U ha' h', valHom_comp (x⁻¹).left hU ((top_le_iff_mem _ _).2 hm) φ h' s]`. Both sides reduce to the same expression.
-/
theorem exists_inv (hF : Γ.IsFinOpenSub U) (s : Γ(Γ.G.left, U)) :
    ∃ c : Γ(Γ.G.left, U), ∀ (a : T) (ha : ⊤ ≤ (Γ.pt a).left ⁻¹ᵁ U) (ha' : ⊤ ≤ (Γ.pt a⁻¹).left ⁻¹ᵁ U),
      valAt (Γ.pt a⁻¹).left U ha' s = valAlg hρ a ha c := by
  let B := Γ(Γ.G.left, U)
  let Q : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  let x : Q ⟶ Γ.G := Over.homMk hU.fromSpec hρ
  have hx : ∀ z, x.left z ∈ U := fun z => fromSpec_mem hU _
  have hm := hF.inv Q x hx
  refine ⟨valHom (x⁻¹).left U ((top_le_iff_mem _ _).2 hm) s, ?_⟩
  intro a ha ha'
  let φ : B →+* FractionRing R := (valAlg hρ a ha).toRingHom
  let w : genPt R ⟶ Q := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    simp only [Q, Over.mk_hom, genPt]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [φ])
  have hwx : w ≫ x = Γ.pt a := by
    apply Over.OverMorphism.ext
    exact spec_valHom_fromSpec _ hU ha
  have hw : w ≫ x⁻¹ = Γ.pt a⁻¹ := by
    rw [GrpObj.comp_inv, hwx, map_inv]
  have e : (Γ.pt a⁻¹).left = Spec.map (CommRingCat.ofHom φ) ≫ (x⁻¹).left := by
    rw [← hw]; rfl
  have h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ (x⁻¹).left) ⁻¹ᵁ U := e ▸ ha'
  rw [← valHom_apply, valHom_congr e U ha' h',
    valHom_comp (x⁻¹).left hU ((top_le_iff_mem _ _).2 hm) φ h' s]
  rfl

end sec

end GlobalTheory.CompanionTheory.Ar.BT.SubOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.SubOrder

/- English proof (translation)
Use `Scheme.Hom.appLE_comp_appLE x f V W ⊤ e h` as an intermediate fact. Simplify using `only [valHom, RingHom.comp_apply]`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem valHom_appLE {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    {V : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ V) (h : ⊤ ≤ x ⁻¹ᵁ W) (h2 : ⊤ ≤ (x ≫ f) ⁻¹ᵁ V) (s : Γ(Y, V)) :
    valHom x W h ((f.appLE V W e).hom s) = valHom (x ≫ f) V h2 s := by
  have := Scheme.Hom.appLE_comp_appLE x f V W ⊤ e h
  simp only [valHom, RingHom.comp_apply]
  rw [← this]
  rfl

/- English proof (translation)
Establish `e` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)`. Establish `e0 : (Spec.map (CommRingCat.ofHom ψ)).appLE ⊤ ⊤ h = (Spec.map (CommRingCat.ofHom ψ)).appTop` using `Scheme.Hom.appLE_eq_app _`. Establish `e1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom ψ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom ψ`. Rewrite using `[← Category.assoc, ← e]`. Simplify using the standard rewrite rules.

Use `congrArg (fun f => f.hom r) e1` as an intermediate fact. Simplify using `only [valHom, RingHom.comp_apply, e0]`. Conclude with `this`.
-/
theorem valHom_spec_top {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ)) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens)) (r : A) :
    valHom (Spec.map (CommRingCat.ofHom ψ)) ⊤ h ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) = ψ r := by
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have e0 : (Spec.map (CommRingCat.ofHom ψ)).appLE ⊤ ⊤ h = (Spec.map (CommRingCat.ofHom ψ)).appTop :=
    Scheme.Hom.appLE_eq_app _
  have e1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom ψ)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom ψ := by
    rw [← Category.assoc, ← e]
    simp
  have := congrArg (fun f => f.hom r) e1
  simp only [valHom, RingHom.comp_apply, e0]
  exact this

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

/- English proof (translation)
Take `⟨V, hg, s, hs⟩` from `h`. Establish `e : V ≤ Γ.G.hom ⁻¹ᵁ ⊤` using `by simp`. Use `⟨V, hg, (Γ.G.hom.appLE ⊤ V e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) * s, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite using `[← valHom_apply, map_mul, valHom_apply _ _ _ s, hs t ht]`. Use `congr 1`.

Establish `e2 : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))` using `Over.w (Γ.pt t)`. Establish `h2 : ⊤ ≤ ((Γ.pt t).left ≫ Γ.G.hom) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)` using `by simp`. Establish `h3 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)` using `by simp`. Rewrite using `[valHom_appLE _ _ e ht h2, valHom_congr e2 _ h2 h3, valHom_spec_top]`.
-/
theorem regularAt_mul (Γ : QFGroup R T) (d : R) {f : T → FractionRing R} {g : Γ.G.left} (h : Γ.RegularAt f g) :
    Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  obtain ⟨V, hg, s, hs⟩ := h
  have e : V ≤ Γ.G.hom ⁻¹ᵁ ⊤ := by simp
  refine ⟨V, hg, (Γ.G.hom.appLE ⊤ V e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) * s, fun t ht => ?_⟩
  rw [← valHom_apply, map_mul, valHom_apply _ _ _ s, hs t ht]
  congr 1
  have e2 : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    Over.w (Γ.pt t)
  have h2 : ⊤ ≤ ((Γ.pt t).left ≫ Γ.G.hom) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := by simp
  have h3 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) ⁻¹ᵁ
    (⊤ : (Spec (CommRingCat.of R)).Opens) := by simp
  rw [valHom_appLE _ _ e ht h2, valHom_congr e2 _ h2 h3, valHom_spec_top]

/- English proof (translation)
It suffices to establish `H : ∃ d : R, d ≠ 0 ∧ ∀ g ∈ (U : Set Γ.G.left), Γ.RegularAt (fun t => algebraMap R _ d * f t) g from H`. Use `hc.induction_on (p := fun S => ∃ d : R, d ≠ 0 ∧ ∀ g ∈ S, Γ.RegularAt (fun t => algebraMap R _ d * f t) g) ⟨1, one_ne_zero, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `S S' hS ⟨d, hd, h⟩`. Conclude with `⟨d, hd, fun g hg => h g (hS hg)⟩`. Introduce and unpack `S S' ⟨d, hd, h⟩ ⟨d', hd', h'⟩`.

Use `⟨d * d', mul_ne_zero hd hd', ?_⟩` and prove the remaining obligations. Introduce and unpack `g (hg | hg)`. Use `regularAt_mul Γ d' (h g hg)` as an intermediate fact. Simplify `this` using `[mul_assoc, mul_comm, mul_left_comm]`. Use `regularAt_mul Γ d (h' g hg)` as an intermediate fact.

Simplify `this` using `[mul_assoc, mul_comm, mul_left_comm]`. Introduce `g _`. Take `⟨d, hd, V, hg, s, hs⟩` from `GlobalTheory.T.exists_denominator_regular R T Γ f g`. Use `⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hg), d, hd, fun g' hg' => ⟨V, hg', s, hs⟩⟩` and prove the remaining obligations.
-/
theorem exists_den [Finite T] (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hc : IsCompact (U : Set Γ.G.left))
    (f : T → FractionRing R) : ∃ d : R, d ≠ 0 ∧ ∀ g ∈ U, Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  suffices H : ∃ d : R, d ≠ 0 ∧ ∀ g ∈ (U : Set Γ.G.left), Γ.RegularAt (fun t => algebraMap R _ d * f t) g from H
  refine hc.induction_on (p := fun S => ∃ d : R, d ≠ 0 ∧ ∀ g ∈ S, Γ.RegularAt (fun t => algebraMap R _ d * f t) g)
    ⟨1, one_ne_zero, by simp⟩ ?_ ?_ ?_
  · rintro S S' hS ⟨d, hd, h⟩
    exact ⟨d, hd, fun g hg => h g (hS hg)⟩
  · rintro S S' ⟨d, hd, h⟩ ⟨d', hd', h'⟩
    refine ⟨d * d', mul_ne_zero hd hd', ?_⟩
    rintro g (hg | hg)
    · have := regularAt_mul Γ d' (h g hg)
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    · have := regularAt_mul Γ d (h' g hg)
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
  · intro g _
    obtain ⟨d, hd, V, hg, s, hs⟩ := GlobalTheory.T.exists_denominator_regular R T Γ f g
    refine ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hg), d, hd, fun g' hg' => ⟨V, hg', s, hs⟩⟩

end GlobalTheory.CompanionTheory.Ar.BT.SubOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.SubOrder

/- English proof (translation)
Introduce `R _ _ _ T _ _ Γ U hF`. Establish `hU` using `isAffineOpen_of_fin Γ hF`. Use `letI : Algebra R Γ(Γ.G.left, U) := (secRho Γ hU).toAlgebra`. Establish `hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U)))` using `fromSpec_hom Γ hU`. Establish `hfin` using `sec_finite hρ hF`.

Establish `hproj` using `sec_projective hρ hF`. Establish `inj : Function.Injective (algebraMap R (FractionRing R))` using `IsFractionRing.injective R _`. Establish `hval : ∀ (t : subH Γ hF) (s : Γ(Γ.G.left, U)), ∃ r : R, algebraMap R (FractionRing R) r = valAlg hρ t t.2 s`. Introduce `t s`. Establish `h1 : IsIntegral R s` using `Algebra.IsIntegral.isIntegral s`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t t.2))`. Use `choose Φf hΦf using hval`. Set `Φ : Γ(Γ.G.left, U) →ₐ[R] (subH Γ hF → R)` to `{ toFun := fun s t => Φf t s map_one' := funext fun t => inj (by simp [hΦf]) map_mul' := fun a b => funext fun t => inj (by simp [hΦf]) map_zero' := funext fun t => inj (by simp [hΦf]) map_add' := fun a b => funext fun t => inj (by simp [hΦf]) commutes' := fun r => funext fun t = …`. Rewrite using `[hΦf, AlgHom.commutes]`. Use the proof step `rfl) }`.

Establish `hΦ : ∀ (s : Γ(Γ.G.left, U)) (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (Φ s t)` using `fun s t h => (hΦf t s).symm`. Establish `hA : ∀ f : subH Γ hF → R, f ∈ Φ.range ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t)`. Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`.

Conclude with `⟨s, fun t h => hΦ s t h⟩`. Introduce and unpack `⟨s, hs⟩`. Conclude with `⟨s, funext fun t => inj ((hΦ s t t.2).symm.trans (hs t t.2))⟩`. Establish `hinj : Function.Injective Φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `s hs`. Use `GlobalTheory.T.section_eq_zero_of_values R T Γ U s fun t h => ?_` and prove the remaining obligations. Use `hΦ s ⟨t, h⟩ h` as an intermediate fact. Rewrite `this` using `[hs]`. Simplify using `using this`.

Use `⟨subH Γ hF, Φ.range, fun t => Iff.rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, hA⟩` and prove the remaining obligations. Conclude with `Module.Finite.of_surjective Φ.rangeRestrict.toLinearMap Φ.rangeRestrict_surjective`. Conclude with `Module.Projective.of_equiv (AlgEquiv.ofInjective Φ hinj).toLinearEquiv`. Use `Fintype.ofFinite (subH Γ hF)` as an intermediate fact. Establish `hc : IsCompact (U : Set Γ.G.left)` using `hU.isCompact`.

Establish `h1 : ∀ h : subH Γ hF, ∃ d : R, d ≠ 0 ∧ d • (Pi.single h 1 : subH Γ hF → R) ∈ Φ.range`. Introduce `h`. Take `⟨d, hd, hreg⟩` from `exists_den Γ hc (fun t => if t = (h : T) then 1 else 0)`. Take `⟨s, hs⟩` from `(GlobalTheory.T.regular_function_iff_section R T Γ U _).1 hreg`. Use `⟨d, hd, (hA _).2 ⟨s, fun t ht => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hs t ht]`. Distinguish the cases in `e : t = h`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Establish `: (t : T) ≠ h` using `fun e' => e (Subtype.ext e')`.

Simplify using `[e, this]`. Use `choose d hd hdA using h1`. Use `⟨∏ h, d h, Finset.prod_ne_zero_iff.2 fun h _ => hd h, fun f => ?_⟩` and prove the remaining obligations. Establish `e : (∏ h, d h) • f = ∑ h, (f h * ∏ h' ∈ Finset.univ.erase h, d h') • (d h • (Pi.single h 1 : subH Γ hF → R))`. Use function extensionality and compare the values at `t`.

Simplify using `only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single t]`. Rewrite using `[Pi.single_eq_same, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ t)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`.

Simplify using `[Pi.single_eq_of_ne hb.symm]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Subalgebra.sum_mem _ fun h _ => Subalgebra.smul_mem _ (hdA h) _`. Introduce and unpack `_ ⟨s, rfl⟩`.

Take `⟨c, hc⟩` from `exists_tensor hρ hF s`. Establish `key : ∀ c' : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∃ g ∈ prodSpan Φ.range, ∀ z : subH Γ hF × subH Γ hF, algebraMap R (FractionRing R) (g z) = Algebra.TensorProduct.productMap (valAlg hρ z.1 z.1.2) (valAlg hρ z.2 z.2.2) c'`. Introduce `c'`. Proceed by induction on `c' with`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, fun z => by simp⟩`.

Consider the case `tmul a b`. Use `⟨fun z => Φ a z.1 * Φ b z.2, Submodule.subset_span ⟨Φ a, ⟨a, rfl⟩, Φ b, ⟨b, rfl⟩, rfl⟩, fun z => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, Algebra.TensorProduct.productMap_apply_tmul]`. Conclude with `congrArg₂ (· * ·) (hΦ a z.1 z.1.2).symm (hΦ b z.2 z.2.2).symm`. Consider the case `add a b ha hb`.

Take `⟨g, hg, hg'⟩` from `ha`. Take `⟨g₂, hg₂, hg₂'⟩` from `hb`. Conclude with `⟨g + g₂, Submodule.add_mem _ hg hg₂, fun z => by simp [hg', hg₂']⟩`. Take `⟨g, hg, hg'⟩` from `key c`. Establish `: (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) = g`.

Use function extensionality and compare the values at `z`. Apply `inj` to reduce the goal to its premises. Rewrite using `[hg' z, ← hc z.1 z.2 z.1.2 z.2.2 (z.1 * z.2).2]`. Conclude with `(hΦ s (z.1 * z.2) (z.1 * z.2).2).symm`. Express the relevant statement in the definitionally equal form `(fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) ∈ prodSpan Φ.range`.

Rewrite using `[this]`. Conclude with `hg`. Introduce and unpack `_ ⟨s, rfl⟩`. Take `⟨c, hc⟩` from `exists_inv hρ hF s`. Use `⟨c, funext fun x => inj ?_⟩` and prove the remaining obligations.

Establish `e1` using `hc x x.2 (x⁻¹).2`. Establish `e2` using `hΦ s x⁻¹ (x⁻¹).2`. Establish `e3` using `hΦ c x x.2`. Conclude with `e3.symm.trans (Eq.trans (valAlg_apply hρ _ _ _).symm (e1.symm.trans e2))`.
-/
theorem hopfOrder_of_finOpenSub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∃ (H : Subgroup T) (A : Subalgebra R (H → R)), (∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧ ∀ f : H → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : H) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  intro R _ _ _ T _ _ Γ U hF
  have hU := isAffineOpen_of_fin Γ hF
  letI : Algebra R Γ(Γ.G.left, U) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
    fromSpec_hom Γ hU
  have hfin := sec_finite hρ hF
  have hproj := sec_projective hρ hF
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hval : ∀ (t : subH Γ hF) (s : Γ(Γ.G.left, U)),
      ∃ r : R, algebraMap R (FractionRing R) r = valAlg hρ t t.2 s := by
    intro t s
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t t.2))
  choose Φf hΦf using hval
  let Φ : Γ(Γ.G.left, U) →ₐ[R] (subH Γ hF → R) :=
    { toFun := fun s t => Φf t s
      map_one' := funext fun t => inj (by simp [hΦf])
      map_mul' := fun a b => funext fun t => inj (by simp [hΦf])
      map_zero' := funext fun t => inj (by simp [hΦf])
      map_add' := fun a b => funext fun t => inj (by simp [hΦf])
      commutes' := fun r => funext fun t => inj (by
        rw [hΦf, AlgHom.commutes]; rfl) }
  have hΦ : ∀ (s : Γ(Γ.G.left, U)) (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
      valAt (Γ.pt t).left U h s = algebraMap R _ (Φ s t) := fun s t h => (hΦf t s).symm
  have hA : ∀ f : subH Γ hF → R, f ∈ Φ.range ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : subH Γ hF)
      (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
    intro f
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, fun t h => hΦ s t h⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, funext fun t => inj ((hΦ s t t.2).symm.trans (hs t t.2))⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ U s fun t h => ?_
    have := hΦ s ⟨t, h⟩ h
    rw [hs] at this
    simpa using this
  refine ⟨subH Γ hF, Φ.range, fun t => Iff.rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, hA⟩
  · exact Module.Finite.of_surjective Φ.rangeRestrict.toLinearMap Φ.rangeRestrict_surjective
  · exact Module.Projective.of_equiv (AlgEquiv.ofInjective Φ hinj).toLinearEquiv
  · classical
    have := Fintype.ofFinite (subH Γ hF)
    have hc : IsCompact (U : Set Γ.G.left) := hU.isCompact
    have h1 : ∀ h : subH Γ hF, ∃ d : R, d ≠ 0 ∧ d • (Pi.single h 1 : subH Γ hF → R) ∈ Φ.range := by
      intro h
      obtain ⟨d, hd, hreg⟩ := exists_den Γ hc (fun t => if t = (h : T) then 1 else 0)
      obtain ⟨s, hs⟩ := (GlobalTheory.T.regular_function_iff_section R T Γ U _).1 hreg
      refine ⟨d, hd, (hA _).2 ⟨s, fun t ht => ?_⟩⟩
      rw [hs t ht]
      by_cases e : t = h
      · subst e; simp
      · have : (t : T) ≠ h := fun e' => e (Subtype.ext e')
        simp [e, this]
    choose d hd hdA using h1
    refine ⟨∏ h, d h, Finset.prod_ne_zero_iff.2 fun h _ => hd h, fun f => ?_⟩
    have e : (∏ h, d h) • f = ∑ h, (f h * ∏ h' ∈ Finset.univ.erase h, d h') • (d h • (Pi.single h 1 : subH Γ hF → R)) := by
      funext t
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_single t]
      · rw [Pi.single_eq_same, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ t)]
        ring
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [e]
    exact Subalgebra.sum_mem _ fun h _ => Subalgebra.smul_mem _ (hdA h) _
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_tensor hρ hF s
    have key : ∀ c' : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∃ g ∈ prodSpan Φ.range, ∀ z : subH Γ hF × subH Γ hF,
        algebraMap R (FractionRing R) (g z) =
          Algebra.TensorProduct.productMap (valAlg hρ z.1 z.1.2) (valAlg hρ z.2 z.2.2) c' := by
      intro c'
      induction c' with
      | zero => exact ⟨0, Submodule.zero_mem _, fun z => by simp⟩
      | tmul a b =>
        refine ⟨fun z => Φ a z.1 * Φ b z.2, Submodule.subset_span ⟨Φ a, ⟨a, rfl⟩, Φ b, ⟨b, rfl⟩, rfl⟩, fun z => ?_⟩
        simp only [map_mul, Algebra.TensorProduct.productMap_apply_tmul]
        exact congrArg₂ (· * ·) (hΦ a z.1 z.1.2).symm (hΦ b z.2 z.2.2).symm
      | add a b ha hb =>
        obtain ⟨g, hg, hg'⟩ := ha
        obtain ⟨g₂, hg₂, hg₂'⟩ := hb
        exact ⟨g + g₂, Submodule.add_mem _ hg hg₂, fun z => by simp [hg', hg₂']⟩
    obtain ⟨g, hg, hg'⟩ := key c
    have : (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) = g := by
      funext z
      apply inj
      rw [hg' z, ← hc z.1 z.2 z.1.2 z.2.2 (z.1 * z.2).2]
      exact (hΦ s (z.1 * z.2) (z.1 * z.2).2).symm
    change (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) ∈ prodSpan Φ.range
    rw [this]
    exact hg
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_inv hρ hF s
    refine ⟨c, funext fun x => inj ?_⟩
    have e1 := hc x x.2 (x⁻¹).2
    have e2 := hΦ s x⁻¹ (x⁻¹).2
    have e3 := hΦ c x x.2
    exact e3.symm.trans (Eq.trans (valAlg_apply hρ _ _ _).symm (e1.symm.trans e2))

end GlobalTheory.CompanionTheory.Ar.BT.SubOrder
