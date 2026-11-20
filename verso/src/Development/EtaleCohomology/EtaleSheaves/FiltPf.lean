import Development.EtaleCohomology.EtaleSheaves.TruncationPieces
import Development.EtaleCohomology.EtaleSheaves.LeafConeZeroPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces

namespace LateralTheory.E.FiltPf

namespace Tri

open Pretriangulated
universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]

def RelY (Y : ℤ → D) (n : ℤ) {A B : D} (g : A ⟶ B) : Prop :=
  Function.Surjective (fun x : B ⟶ Y (n - 1) => g ≫ x) ∧ Function.Injective (fun x : B ⟶ Y n => g ≫ x)

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x hx; exact h (by simpa using hx)`. Introduce `h x y hxy`. Use `h (x - y) (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.2 hxy)` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem inj_iff {A B X : D} (g : A ⟶ B) :
    Function.Injective (fun x : B ⟶ X => g ≫ x) ↔ ∀ x : B ⟶ X, g ≫ x = 0 → x = 0 := by
  constructor
  · intro h x hx; exact h (by simpa using hx)
  · intro h x y hxy
    have := h (x - y) (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.2 hxy)
    exact sub_eq_zero.1 this

/- English proof (translation)
Establish `hci` using `(inj_iff _).1 hc.2`. Establish `hai` using `(inj_iff _).1 ha.2`. Use `⟨fun x => ?_, (inj_iff _).2 fun d hd => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `ha.1 (T₁.mor₁ ≫ x)`. Simplify using `only at hy`.

Establish `ho : T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y ≫ (e n).inv = 0`. Apply `hci` to reduce the goal to its premises. Rewrite using `[← Category.assoc, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc, hy, Functor.map_comp_assoc, ← Category.assoc, comp_distTriang_mor_zero₃₁ T₁ h₁, zero_comp]`. Establish `ho' : T₂.rotate.mor₂ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y = 0`. Use `congrArg (· ≫ (e n).hom) ho` as an intermediate fact.

Simplify using `only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] at this`. Conclude with `this`. Take `⟨g, hg⟩` from `Triangle.yoneda_exact₃ _ (rot_of_distTriang _ h₂) _ ho'`. Take `⟨(z : T₂.obj₂ ⟶ Y (n - 1)), rfl⟩` from `(CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective g`. Establish `hyz : y = T₂.mor₁ ≫ (-z)`.

Apply `(CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective` to reduce the goal to its premises. Rewrite using `[hg]`. Simplify using `only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]`. Conclude with `Preadditive.neg_comp _ _`. Establish `hw : T₁.mor₁ ≫ (x - φ.hom₂ ≫ (-z)) = 0`.

Rewrite using `[Preadditive.comp_sub, ← hy, hyz, ← Category.assoc, ← φ.comm₁, Category.assoc, sub_self]`. Take `⟨w, hw⟩` from `Triangle.yoneda_exact₂ _ h₁ _ hw`. Take `⟨w', hw'⟩` from `hc.1 w`. Simplify using `only at hw'`. Use `⟨-z + T₂.mor₂ ≫ w', ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[Preadditive.comp_add, ← Category.assoc, ← φ.comm₂, Category.assoc, hw', ← hw]`. Normalize the expressions using the abelian group laws. Establish `h1 : T₂.mor₁ ≫ d = 0`. Apply `hai` to reduce the goal to its premises.

Rewrite using `[← Category.assoc, ← φ.comm₁, Category.assoc, hd, comp_zero]`. Take `⟨h, rfl⟩` from `Triangle.yoneda_exact₂ _ h₂ _ h1`. Establish `h3 : T₁.mor₂ ≫ φ.hom₃ ≫ h = 0`. Rewrite using `[← Category.assoc, φ.comm₂, Category.assoc, hd]`. Take `⟨k, hk⟩` from `Triangle.yoneda_exact₃ _ h₁ _ h3`.

Take `⟨k', hk'⟩` from `(CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (k ≫ (e n).hom)`. Take `⟨k'', hk''⟩` from `ha.1 k'`. Simplify using `only at hk''`. Establish `hm : h = T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map k'' ≫ (e n).inv`. Rewrite using `[← sub_eq_zero]`.

Apply `hci` to reduce the goal to its premises. Rewrite using `[Preadditive.comp_sub, hk, ← Category.assoc φ.hom₃, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc, hk'', hk', Category.assoc, Iso.hom_inv_id, Category.comp_id, sub_self]`. Rewrite using `[hm, ← Category.assoc, comp_distTriang_mor_zero₂₃ _ h₂, zero_comp]`.
-/
theorem relY_mid (T₁ T₂ : Triangle D) (h₁ : T₁ ∈ distTriang D) (h₂ : T₂ ∈ distTriang D) (φ : T₁ ⟶ T₂)
    (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧) (n : ℤ)
    (ha : RelY Y n φ.hom₁) (hc : RelY Y n φ.hom₃) : RelY Y n φ.hom₂ := by
  have hci := (inj_iff _).1 hc.2
  have hai := (inj_iff _).1 ha.2
  refine ⟨fun x => ?_, (inj_iff _).2 fun d hd => ?_⟩
  · obtain ⟨y, hy⟩ := ha.1 (T₁.mor₁ ≫ x)
    simp only at hy
    have ho : T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y ≫ (e n).inv = 0 := by
      apply hci
      rw [← Category.assoc, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc, hy, Functor.map_comp_assoc,
        ← Category.assoc, comp_distTriang_mor_zero₃₁ T₁ h₁, zero_comp]
    have ho' : T₂.rotate.mor₂ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y = 0 := by
      have := congrArg (· ≫ (e n).hom) ho
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] at this
      exact this
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ h₂) _ ho'
    obtain ⟨(z : T₂.obj₂ ⟶ Y (n - 1)), rfl⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective g
    have hyz : y = T₂.mor₁ ≫ (-z) := by
      apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
      rw [hg]
      simp only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]
      exact Preadditive.neg_comp _ _
    have hw : T₁.mor₁ ≫ (x - φ.hom₂ ≫ (-z)) = 0 := by
      rw [Preadditive.comp_sub, ← hy, hyz, ← Category.assoc, ← φ.comm₁, Category.assoc, sub_self]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ h₁ _ hw
    obtain ⟨w', hw'⟩ := hc.1 w
    simp only at hw'
    refine ⟨-z + T₂.mor₂ ≫ w', ?_⟩
    simp only
    rw [Preadditive.comp_add, ← Category.assoc, ← φ.comm₂, Category.assoc, hw', ← hw]
    abel
  · have h1 : T₂.mor₁ ≫ d = 0 := by
      apply hai
      rw [← Category.assoc, ← φ.comm₁, Category.assoc, hd, comp_zero]
    obtain ⟨h, rfl⟩ := Triangle.yoneda_exact₂ _ h₂ _ h1
    have h3 : T₁.mor₂ ≫ φ.hom₃ ≫ h = 0 := by
      rw [← Category.assoc, φ.comm₂, Category.assoc, hd]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ h₁ _ h3
    obtain ⟨k', hk'⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (k ≫ (e n).hom)
    obtain ⟨k'', hk''⟩ := ha.1 k'
    simp only at hk''
    have hm : h = T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map k'' ≫ (e n).inv := by
      rw [← sub_eq_zero]
      apply hci
      rw [Preadditive.comp_sub, hk, ← Category.assoc φ.hom₃, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc,
        hk'', hk', Category.assoc, Iso.hom_inv_id, Category.comp_id, sub_self]
    rw [hm, ← Category.assoc, comp_distTriang_mor_zero₂₃ _ h₂, zero_comp]

end Tri

section Bridge
open CochainComplex CochainComplex.HomComplex
variable (R : Type) [CommRing R]

abbrev Yres (F : Shv R) (m : ℤ) : HomotopyCategory (Shv R) (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦m⟧)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]`. Use `congr 1`. Conclude with `(CohomologyClass.homAddEquiv.apply_symm_apply g).symm`.
-/
theorem pull_eq_comp {K L : Cx R} (f : K ⟶ L) (F : Shv R) (m : ℤ) :
    (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶ Yres R F m =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R f F m) ∘ (CohomologyClass.homAddEquiv.symm) := by
  funext g
  simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  congr 1
  exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm

/- English proof (translation)
Unfold `Tri.RelY RelK`. Rewrite using `[pull_eq_comp, pull_eq_comp, EquivLike.comp_surjective, EquivLike.surjective_comp, EquivLike.comp_injective, EquivLike.injective_comp]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩; exact ⟨h1 (n - 1) (by omega), h2⟩`. Introduce and unpack `⟨h1, h2⟩; refine ⟨fun m hm => ?_, h2⟩; obtain rfl : m = n - 1 := (by omega)`.

Conclude with `h1`.
-/
theorem relK_iff {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) :
    RelK R F n f ↔ Tri.RelY (Yres R F) n ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f) := by
  unfold Tri.RelY RelK
  rw [pull_eq_comp, pull_eq_comp, EquivLike.comp_surjective, EquivLike.surjective_comp,
    EquivLike.comp_injective, EquivLike.injective_comp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 (n - 1) (by omega), h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨fun m hm => ?_, h2⟩; obtain rfl : m = n - 1 := (by omega)
    exact h1

def yresIso (F : Shv R) (m : ℤ) : Yres R F m ≅ (Yres R F (m - 1))⟦(1 : ℤ)⟧ :=
  LateralTheory.E.E8.ExciseCut.ConeZeroPf.shIso R (res R F) m

end Bridge

def pieceC (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (K.X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (L.X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (f.f (-(p : ℤ)))

def Tower : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def TowerFin : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ) (P : ℕ),
  (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def Trunc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧
    ((∀ p : ℕ, RelK R F n (pieceC R f p)) → ∀ p : ℕ, RelK R F n (pieceC R f' p)) ∧
    (RelK R F n f' → RelK R F n f)

/- English proof (translation)
Introduce `R _ F K L f n hz hp`. Take `⟨P, K', L', f', hz', hpp, hback⟩` from `hT R F f n hz`. Conclude with `hback (hB R F f' n P hz' (hpp hp))`.
-/
theorem tower_of (hB : TowerFin) (hT : Trunc) : Tower := by
  intro R _ F K L f n hz hp
  obtain ⟨P, K', L', f', hz', hpp, hback⟩ := hT R F f n hz
  exact hback (hB R F f' n P hz' (hpp hp))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)`. Apply `HomologicalComplex.isZero_extend_X` to reduce the goal to its premises. Introduce `j hj`. Establish `e : ComplexShape.embeddingDownNat.f j = -(j : ℤ)` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem chains_X_isZero (R : Type) [CommRing R] (U : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj U).X i) := by
  change IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  have e : ComplexShape.embeddingDownNat.f j = -(j : ℤ) := rfl
  omega

end LateralTheory.E.FiltPf

open LateralTheory.E.FiltPf in
/- English proof (translation)
Introduce `R _ F U E u n h`. Conclude with `hT R F ((chains R).map u) n (fun i hi => ⟨chains_X_isZero R U i hi, chains_X_isZero R E i hi⟩) h`.
-/
theorem LateralTheory.E.TruncationPieces.Filt_of_tower (hT : Tower) : LateralTheory.E.TruncationPieces.Filt := by
  intro R _ F U E u n h
  exact hT R F ((chains R).map u) n (fun i hi => ⟨chains_X_isZero R U i hi, chains_X_isZero R E i hi⟩) h

open LateralTheory.E.FiltPf in
/- English proof (translation)
The claim follows from `LateralTheory.E.TruncationPieces.Filt_of_tower (tower_of hB hT)`.
-/
theorem LateralTheory.E.TruncationPieces.Filt_of (hB : TowerFin) (hT : Trunc) : LateralTheory.E.TruncationPieces.Filt :=
  LateralTheory.E.TruncationPieces.Filt_of_tower (tower_of hB hT)
