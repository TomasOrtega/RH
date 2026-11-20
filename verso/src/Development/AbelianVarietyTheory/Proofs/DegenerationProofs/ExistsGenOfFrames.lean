import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.FrameGen

/- English proof (translation)
Rewrite using `[← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]`. Conclude with `Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _`.
-/
theorem gs_stalk {X X' Y : Scheme.{0}} (r : Y ⟶ X') (β : X' ⟶ X) (z : Y) (U : X.Opens) (h : β (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

def gT {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) : Γ(X, ⊤) →+* Y.presheaf.stalk z :=
  (Y.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom

/- English proof (translation)
The claim follows from `gs_eq r z ⊤ trivial a`.
-/
theorem gs_top {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) (a : Γ(X, ⊤)) : gs r z ⊤ a = gT r z a := gs_eq r z ⊤ trivial a

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gT_comp {X X' Y : Scheme.{0}} (r : Y ⟶ X') (β : X' ⟶ X) (z : Y) (a : Γ(X, ⊤)) :
    gT r z (β.appTop.hom a) = gT (r ≫ β) z a := rfl

variable {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ)

def sv {T : Over Z} (s : LB.Sec (LPow G L (N : ℤ) T)) {Y : Scheme.{0}} (r : Y ⟶ (T ⊗ G).left) (z : Y)
    (J : (Y ⟶ G.left) → L.ι) : Y.presheaf.stalk z :=
  sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s r z J

/- English proof (translation)
Rewrite using `[← Over.comp_left, whiskerRight_snd]`.
-/
theorem wh_snd {T T' : Over Z} (h : T' ⟶ T) : (h ▷ G).left ≫ (snd T G).left = (snd T' G).left := by
  rw [← Over.comp_left, whiskerRight_snd]

/- English proof (translation)
Rewrite using `[← Over.comp_left, whiskerRight_fst, Over.comp_left]`.
-/
theorem wh_fst {T T' : Over Z} (h : T' ⟶ T) : (h ▷ G).left ≫ (fst T G).left = (fst T' G).left ≫ h.left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

/- English proof (translation)
Establish `e₁` using `sval_of (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (r ≫ p) z J' (fun _ => J (p ≫ (snd T G).left)) (fun _ => by rw [Category.assoc, e])`. Conclude with `(gs_stalk r p z _ (hJ.mem (fun _ : Fin 1 => (snd T G).left) p) _).trans e₁.symm`.
-/
theorem sv_stalk {T : Over Z} (s : LB.Sec (LPow G L (N : ℤ) T)) {Y Y' : Scheme.{0}} (p : Y ⟶ (T ⊗ G).left)
    (r : Y' ⟶ Y) (z : Y') {J J'} (hJ : Good L (r z) J) (e : J (p ≫ (snd T G).left) = J' (r ≫ p ≫ (snd T G).left)) :
    (r.stalkMap z).hom (sv G L N s p (r z) J) = sv G L N s (r ≫ p) z J' := by
  have e₁ := sval_of (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (r ≫ p) z J'
    (fun _ => J (p ≫ (snd T G).left)) (fun _ => by rw [Category.assoc, e])
  exact (gs_stalk r p z _ (hJ.mem (fun _ : Fin 1 => (snd T G).left) p) _).trans e₁.symm

variable {G L N}

/- English proof (translation)
Take `⟨J', hJ', e⟩` from `exists_good L hL (r z) (K := PUnit) (fun _ => (snd T' G).left) (fun _ => J (r ≫ (snd T' G).left)) (fun _ _ _ => rfl) (fun _ => hJ (r ≫ (snd T' G).left))`. Establish `e₀` using `congrArg (r.stalkMap z).hom (H (r z) J' hJ')`. Rewrite `e₀` using `[map_sum]`. Establish `e₁` using `sv_stalk G L N s (𝟙 _) r z hJ' (J' := J) (by simpa only [Category.id_comp] using e PUnit.unit)`. Rewrite `e₁` using `[Category.comp_id]`.

Use `e₁.symm.trans (e₀.trans (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[map_mul, gs_stalk r _ z ⊤ trivial, gs_top]`. Conclude with `congrArg _ (sv_stalk G L N (b i) _ r z hJ' (by rw [wh_snd]; exact e PUnit.unit))`.
-/
theorem lin_all (hL : L.IsLB) {T T' : Over Z} {h : T' ⟶ T} {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {c : Fin n → Γ(T'.left, ⊤)} {s} (H : Lin G L N h b c s) {Y : Scheme.{0}} (r : Y ⟶ (T' ⊗ G).left) (z : Y) {J}
    (hJ : Good L z J) :
    sv G L N s r z J = ∑ i, gT (r ≫ (fst T' G).left) z (c i) * sv G L N (b i) (r ≫ (h ▷ G).left) z J := by
  obtain ⟨J', hJ', e⟩ := exists_good L hL (r z) (K := PUnit) (fun _ => (snd T' G).left)
    (fun _ => J (r ≫ (snd T' G).left)) (fun _ _ _ => rfl) (fun _ => hJ (r ≫ (snd T' G).left))
  have e₀ := congrArg (r.stalkMap z).hom (H (r z) J' hJ')
  rw [map_sum] at e₀
  have e₁ := sv_stalk G L N s (𝟙 _) r z hJ' (J' := J) (by simpa only [Category.id_comp] using e PUnit.unit)
  rw [Category.comp_id] at e₁
  refine e₁.symm.trans (e₀.trans (Finset.sum_congr rfl fun i _ => ?_))
  rw [map_mul, gs_stalk r _ z ⊤ trivial, gs_top]
  exact congrArg _ (sv_stalk G L N (b i) _ r z hJ' (by rw [wh_snd]; exact e PUnit.unit))

/- English proof (translation)
Introduce `_ _` and use `(map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.one_mul _)).symm`.
-/
theorem isGen_one {X : Scheme.{0}} (A : LB X) (Y : Scheme.{0}) : (LB.oneGen A (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.one_mul _)).symm

/- English proof (translation)
Establish `one` using `isGen_one L (T' ⊗ G).left`. Take `⟨s, hs⟩` from `exists_sec hL (φ' := fun _ : Fin 1 => (snd T' G).left) (ε' := fun _ => (N : ℤ)) (fun U _ k => by simp [wh_snd]) (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) a (h ▷ G).left _ one)`. Use `⟨s, fun Y r z J hJ => (hs Y r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩` and prove the remaining obligations. Rewrite using `[val_one, Units.val_one, _root_.mul_one]`. Both sides reduce to the same expression.
-/
theorem exists_pull (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) (a : LB.Sec (LPow G L (N : ℤ) T)) :
    ∃ s : LB.Sec (LPow G L (N : ℤ) T'), ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
      sv G L N s r z J = sv G L N a (r ≫ (h ▷ G).left) z J := by
  have one := isGen_one L (T' ⊗ G).left
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T' G).left) (ε' := fun _ => (N : ℤ))
    (fun U _ k => by simp [wh_snd])
    (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) a (h ▷ G).left _ one)
  refine ⟨s, fun Y r z J hJ => (hs Y r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]; rfl

variable (G L N) in

def Rel {T T₁ T₂ : Over Z} {m n : ℕ} (h₁ : T ⟶ T₁) (a : Fin m → LB.Sec (LPow G L (N : ℤ) T₁)) (h₂ : T ⟶ T₂)
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)) (M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)) : Prop :=
  ∀ (k : Fin m) (Y : Scheme.{0}) (r : Y ⟶ (T ⊗ G).left) (z : Y) (J), Good L z J →
    sv G L N (a k) (r ≫ (h₁ ▷ G).left) z J =
      ∑ i, gT (r ≫ (fst T G).left) z (M k i) * sv G L N (b i) (r ≫ (h₂ ▷ G).left) z J

section
variable {T T' T₁ T₂ T₃ : Over Z} {m n l : ℕ} {h₁ : T ⟶ T₁} {a : Fin m → LB.Sec (LPow G L (N : ℤ) T₁)} {h₂ : T ⟶ T₂}
  {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {h₃ : T ⟶ T₃} {c : Fin l → LB.Sec (LPow G L (N : ℤ) T₃)}

/- English proof (translation)
Introduce `k Y r z J hJ`. Use `H k Y (r ≫ (g ▷ G).left) z J hJ` as an intermediate fact. Simplify using `only [Category.assoc, wh_fst] at this`. Simplify using `only [comp_whiskerRight, Over.comp_left, Matrix.map_apply, gT_comp, Category.assoc]`. Conclude with `this`.
-/
theorem Rel.pull {M} (H : Rel G L N h₁ a h₂ b M) (g : T' ⟶ T) :
    Rel G L N (g ≫ h₁) a (g ≫ h₂) b (M.map g.left.appTop.hom) := by
  intro k Y r z J hJ
  have := H k Y (r ≫ (g ▷ G).left) z J hJ
  simp only [Category.assoc, wh_fst] at this
  simp only [comp_whiskerRight, Over.comp_left, Matrix.map_apply, gT_comp, Category.assoc]
  exact this

/- English proof (translation)
Introduce `k Y r z J hJ`. Rewrite using `[H k Y r z J hJ]`. Simplify using `only [H' _ Y r z J hJ, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem Rel.trans {M P} (H : Rel G L N h₁ a h₂ b M) (H' : Rel G L N h₂ b h₃ c P) : Rel G L N h₁ a h₃ c (M * P) := by
  intro k Y r z J hJ
  rw [H k Y r z J hJ]
  simp only [H' _ Y r z J hJ, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `k Y r z J _`. Simplify using `[Matrix.one_apply, apply_ite (gT (r ≫ (fst T G).left) z)]`.
-/
theorem Rel.refl : Rel G L N h₁ a h₁ a 1 := by
  intro k Y r z J _
  simp [Matrix.one_apply, apply_ite (gT (r ≫ (fst T G).left) z)]

/- English proof (translation)
Introduce `k Y r z J hJ`. Take `⟨t, t₁, t₂⟩` from `H k`. Use `lin_all hL t₁ r z hJ` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_one, map_one, _root_.one_mul]`. Conclude with `this.symm.trans (lin_all hL t₂ r z hJ)`.
-/
theorem rel_of_lin (hL : L.IsLB) {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)}
    (H : ∀ k, ∃ t, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) t ∧ Lin G L N h₂ b (fun k' => M k k') t) :
    Rel G L N h₁ a h₂ b M := by
  intro k Y r z J hJ
  obtain ⟨t, t₁, t₂⟩ := H k
  have := lin_all hL t₁ r z hJ
  rw [Fin.sum_univ_one, map_one, _root_.one_mul] at this
  exact this.symm.trans (lin_all hL t₂ r z hJ)

/- English proof (translation)
Establish `key : ∀ (k : Fin m) (Y : Scheme.{0}) (r : Y ⟶ (T ⊗ G).left) (z : Y) (J), Good L z J → sv G L N (a k) (r ≫ (h₁ ▷ G).left) z J = sv G L N (b k) (r ≫ (h₂ ▷ G).left) z J` using `fun k Y r z J hJ => by`. Take `⟨t, t₁, t₂⟩` from `H k`. Establish `e₁` using `lin_all hL t₁ r z hJ`. Establish `e₂` using `lin_all hL t₂ r z hJ`. Rewrite `e₁`, `e₂` using `[Fin.sum_univ_one, map_one, _root_.one_mul]`.

Conclude with `e₁.symm.trans e₂`. Conclude with `⟨fun k Y r z J hJ => (key k Y r z J hJ).trans (Rel.refl k Y r z J hJ), fun k Y r z J hJ => (key k Y r z J hJ).symm.trans (Rel.refl k Y r z J hJ)⟩`.
-/
theorem rel_one_of_lin (hL : L.IsLB) {b : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)}
    (H : ∀ k, ∃ t, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) t ∧ Lin G L N h₂ (fun _ : Fin 1 => b k) (fun _ => 1) t) :
    Rel G L N h₁ a h₂ b 1 ∧ Rel G L N h₂ b h₁ a 1 := by
  have key : ∀ (k : Fin m) (Y : Scheme.{0}) (r : Y ⟶ (T ⊗ G).left) (z : Y) (J), Good L z J →
      sv G L N (a k) (r ≫ (h₁ ▷ G).left) z J = sv G L N (b k) (r ≫ (h₂ ▷ G).left) z J := fun k Y r z J hJ => by
    obtain ⟨t, t₁, t₂⟩ := H k
    have e₁ := lin_all hL t₁ r z hJ
    have e₂ := lin_all hL t₂ r z hJ
    rw [Fin.sum_univ_one, map_one, _root_.one_mul] at e₁ e₂
    exact e₁.symm.trans e₂
  exact ⟨fun k Y r z J hJ => (key k Y r z J hJ).trans (Rel.refl k Y r z J hJ),
    fun k Y r z J hJ => (key k Y r z J hJ).symm.trans (Rel.refl k Y r z J hJ)⟩

/- English proof (translation)
Use `choose s hs using fun k => exists_pull hL h₁ (a k)`. Use `choose M hM using fun k => (hb (s k)).exists`. Conclude with `⟨Matrix.of M, fun k Y r z J hJ => (hs k Y r z J hJ).symm.trans (lin_all hL (hM k) r z hJ)⟩`.
-/
theorem exists_rel (hL : L.IsLB) (hb : BasisAlong G L N h₂ b) (h₁ : T ⟶ T₁) (a : Fin m → LB.Sec (LPow G L (N : ℤ) T₁)) :
    ∃ M, Rel G L N h₁ a h₂ b M := by
  choose s hs using fun k => exists_pull hL h₁ (a k)
  choose M hM using fun k => (hb (s k)).exists
  exact ⟨Matrix.of M, fun k Y r z J hJ => (hs k Y r z J hJ).symm.trans (lin_all hL (hM k) r z hJ)⟩

/- English proof (translation)
Use `choose s hs using fun k => exists_pull hL h₁ (a k)`. Establish `key : ∀ M, Rel G L N h₁ a h₂ b M → ∀ k, Lin G L N h₂ b (M k) (s k)` using `fun M H k z J hJ => by`. Use `(hs k _ (𝟙 _) z J hJ).trans (H k _ (𝟙 _) z J hJ)` as an intermediate fact. Simplify using `only [Category.id_comp, ← gs_top] at this`. Conclude with `this`.

Use `ext1 k i`. Conclude with `congrFun ((hb (s k)).unique (key M H k) (key M' H' k)) i`.
-/
theorem Rel.unique (hL : L.IsLB) (hb : BasisAlong G L N h₂ b) {M M'} (H : Rel G L N h₁ a h₂ b M)
    (H' : Rel G L N h₁ a h₂ b M') : M = M' := by
  choose s hs using fun k => exists_pull hL h₁ (a k)
  have key : ∀ M, Rel G L N h₁ a h₂ b M → ∀ k, Lin G L N h₂ b (M k) (s k) := fun M H k z J hJ => by
    have := (hs k _ (𝟙 _) z J hJ).trans (H k _ (𝟙 _) z J hJ)
    simp only [Category.id_comp, ← gs_top] at this
    exact this
  ext1 k i
  exact congrFun ((hb (s k)).unique (key M H k) (key M' H' k)) i

end

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, charZero_of_injective_ringHom (PowerSeries.C_injective (R := F))⟩`.
-/
theorem cDvr_powerSeries (F : Type) [Field F] [CharZero F] : CDvr (PowerSeries F) :=
  ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
    charZero_of_injective_ringHom (PowerSeries.C_injective (R := F))⟩

/- English proof (translation)
Establish `e` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)`. Introduce `a a' h`. Apply `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1` to reduce the goal to its premises. Apply `hf` to reduce the goal to its premises. Establish `e₁` using `congrArg (fun q => q.hom a) e`.

Establish `e₂` using `congrArg (fun q => q.hom a') e`. Conclude with `e₁.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h).trans e₂)`.
-/
theorem appTop_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (spMap f).appTop.hom := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  intro a a' h
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
  apply hf
  have e₁ := congrArg (fun q => q.hom a) e
  have e₂ := congrArg (fun q => q.hom a') e
  exact e₁.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h).trans e₂)

/- English proof (translation)
The claim follows from `MulEquiv.isField (Field.toIsField F) (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv`.
-/
theorem isField_top (F : Type) [Field F] : IsField Γ(Sp F, ⊤) :=
  MulEquiv.isField (Field.toIsField F) (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv

/- English proof (translation)
The claim follows from `(Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toEquiv.nontrivial`.
-/
theorem nontrivial_top (A : Type) [CommRing A] [Nontrivial A] : Nontrivial Γ(Sp A, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

/- English proof (translation)
Use `ext1`. Conclude with `(cancel_mono U.ι).1 ((Over.w y).trans (Over.w y').symm)`.
-/
theorem hom_unique {T : Over Z} {U : Z.Opens} (y y' : T ⟶ Over.mk U.ι) : y = y' := by
  ext1
  exact (cancel_mono U.ι).1 ((Over.w y).trans (Over.w y').symm)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk (IsOpenImmersion.lift U.ι y (by rintro _ ⟨t, rfl⟩; simpa using h t)) (IsOpenImmersion.lift_fac _ _ _)⟩`.
-/
theorem exists_lift {Y : Scheme.{0}} (y : Y ⟶ Z) (U : Z.Opens) (h : ∀ t, y t ∈ U) : Nonempty (Over.mk y ⟶ Over.mk U.ι) :=
  ⟨Over.homMk (IsOpenImmersion.lift U.ι y (by rintro _ ⟨t, rfl⟩; simpa using h t)) (IsOpenImmersion.lift_fac _ _ _)⟩

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart hA (χ (IsLocalRing.closedPoint W))`. Conclude with `⟨i, fun t => ((IsLocalRing.specializes_closedPoint t).map χ.continuous).mem_open (A.U i).isOpen hi⟩`.
-/
theorem exists_chart_local {A : LB Z} (hA : A.IsLB) {W : Type} [CommRing W] [IsLocalRing W] (χ : Sp W ⟶ Z) :
    ∃ i, ∀ t, χ t ∈ A.U i := by
  obtain ⟨i, hi⟩ := exists_chart hA (χ (IsLocalRing.closedPoint W))
  exact ⟨i, fun t => ((IsLocalRing.specializes_closedPoint t).map χ.continuous).mem_open (A.U i).isOpen hi⟩

variable (G L N) in

def TraitBasis (U : Z.Opens) {m : ℕ} (b : Fin m → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ U.toScheme,
    Set.range (jK W ≫ χ ≫ U.ι) ⊆ abLocus G →
    BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ U.ι) ⟶ Over.mk U.ι) b

section
variable {U : Z.Opens} {m n : ℕ} {b : Fin m → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))}

/- English proof (translation)
Take `⟨χ₀, e⟩ : ∃ χ₀ : Sp W ⟶ U.toScheme, χ₀ ≫ U.ι = χ` from `⟨y.left, Over.w y⟩`. Substitute `e` using the available equality. Rewrite using `[hom_unique y (Over.homMk χ₀ rfl)]`. Conclude with `hb W hW χ₀ hr`.
-/
theorem TraitBasis.basis (hb : TraitBasis G L N U b) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W)
    {χ : Sp W ⟶ Z} (y : Over.mk χ ⟶ Over.mk U.ι) (hr : Set.range (jK W ≫ χ) ⊆ abLocus G) : BasisAlong G L N y b := by
  obtain ⟨χ₀, e⟩ : ∃ χ₀ : Sp W ⟶ U.toScheme, χ₀ ≫ U.ι = χ := ⟨y.left, Over.w y⟩
  subst e
  rw [hom_unique y (Over.homMk χ₀ rfl)]
  exact hb W hW χ₀ hr

/- English proof (translation)
Set `g : Over.mk (spMap (PowerSeries.C (R` to `F)) ≫ w) ⟶ Over.mk w := Over.homMk (spMap (PowerSeries.C (R := F))) rfl`. Establish `hB` using `hb.basis (cDvr_powerSeries F) (g ≫ y) (by rintro _ ⟨t, rfl⟩; exact hw ⟨_, rfl⟩)`. Establish `e` using `(H.pull g).unique hL hB (H'.pull g)`. Use `ext1 k i`. Conclude with `appTop_injective _ (PowerSeries.C_injective (R := F)) (congrFun (congrFun e k) i)`.
-/
theorem TraitBasis.unique (hL : L.IsLB) (hb : TraitBasis G L N U b) {F : Type} [Field F] [CharZero F] {w : Sp F ⟶ Z}
    (hw : Set.range w ⊆ abLocus G) {y : Over.mk w ⟶ Over.mk U.ι} {T₁ : Over Z} {h₁ : Over.mk w ⟶ T₁}
    {a : Fin n → LB.Sec (LPow G L (N : ℤ) T₁)} {M M'} (H : Rel G L N h₁ a y b M) (H' : Rel G L N h₁ a y b M') :
    M = M' := by
  let g : Over.mk (spMap (PowerSeries.C (R := F)) ≫ w) ⟶ Over.mk w := Over.homMk (spMap (PowerSeries.C (R := F))) rfl
  have hB := hb.basis (cDvr_powerSeries F) (g ≫ y) (by rintro _ ⟨t, rfl⟩; exact hw ⟨_, rfl⟩)
  have e := (H.pull g).unique hL hB (H'.pull g)
  ext1 k i
  exact appTop_injective _ (PowerSeries.C_injective (R := F)) (congrFun (congrFun e k) i)

variable {R : Type} [CommRing R] [IsDomain R] {x : Sp (FractionRing R) ⟶ Z}
  {f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))}

/- English proof (translation)
Take `⟨b', hb', hbb⟩` from `hf W hW φ gam hg χ h`. Establish `hr : Set.range (jK W ≫ χ) ⊆ abLocus G` using `by rw [← h]; rintro _ ⟨t, rfl⟩; exact hx ⟨_, rfl⟩`. Establish `hU` using `hb.basis hW χU hr`. Take `⟨M', hM'⟩` from `exists_rel hL hb' χU b`. Take `⟨P', hP'⟩` from `exists_rel hL hU (𝟙 _) b'`.

Establish `e₁ : M' * P' = 1` using `(hM'.trans hP').unique hL hU Rel.refl`. Establish `e₂ : P' * M' = 1` using `(hP'.trans hM').unique hL hb' Rel.refl`. Use `⟨M', P', e₁, e₂, ?_⟩` and prove the remaining obligations. Use `haveI : CharZero W := hW.2.2`. Establish `r₁` using `hM.pull (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x)`.

Establish `r₂` using `(rel_one_of_lin hL hbb).1`. Establish `r₃` using `hP'.pull (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ)`. Rewrite `r₁`, `r₃` using `[Category.comp_id]`. Establish `r₄` using `(r₁.trans r₂).trans r₃`. Rewrite `r₄` using `[hom_unique (_ ≫ xU) ((Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) ≫ χU), Matrix.mul_one]`.

Establish `e₃ : Matrix.map M (spMap gam).appTop.hom * P'.map (jK W).appTop.hom = 1` using `hb.unique hL hr r₄ Rel.refl`. Establish `e₄ : P'.map (jK W).appTop.hom * M'.map (jK W).appTop.hom = 1`. Rewrite using `[← Matrix.map_mul, e₂, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `(Matrix.mul_one _).symm.trans ((congrArg _ e₄.symm).trans ((Matrix.mul_assoc _ _ _).symm.trans ((congrArg (· * M'.map (jK W).appTop.hom) e₃).trans (Matrix.one_mul _))))`.
-/
theorem trait_matrix (hL : L.IsLB) (hb : TraitBasis G L N U b) (hx : Set.range x ⊆ abLocus G) (hf : IsFrame G L N x f)
    {xU : Over.mk x ⟶ Over.mk U.ι} {M} (hM : Rel G L N xU b (𝟙 _) f M)
    {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hg : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r))
    {χ : Sp W ⟶ Z} (h : spMap gam ≫ x = jK W ≫ χ) (χU : Over.mk χ ⟶ Over.mk U.ι) :
    ∃ (M' : Matrix (Fin m) (Fin n) Γ(Sp W, ⊤)) (P' : Matrix (Fin n) (Fin m) Γ(Sp W, ⊤)), M' * P' = 1 ∧ P' * M' = 1 ∧
      Matrix.map M (spMap gam).appTop.hom = M'.map (jK W).appTop.hom := by
  obtain ⟨b', hb', hbb⟩ := hf W hW φ gam hg χ h
  have hr : Set.range (jK W ≫ χ) ⊆ abLocus G := by rw [← h]; rintro _ ⟨t, rfl⟩; exact hx ⟨_, rfl⟩
  have hU := hb.basis hW χU hr
  obtain ⟨M', hM'⟩ := exists_rel hL hb' χU b
  obtain ⟨P', hP'⟩ := exists_rel hL hU (𝟙 _) b'
  have e₁ : M' * P' = 1 := (hM'.trans hP').unique hL hU Rel.refl
  have e₂ : P' * M' = 1 := (hP'.trans hM').unique hL hb' Rel.refl
  refine ⟨M', P', e₁, e₂, ?_⟩
  haveI : CharZero W := hW.2.2
  have r₁ := hM.pull (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x)
  have r₂ := (rel_one_of_lin hL hbb).1
  have r₃ := hP'.pull (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ)
  rw [Category.comp_id] at r₁ r₃
  have r₄ := (r₁.trans r₂).trans r₃
  rw [hom_unique (_ ≫ xU) ((Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) ≫ χU), Matrix.mul_one] at r₄
  have e₃ : Matrix.map M (spMap gam).appTop.hom * P'.map (jK W).appTop.hom = 1 := hb.unique hL hr r₄ Rel.refl
  have e₄ : P'.map (jK W).appTop.hom * M'.map (jK W).appTop.hom = 1 := by
    rw [← Matrix.map_mul, e₂, Matrix.map_one _ (map_zero _) (map_one _)]
  exact (Matrix.mul_one _).symm.trans ((congrArg _ e₄.symm).trans ((Matrix.mul_assoc _ _ _).symm.trans
    ((congrArg (· * M'.map (jK W).appTop.hom) e₃).trans (Matrix.one_mul _))))

/- English proof (translation)
Set `K` to `FractionRing R`. Set `W` to `PowerSeries K`. Take `⟨M', P', H⟩` from `trait_matrix hL hb hx hf hM (cDvr_powerSeries K) ((PowerSeries.C (R := K)).comp (algebraMap R K)) ((algebraMap W (FractionRing W)).comp (PowerSeries.C (R := K))) (fun _ => rfl) (χ := spMap (PowerSeries.C (R := K)) ≫ x) (by rw [spMap_comp, Category.assoc]) ((Over.homMk (spMap (Pow …`. Conclude with `⟨_, _, inferInstance, inferInstance, nontrivial_top W, nontrivial_top (FractionRing W), _, _, M', P', H⟩`.
-/
theorem const_matrix [CharZero R] (hL : L.IsLB) (hb : TraitBasis G L N U b) (hx : Set.range x ⊆ abLocus G)
    (hf : IsFrame G L N x f) {xU : Over.mk x ⟶ Over.mk U.ι} {M} (hM : Rel G L N xU b (𝟙 _) f M) :
    ∃ (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Nontrivial A) (_ : Nontrivial B) (p : Γ(Sp (FractionRing R), ⊤) →+* B)
      (q : A →+* B) (M' : Matrix (Fin m) (Fin n) A) (P' : Matrix (Fin n) (Fin m) A), M' * P' = 1 ∧ P' * M' = 1 ∧
      Matrix.map M p = M'.map q := by
  let K := FractionRing R
  let W := PowerSeries K
  obtain ⟨M', P', H⟩ := trait_matrix hL hb hx hf hM (cDvr_powerSeries K) ((PowerSeries.C (R := K)).comp (algebraMap R K))
    ((algebraMap W (FractionRing W)).comp (PowerSeries.C (R := K))) (fun _ => rfl)
    (χ := spMap (PowerSeries.C (R := K)) ≫ x) (by rw [spMap_comp, Category.assoc])
    ((Over.homMk (spMap (PowerSeries.C (R := K))) rfl : Over.mk (spMap (PowerSeries.C (R := K)) ≫ x) ⟶ Over.mk x) ≫ xU)
  exact ⟨_, _, inferInstance, inferInstance, nontrivial_top W, nontrivial_top (FractionRing W), _, _, M', P', H⟩

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_rel hL hf' xU b`. Take `⟨A, B, _, _, _, _, p, q, M', P', e₁, e₂, -⟩` from `const_matrix hL hb hx hf hM`. Simplify using `using Matrix.square_of_invertible P' M' e₂ e₁`.
-/
theorem card_eq [CharZero R] (hL : L.IsLB) (hb : TraitBasis G L N U b) (hx : Set.range x ⊆ abLocus G)
    (hf : IsFrame G L N x f) (hf' : BasisAlong G L N (𝟙 _) f) (xU : Over.mk x ⟶ Over.mk U.ι) : n = m := by
  obtain ⟨M, hM⟩ := exists_rel hL hf' xU b
  obtain ⟨A, B, _, _, _, _, p, q, M', P', e₁, e₂, -⟩ := const_matrix hL hb hx hf hM
  simpa using Matrix.square_of_invertible P' M' e₂ e₁

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_rel hL hf' xU b`. Take `⟨A, B, _, _, _, _, p, q, M', P', e₁, -, e⟩` from `const_matrix hL hb hx hf hM`. Establish `u : IsUnit (p (Matrix.det M))`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(Matrix.isUnit_det_of_right_inverse e₁).map q`.

Establish `hne : Matrix.det (R` using `Γ(Sp (FractionRing R), ⊤)) M ≠ 0 := fun h0 => by`. Rewrite `u` using `[h0, map_zero]`. Conclude with `not_isUnit_zero u`. Take `⟨v, hv⟩` from `(isField_top (FractionRing R)).mul_inv_cancel hne`. Take `⟨M₀, rfl⟩` from `(Matrix.isUnit_iff_isUnit_det M).2 (IsUnit.of_mul_eq_one v hv)`.

Conclude with `⟨M₀, hM⟩`.
-/
theorem exists_gl [CharZero R] (hL : L.IsLB) {b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))}
    (hb : TraitBasis G L N U b) (hx : Set.range x ⊆ abLocus G)
    (hf : IsFrame G L N x f) (hf' : BasisAlong G L N (𝟙 _) f) (xU : Over.mk x ⟶ Over.mk U.ι) :
    ∃ M : GL (Fin n) Γ(Sp (FractionRing R), ⊤), Rel G L N xU b (𝟙 _) f M.val := by
  obtain ⟨M, hM⟩ := exists_rel hL hf' xU b
  obtain ⟨A, B, _, _, _, _, p, q, M', P', e₁, -, e⟩ := const_matrix hL hb hx hf hM
  have u : IsUnit (p (Matrix.det M)) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_det_of_right_inverse e₁).map q
  have hne : Matrix.det (R := Γ(Sp (FractionRing R), ⊤)) M ≠ 0 := fun h0 => by
    rw [h0, map_zero] at u; exact not_isUnit_zero u
  obtain ⟨v, hv⟩ := (isField_top (FractionRing R)).mul_inv_cancel hne
  obtain ⟨M₀, rfl⟩ := (Matrix.isUnit_iff_isUnit_det M).2 (IsUnit.of_mul_eq_one v hv)
  exact ⟨M₀, hM⟩

/- English proof (translation)
Take `⟨M', P', e₁, -, e⟩` from `trait_matrix hL hb hx hf hM hW φ gam hg h χU`. Use `⟨(Matrix.isUnit_det_of_right_inverse e₁).unit, fun z => Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← gs_unit _ z ⊤ trivial, ← gs_unit _ z ⊤ trivial, gs_top, gs_top, IsUnit.unit_spec]`. Establish `e'` using `congrArg Matrix.det e`. Rewrite `e'` using `[← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det]`.

Conclude with `congrArg (gT (𝟙 _) z) e'`.
-/
theorem trait_det (hL : L.IsLB) {b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))}
    (hb : TraitBasis G L N U b) (hx : Set.range x ⊆ abLocus G) (hf : IsFrame G L N x f)
    {xU : Over.mk x ⟶ Over.mk U.ι} {M : GL (Fin n) Γ(Sp (FractionRing R), ⊤)} (hM : Rel G L N xU b (𝟙 _) f M.val)
    {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hg : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r))
    {χ : Sp W ⟶ Z} (h : spMap gam ≫ x = jK W ≫ χ) (χU : Over.mk χ ⟶ Over.mk U.ι) :
    ∃ u : Γ(Sp W, ⊤)ˣ, ∀ z, gm (spMap gam) z ⊤ (Matrix.GeneralLinearGroup.det M) = gm (jK W) z ⊤ u := by
  obtain ⟨M', P', e₁, -, e⟩ := trait_matrix hL hb hx hf hM hW φ gam hg h χU
  refine ⟨(Matrix.isUnit_det_of_right_inverse e₁).unit, fun z => Units.ext ?_⟩
  rw [← gs_unit _ z ⊤ trivial, ← gs_unit _ z ⊤ trivial, gs_top, gs_top, IsUnit.unit_spec]
  have e' := congrArg Matrix.det e
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at e'
  exact congrArg (gT (𝟙 _) z) e'

end

/- English proof (translation)
Establish `le : ∀ j : PUnit → A.ι, LB.wchart A (fun _ : PUnit => y) j ≤ y ⁻¹ᵁ (A.U (j PUnit.unit) ⊓ A.U i)` using `fun j t ht => ⟨Set.mem_iInter.1 ht PUnit.unit, hy t⟩`. Establish `v : ∀ (j : PUnit → A.ι) (Y' : Scheme.{0}) (r : Y' ⟶ Y) (z : Y'), r z ∈ LB.wchart A (fun _ : PUnit => y) j → gm r z _ (res (le j) (pullU y _ (A.g (j PUnit.unit) i)) * res le_top u) = gm (r ≫ y) z _ (A.g (j PUnit.unit) i) * gm r z ⊤ u` using `fun j Y' r z hz => by`. Rewrite using `[map_mul, gm_res r z _ hz, gm_res r z _ hz, gm_pull r y z (A.U (j PUnit.unit) ⊓ A.U i) (le j hz)]`. Use `⟨⟨fun j => res (le j) (pullU y _ (A.g (j PUnit.unit) i)) * res le_top u⟩, fun j j' => unit_ext fun t ht => ?_, fun Y' r z J hJ => v _ Y' r z (hJ.mem (fun _ : PUnit => y) r)⟩` and prove the remaining obligations. Use `((gm_res (𝟙 _) t _ ht _).trans (v j _ _ t ht.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb A _ _ (𝟙 _) t j j' ht.1 ht.2) ((gm_res (𝟙 _) t _ ht _).trans (v j' _ _ t ht.2)))).symm)` and prove the remaining obligations.

Rewrite using `[Fintype.prod_unique, zpow_one, ← _root_.mul_assoc, gm_cocycle hA (𝟙 _ ≫ y) t (i := j PUnit.unit) (j := j' PUnit.unit) (Set.mem_iInter.1 ht.1 PUnit.unit) (Set.mem_iInter.1 ht.2 PUnit.unit) (hy t)]`.
-/
theorem exists_gen_chart {A : LB Z} (hA : A.IsLB) {Y : Scheme.{0}} (y : Y ⟶ Z) (i : A.ι) (hy : ∀ t, y t ∈ A.U i)
    (u : Γ(Y, ⊤)ˣ) : ∃ e : LB.Gen (A.pull y), e.IsGen ∧ ∀ (Y' : Scheme.{0}) (r : Y' ⟶ Y) (z : Y') (J), Good A z J →
      val (L := A) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e r z J =
        gm (r ≫ y) z _ (A.g (J (r ≫ y)) i) * gm r z ⊤ u := by
  have le : ∀ j : PUnit → A.ι, LB.wchart A (fun _ : PUnit => y) j ≤ y ⁻¹ᵁ (A.U (j PUnit.unit) ⊓ A.U i) :=
    fun j t ht => ⟨Set.mem_iInter.1 ht PUnit.unit, hy t⟩
  have v : ∀ (j : PUnit → A.ι) (Y' : Scheme.{0}) (r : Y' ⟶ Y) (z : Y'), r z ∈ LB.wchart A (fun _ : PUnit => y) j →
      gm r z _ (res (le j) (pullU y _ (A.g (j PUnit.unit) i)) * res le_top u) =
        gm (r ≫ y) z _ (A.g (j PUnit.unit) i) * gm r z ⊤ u := fun j Y' r z hz => by
    rw [map_mul, gm_res r z _ hz, gm_res r z _ hz, gm_pull r y z (A.U (j PUnit.unit) ⊓ A.U i) (le j hz)]
  refine ⟨⟨fun j => res (le j) (pullU y _ (A.g (j PUnit.unit) i)) * res le_top u⟩, fun j j' => unit_ext fun t ht => ?_,
    fun Y' r z J hJ => v _ Y' r z (hJ.mem (fun _ : PUnit => y) r)⟩
  refine ((gm_res (𝟙 _) t _ ht _).trans (v j _ _ t ht.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb A _ _ (𝟙 _) t j j' ht.1 ht.2) ((gm_res (𝟙 _) t _ ht _).trans (v j' _ _ t ht.2)))).symm)
  rw [Fintype.prod_unique, zpow_one, ← _root_.mul_assoc, gm_cocycle hA (𝟙 _ ≫ y) t (i := j PUnit.unit) (j := j' PUnit.unit)
    (Set.mem_iInter.1 ht.1 PUnit.unit) (Set.mem_iInter.1 ht.2 PUnit.unit) (hy t)]

/- English proof (translation)
Substitute `e` using the available equality. Apply `Units.ext` to reduce the goal to its premises. Establish `hm : ∀ t : V.toScheme, V.ι t ∈ V` using `fun t => t.2`. Establish `e : V.topIso.inv = V.ι.appLE V ⊤ (fun t _ => hm t)` using `(Scheme.Opens.ι_appLE V V ⊤ (fun t _ => hm t)).symm`. Rewrite using `[← gs_unit _ z _ (hm _), ← Category.assoc, ← gs_pull _ V.ι z _ (hm _), ← gs_unit _ z ⊤ trivial, ← hc, e]`.

Conclude with `(gs_res (r ≫ y) z (show ⊤ ≤ V.ι ⁻¹ᵁ V from fun t _ => hm t) trivial _).symm`.
-/
theorem gm_lift {Y Y' : Scheme.{0}} {x : Y ⟶ Z} {V : Z.Opens} (y : Y ⟶ V.toScheme) (e : y ≫ V.ι = x) (r : Y' ⟶ Y) (z : Y')
    (a : Γ(Z, V)ˣ) (c : Γ(V.toScheme, ⊤)ˣ) (hc : V.topIso.inv.hom a.val = c.val) :
    gm (r ≫ x) z V a = gm (r ≫ y) z ⊤ c := by
  subst e
  apply Units.ext
  have hm : ∀ t : V.toScheme, V.ι t ∈ V := fun t => t.2
  have e : V.topIso.inv = V.ι.appLE V ⊤ (fun t _ => hm t) := (Scheme.Opens.ι_appLE V V ⊤ (fun t _ => hm t)).symm
  rw [← gs_unit _ z _ (hm _), ← Category.assoc, ← gs_pull _ V.ι z _ (hm _), ← gs_unit _ z ⊤ trivial, ← hc, e]
  exact (gs_res (r ≫ y) z (show ⊤ ≤ V.ι ⁻¹ᵁ V from fun t _ => hm t) trivial _).symm

/- English proof (translation)
Establish `r₁` using `hP.pull (Over.homMk y e : Over.mk x ⟶ Over.mk v)`. Rewrite `r₁` using `[hom_unique (_ ≫ h) xU, hom_unique (_ ≫ h') xU']`. Establish `e₁ : M.val = P.map y.appTop.hom * M'.val` using `hM.unique hL hf (r₁.trans hM')`. Establish `e₂ : M.val.det = y.appTop.hom c.val * M'.val.det`. Rewrite using `[e₁, hc, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, ← gs_unit _ z ⊤ trivial, ← gs_unit _ z ⊤ trivial, ← gs_unit _ z ⊤ trivial, gs_top, gs_top, gs_top, ← gT_comp, ← map_mul]`. Conclude with `congrArg (gT r z) e₂`.
-/
theorem det_trans (hL : L.IsLB) {U U' : Z.Opens} {Y V : Scheme.{0}} {x : Y ⟶ Z} {v : V ⟶ Z} {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))} {b' : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U'.ι))}
    {f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))} (hf : BasisAlong G L N (𝟙 _) f)
    {h : Over.mk v ⟶ Over.mk U.ι} {h' : Over.mk v ⟶ Over.mk U'.ι} {P : Matrix (Fin n) (Fin n) Γ(V, ⊤)}
    (hP : Rel G L N h b h' b' P) (c : Γ(V, ⊤)ˣ) (hc : c.val = P.det) (y : Y ⟶ V) (e : y ≫ v = x)
    {xU : Over.mk x ⟶ Over.mk U.ι} {xU' : Over.mk x ⟶ Over.mk U'.ι} {M M' : GL (Fin n) Γ(Y, ⊤)}
    (hM : Rel G L N xU b (𝟙 _) f M.val) (hM' : Rel G L N xU' b' (𝟙 _) f M'.val) {Y' : Scheme.{0}} (r : Y' ⟶ Y) (z : Y') :
    gm r z ⊤ (Matrix.GeneralLinearGroup.det M) = gm (r ≫ y) z ⊤ c * gm r z ⊤ (Matrix.GeneralLinearGroup.det M') := by
  have r₁ := hP.pull (Over.homMk y e : Over.mk x ⟶ Over.mk v)
  rw [hom_unique (_ ≫ h) xU, hom_unique (_ ≫ h') xU'] at r₁
  have e₁ : M.val = P.map y.appTop.hom * M'.val := hM.unique hL hf (r₁.trans hM')
  have e₂ : M.val.det = y.appTop.hom c.val * M'.val.det := by
    rw [e₁, hc, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
  apply Units.ext
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial, ← gs_unit _ z ⊤ trivial, ← gs_unit _ z ⊤ trivial, gs_top, gs_top, gs_top,
    ← gT_comp, ← map_mul]
  exact congrArg (gT r z) e₂

/- English proof (translation)
Take `⟨c, P, hc, hP, e⟩` from `Am.trans i j`. Take `⟨y⟩` from `exists_lift x (Am.A.U i ⊓ Am.A.U j) (fun t => ⟨hi t, hj t⟩)`. Take `⟨y₀, e₀⟩ : ∃ y₀ : Y ⟶ (Am.A.U i ⊓ Am.A.U j).toScheme, y₀ ≫ (Am.A.U i ⊓ Am.A.U j).ι = x` from `⟨y.left, Over.w y⟩`. Establish `d₁` using `det_trans hL hθ (P := Matrix.of fun _ _ => c.val) (rel_of_lin hL (fun _ => hc)) c (Matrix.det_unique (Matrix.of fun _ _ : Fin 1 => c.val)).symm y₀ e₀ hC hC' r z`. Establish `d₂` using `det_trans hL hf (P := P.val) (rel_of_lin hL hP) (Matrix.GeneralLinearGroup.det P) rfl y₀ e₀ hM hM' r z`.

Rewrite using `[gm_lift y₀ e₀ r z _ _ e]`. Simplify using `only [map_mul, map_zpow]`. Rewrite using `[d₁, d₂, mul_zpow, mul_zpow, _root_.mul_mul_mul_comm]`.
-/
theorem unit_trans (hL : L.IsLB) (Am : AmpFrames G L N) {Y : Scheme.{0}} {x : Y ⟶ Z}
    {θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))} {f : Fin Am.n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))}
    (hθ : BasisAlong G L 1 (𝟙 _) (fun _ : Fin 1 => θ)) (hf : BasisAlong G L N (𝟙 _) f) {i j : Am.A.ι}
    (hi : ∀ t, x t ∈ Am.A.U i) (hj : ∀ t, x t ∈ Am.A.U j)
    {xi : Over.mk x ⟶ Over.mk (Am.A.U i).ι} {xj : Over.mk x ⟶ Over.mk (Am.A.U j).ι}
    {C C' : GL (Fin 1) Γ(Y, ⊤)} {M M' : GL (Fin Am.n) Γ(Y, ⊤)}
    (hC : Rel G L 1 xi (fun _ : Fin 1 => Am.th i) (𝟙 _) (fun _ : Fin 1 => θ) C.val)
    (hC' : Rel G L 1 xj (fun _ : Fin 1 => Am.th j) (𝟙 _) (fun _ : Fin 1 => θ) C'.val)
    (hM : Rel G L N xi (Am.b i) (𝟙 _) f M.val) (hM' : Rel G L N xj (Am.b j) (𝟙 _) f M'.val)
    {Y' : Scheme.{0}} (r : Y' ⟶ Y) (z : Y') :
    gm r z ⊤ (Matrix.GeneralLinearGroup.det C ^ Am.r * Matrix.GeneralLinearGroup.det M ^ Am.s) =
      gm (r ≫ x) z _ (Am.A.g i j) *
        gm r z ⊤ (Matrix.GeneralLinearGroup.det C' ^ Am.r * Matrix.GeneralLinearGroup.det M' ^ Am.s) := by
  obtain ⟨c, P, hc, hP, e⟩ := Am.trans i j
  obtain ⟨y⟩ := exists_lift x (Am.A.U i ⊓ Am.A.U j) (fun t => ⟨hi t, hj t⟩)
  obtain ⟨y₀, e₀⟩ : ∃ y₀ : Y ⟶ (Am.A.U i ⊓ Am.A.U j).toScheme, y₀ ≫ (Am.A.U i ⊓ Am.A.U j).ι = x := ⟨y.left, Over.w y⟩
  have d₁ := det_trans hL hθ (P := Matrix.of fun _ _ => c.val) (rel_of_lin hL (fun _ => hc)) c
    (Matrix.det_unique (Matrix.of fun _ _ : Fin 1 => c.val)).symm y₀ e₀ hC hC' r z
  have d₂ := det_trans hL hf (P := P.val) (rel_of_lin hL hP) (Matrix.GeneralLinearGroup.det P) rfl y₀ e₀ hM hM' r z
  rw [gm_lift y₀ e₀ r z _ _ e]
  simp only [map_mul, map_zpow]
  rw [d₁, d₂, mul_zpow, mul_zpow, _root_.mul_mul_mul_comm]

/- English proof (translation)
Introduce `Z G _ L hL N Am AA hA R _ _ x hx θ n f hθ hf bθ bf hR`. Substitute `hA` using the available equality. Establish `tθ : ∀ i, TraitBasis G L 1 (Am.A.U i) (fun _ : Fin 1 => Am.th i)` using `fun i W _ _ _ hW χ h => (Am.trait i W hW χ h).1`. Establish `tb : ∀ i, TraitBasis G L N (Am.A.U i) (Am.b i)` using `fun i W _ _ _ hW χ h => (Am.trait i W hW χ h).2`. Take `⟨i, hi⟩` from `exists_chart_local Am.isLB x`.

Take `⟨xi⟩` from `exists_lift x _ hi`. Take `rfl : n = Am.n` from `card_eq hL (tb i) hx hf bf xi`. Take `⟨C, hC⟩` from `exists_gl hL (tθ i) hx hθ bθ xi`. Take `⟨M, hM⟩` from `exists_gl hL (tb i) hx hf bf xi`. Take `⟨e, he, ve⟩` from `exists_gen_chart Am.isLB x i hi (Matrix.GeneralLinearGroup.det C ^ Am.r * Matrix.GeneralLinearGroup.det M ^ Am.s)`.

Use `⟨e, he, fun W _ _ _ hW φ gam hg χ h => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart_local Am.isLB χ`. Take `⟨χj⟩` from `exists_lift χ _ hj`. Establish `hxj : ∀ t, x t ∈ Am.A.U j` using `fun t => by`. Set `s : Sp (FractionRing W)` to `IsLocalRing.closedPoint _`.

Establish `e₁ : t = spMap gam s` using `Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _`. Establish `e₂ : (spMap gam ≫ x) s ∈ Am.A.U j` using `by rw [h]; exact hj _`. Rewrite using `[e₁]`. Conclude with `e₂`. Take `⟨xj⟩` from `exists_lift x _ hxj`.

Take `⟨C', hC'⟩` from `exists_gl hL (tθ j) hx hθ bθ xj`. Take `⟨M', hM'⟩` from `exists_gl hL (tb j) hx hf bf xj`. Take `⟨u, hu⟩` from `trait_det hL (tθ j) hx hθ hC' hW φ gam hg h χj`. Take `⟨w, hw⟩` from `trait_det hL (tb j) hx hf hM' hW φ gam hg h χj`. Take `⟨e', he', ve'⟩` from `exists_gen_chart Am.isLB χ j hj (u ^ Am.r * w ^ Am.s)`.

Use `⟨e', he', fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[ve _ _ z J hJ, ve' _ _ z J hJ, unit_trans hL Am bθ bf hi hxj hC hC' hM hM', ← _root_.mul_assoc, gm_cocycle Am.isLB (spMap gam ≫ x) z (hJ _) (hi _) (hxj _), h]`. Simplify using `only [map_mul, map_zpow, hu, hw]`.
-/
theorem exists_gen_of_frames : ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (N : ℕ) (Am : AmpFrames G L N) (AA : LB Z), ∀ hA : AA = Am.A, ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z), Set.range x ⊆ abLocus G → ∀ (θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) (n : ℕ) (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))), IsFrame G L 1 x (fun _ : Fin 1 => θ) → IsFrame G L N x f → BasisAlong G L 1 (𝟙 _) (fun _ : Fin 1 => θ) → BasisAlong G L N (𝟙 _) f → CharZero R → ∃ e : LB.Gen (AA.pull x), e.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Z, spMap gam ≫ x = jK W ≫ χ → ∃ e' : LB.Gen (AA.pull χ), e'.IsGen ∧ ∀ z J, Good AA z J → val (L := AA) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J = val (L := AA) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (jK W) z J := by
  intro Z G _ L hL N Am AA hA R _ _ x hx θ n f hθ hf bθ bf hR
  subst hA
  have tθ : ∀ i, TraitBasis G L 1 (Am.A.U i) (fun _ : Fin 1 => Am.th i) := fun i W _ _ _ hW χ h => (Am.trait i W hW χ h).1
  have tb : ∀ i, TraitBasis G L N (Am.A.U i) (Am.b i) := fun i W _ _ _ hW χ h => (Am.trait i W hW χ h).2
  obtain ⟨i, hi⟩ := exists_chart_local Am.isLB x
  obtain ⟨xi⟩ := exists_lift x _ hi
  obtain rfl : n = Am.n := card_eq hL (tb i) hx hf bf xi
  obtain ⟨C, hC⟩ := exists_gl hL (tθ i) hx hθ bθ xi
  obtain ⟨M, hM⟩ := exists_gl hL (tb i) hx hf bf xi
  obtain ⟨e, he, ve⟩ := exists_gen_chart Am.isLB x i hi
    (Matrix.GeneralLinearGroup.det C ^ Am.r * Matrix.GeneralLinearGroup.det M ^ Am.s)
  refine ⟨e, he, fun W _ _ _ hW φ gam hg χ h => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart_local Am.isLB χ
  obtain ⟨χj⟩ := exists_lift χ _ hj
  have hxj : ∀ t, x t ∈ Am.A.U j := fun t => by
    let s : Sp (FractionRing W) := IsLocalRing.closedPoint _
    have e₁ : t = spMap gam s := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    have e₂ : (spMap gam ≫ x) s ∈ Am.A.U j := by rw [h]; exact hj _
    rw [e₁]; exact e₂
  obtain ⟨xj⟩ := exists_lift x _ hxj
  obtain ⟨C', hC'⟩ := exists_gl hL (tθ j) hx hθ bθ xj
  obtain ⟨M', hM'⟩ := exists_gl hL (tb j) hx hf bf xj
  obtain ⟨u, hu⟩ := trait_det hL (tθ j) hx hθ hC' hW φ gam hg h χj
  obtain ⟨w, hw⟩ := trait_det hL (tb j) hx hf hM' hW φ gam hg h χj
  obtain ⟨e', he', ve'⟩ := exists_gen_chart Am.isLB χ j hj (u ^ Am.r * w ^ Am.s)
  refine ⟨e', he', fun z J hJ => ?_⟩
  rw [ve _ _ z J hJ, ve' _ _ z J hJ, unit_trans hL Am bθ bf hi hxj hC hC' hM hM', ← _root_.mul_assoc,
    gm_cocycle Am.isLB (spMap gam ≫ x) z (hJ _) (hi _) (hxj _), h]
  simp only [map_mul, map_zpow, hu, hw]

end GlobalTheory.FrameGen
end
