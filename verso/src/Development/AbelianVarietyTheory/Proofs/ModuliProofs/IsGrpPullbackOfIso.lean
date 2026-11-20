import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ThetaToObj

section Comb
variable {Q L : Type} [AddCommGroup L] {n : ℕ}

/- English proof (translation)
Use `hf 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`.
-/
theorem add_zero' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have := hf 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [zero_smul, pow_zero, add_zero' hf]`. Consider the case `succ m ih => rw [succ_nsmul, hf, ih, pow_succ]`.
-/
theorem add_nsmul' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) (m : ℕ) (x : L) :
    f (m • x) = f x ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, add_zero' hf]
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

/- English proof (translation)
Set `F : L →+ Additive Q` to `AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) fun x y => by rw [hf]; rfl`. Set `F' : L →+ Additive Q` to `AddMonoidHom.mk' (fun x => Additive.ofMul (f' x)) fun x y => by rw [hf']; rfl`. Establish `: F.toIntLinearMap ∘ₗ bas.toLinearMap = F'.toIntLinearMap ∘ₗ bas.toLinearMap`. Use `(Pi.basisFun ℤ (Fin n)).ext fun i => ?_` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply]`.

Conclude with `congrArg Additive.ofMul (h i)`. Establish `e` using `LinearMap.congr_fun this (bas.symm x)`. Simplify `e` using `[F, F']`.
-/
theorem ext_basis [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) {f f' : L → Q} (hf : ∀ x y, f (x + y) = f x * f y)
    (hf' : ∀ x y, f' (x + y) = f' x * f' y) (h : ∀ i, f (bas (Pi.single i 1)) = f' (bas (Pi.single i 1))) (x : L) :
    f x = f' x := by
  let F : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) fun x y => by rw [hf]; rfl
  let F' : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f' x)) fun x y => by rw [hf']; rfl
  have : F.toIntLinearMap ∘ₗ bas.toLinearMap = F'.toIntLinearMap ∘ₗ bas.toLinearMap := by
    refine (Pi.basisFun ℤ (Fin n)).ext fun i => ?_
    rw [Pi.basisFun_apply]
    exact congrArg Additive.ofMul (h i)
  have e := LinearMap.congr_fun this (bas.symm x)
  simpa [F, F'] using e

/- English proof (translation)
Establish `hf : ∀ x y : L, ∏ i, p i ^ bas.symm (x + y) i = (∏ i, p i ^ bas.symm x i) * ∏ i, p i ^ bas.symm y i`. Introduce `x y`. Simplify using `only [map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]`. Use `⟨fun x => ∏ i, p i ^ bas.symm x i, hf, fun x => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_nsmul, Pi.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, hp, one_zpow]`. Use `beta_reduce`. Rewrite using `[LinearEquiv.symm_apply_apply, Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules.
-/
theorem exists_comb [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) (p : Fin n → Q) (k : ℕ) (hp : ∀ i, p i ^ k = 1) :
    ∃ f : L → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ x, f (k • x) = 1) ∧ ∀ i, f (bas (Pi.single i 1)) = p i := by
  have hf : ∀ x y : L, ∏ i, p i ^ bas.symm (x + y) i = (∏ i, p i ^ bas.symm x i) * ∏ i, p i ^ bas.symm y i := by
    intro x y
    simp only [map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  refine ⟨fun x => ∏ i, p i ^ bas.symm x i, hf, fun x => ?_, fun i => ?_⟩
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, hp, one_zpow]
  · beta_reduce
    rw [LinearEquiv.symm_apply_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp

end Comb

/- English proof (translation)
Establish `h1 : u • x ∈ (I * J) • (⊤ : Submodule O L)`. Rewrite using `[Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul hu hx`. Rewrite `h1` using `[h, Submodule.ideal_span_singleton_smul]`. Take `⟨y, -, hy⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1`.

Conclude with `⟨y, by rw [← hy, Nat.cast_smul_eq_nsmul]⟩`.
-/
theorem smul_mem_of_mul {O L : Type} [CommRing O] [AddCommGroup L] [Module O L] {I J : Ideal O} {M : ℕ}
    (h : I * J = Ideal.span {(M : O)}) {u : O} (hu : u ∈ I) {x : L} (hx : x ∈ J • (⊤ : Submodule O L)) :
    ∃ y : L, u • x = M • y := by
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule O L) := by
    rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu hx
  rw [h, Submodule.ideal_span_singleton_smul] at h1
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  exact ⟨y, by rw [← hy, Nat.cast_smul_eq_nsmul]⟩

/- English proof (translation)
Establish `: IsIso φ.hom.left` using `inferInstanceAs (IsIso ((Over.forget S).map φ.hom))`. Use `⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Set `j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T` to `Over.homMk (𝟙 T.left) (by simp)`. Establish `e₁ : x₀ = j ≫ x ≫ φ.hom` using `Over.OverMorphism.ext (by simp [hx, j])`. Establish `e₂ : y₀ = j ≫ y ≫ φ.hom` using `Over.OverMorphism.ext (by simp [hy, j])`.

Rewrite using `[e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]`. Simplify using `[j]`.
-/
theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (φ : G' ≅ G) [IsMonHom φ.hom] :
    IsGrpPullback G' G (𝟙 S) φ.hom.left := by
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget S).map φ.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x ≫ φ.hom := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y ≫ φ.hom := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [j]

/- English proof (translation)
Introduce `_ _ E _ _ _ H D g J a bas l o _ _ b ρ S s t τ hMA _ _ hρ hζ _ hP`. Take `⟨φ, hmon, hL, hact, hgeo⟩` from `hP`. Take `⟨r, hr⟩` from `hMA`. Establish `hrpos : 0 < r` using `Nat.pos_of_ne_zero fun h => by`. Use `l.A_pos` as an intermediate fact.

Rewrite `this` using `[hr, h]`. Simplify using `at this`. Establish `hMpos : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Take `⟨hab, hamp, hk⟩` from `PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S t.A τ.G (𝟙 S) φ.hom.left t.L τ.PP.L t.isLB τ.PP.isLB t.ab (isGrpPullback_of_iso φ) hL`. Set `j : 𝟙_ (Over S) ⟶ Out.baseOver S` to `Over.homMk (𝟙 S) (by simp)`.

Take `⟨f, fadd, fker, fbas⟩` from `exists_comb (Q := 𝟙_ (Over S) ⟶ τ.G) bas (fun i => j ≫ t.pt i ≫ φ.inv) l.A fun i => by`. Rewrite using `[← MonObj.comp_pow, ← MonObj.pow_comp, t.torsion, MonObj.one_comp, MonObj.comp_one]`. Take `⟨e', he', e, he, hee⟩` from `Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)`. Use `⟨⟨τ, hab.proper, hamp t.ample, hk t.ktriv, fun x => f (r • e • x), fun x y => ?_, fun x hx => ?_, f, fadd, fker, fun K _ _ x β hβ => ?_⟩, φ, hmon, hL, hact, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, smul_add, fadd]`.

Take `⟨y, hy⟩` from `smul_mem_of_mul ((mul_comm _ _).trans l.prod) he hx`. Rewrite using `[hy, smul_smul, mul_comm, ← hr, fker]`. Establish `: CharZero K` using `RingHom.charZero_iff β.injective |>.1 inferInstance`. Take `⟨hd, I, hI, hev⟩` from `hgeo K x (β.comp (algebraMap o (KA l))) (by`. Rewrite using `[← Category.assoc, hβ, ← Spec.map_comp]`.

Use the proof step `rfl)`. Establish `hA : ∀ y, toUnit (Over.mk x) ≫ f y = I.ev l.A y`. Use `ext_basis (Q := Over.mk x ⟶ τ.G) bas (fun y z => ?_) (I.add _) fun i => ?_` and prove the remaining obligations. Rewrite using `[fadd, MonObj.comp_mul]`. Rewrite using `[fbas, ← cancel_mono φ.hom, hev]`.

Simplify using `only [Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Rewrite using `[← Category.assoc]`. Use `congr 1`. Use `⟨by rw [← hρ]; exact hd, I, by rw [← hζ]; exact hI, hA, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `smul_mem_of_mul l.prod he' hy`.

Establish `h1 : y = e • y + l.M • z` using `by rw [← hz, ← add_smul, add_comm, hee, one_smul]`. Rewrite using `[hA, add_nsmul' (I.add _), hr, I.tower _ _ hMpos hrpos]`. Use `conv_rhs => rw [h1, I.add, (I.ker _ hMpos _).2 ⟨z, rfl⟩, _root_.mul_one]`. Use `show (f _ ≫ φ.hom).left = _`. Rewrite using `[fbas]`.

Simplify using `[j]`.
-/
theorem exists_obj_under : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (o : Type) [CommRing o] [Algebra o (KA l)] (b : TBase o l.A) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (t : TObj g l.A J b (s ≫ spMap (algebraMap o (KA l)))) (τ : SAB H S), l.M ∣ l.A → IsSympBasis D bas → IsFractionRing o (KA l) → algebraMap o (KA l) ρ = (baseKA l).ρ → algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ → (IsReduced S ∨ IsLocallyNoetherian S) → IsPEL D a bas ρ t τ → ∃ ob : Obj D l (baseKA l) s, ObjUnder ob a bas t := by
  intro _ _ E _ _ _ H D g J a bas l o _ _ b ρ S s t τ hMA _ _ hρ hζ _ hP
  obtain ⟨φ, hmon, hL, hact, hgeo⟩ := hP
  obtain ⟨r, hr⟩ := hMA
  have hrpos : 0 < r := Nat.pos_of_ne_zero fun h => by
    have := l.A_pos
    rw [hr, h] at this
    simp at this
  have hMpos : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨hab, hamp, hk⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S t.A τ.G (𝟙 S)
    φ.hom.left t.L τ.PP.L t.isLB τ.PP.isLB t.ab (isGrpPullback_of_iso φ) hL
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (by simp)
  obtain ⟨f, fadd, fker, fbas⟩ := exists_comb (Q := 𝟙_ (Over S) ⟶ τ.G) bas (fun i => j ≫ t.pt i ≫ φ.inv) l.A
    fun i => by
      rw [← MonObj.comp_pow, ← MonObj.pow_comp, t.torsion, MonObj.one_comp, MonObj.comp_one]
  obtain ⟨e', he', e, he, hee⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  refine ⟨⟨τ, hab.proper, hamp t.ample, hk t.ktriv, fun x => f (r • e • x), fun x y => ?_, fun x hx => ?_, f, fadd, fker,
    fun K _ _ x β hβ => ?_⟩, φ, hmon, hL, hact, fun i => ?_⟩
  · rw [smul_add, smul_add, fadd]
  · obtain ⟨y, hy⟩ := smul_mem_of_mul ((mul_comm _ _).trans l.prod) he hx
    rw [hy, smul_smul, mul_comm, ← hr, fker]
  · have : CharZero K := RingHom.charZero_iff β.injective |>.1 inferInstance
    obtain ⟨hd, I, hI, hev⟩ := hgeo K x (β.comp (algebraMap o (KA l))) (by
      rw [← Category.assoc, hβ, ← Spec.map_comp]; rfl)
    have hA : ∀ y, toUnit (Over.mk x) ≫ f y = I.ev l.A y := by
      refine ext_basis (Q := Over.mk x ⟶ τ.G) bas (fun y z => ?_) (I.add _) fun i => ?_
      · rw [fadd, MonObj.comp_mul]
      · rw [fbas, ← cancel_mono φ.hom, hev]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [← Category.assoc]
        congr 1
    refine ⟨by rw [← hρ]; exact hd, I, by rw [← hζ]; exact hI, hA, fun y hy => ?_⟩
    obtain ⟨z, hz⟩ := smul_mem_of_mul l.prod he' hy
    have h1 : y = e • y + l.M • z := by rw [← hz, ← add_smul, add_comm, hee, one_smul]
    rw [hA, add_nsmul' (I.add _), hr, I.tower _ _ hMpos hrpos]
    conv_rhs => rw [h1, I.add, (I.ker _ hMpos _).2 ⟨z, rfl⟩, _root_.mul_one]
  · show (f _ ≫ φ.hom).left = _
    rw [fbas]
    simp [j]

end GlobalTheory.ThetaToObj
end
