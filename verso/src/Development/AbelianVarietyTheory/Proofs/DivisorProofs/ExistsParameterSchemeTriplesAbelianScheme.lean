import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ParamTriple

/- English proof (translation)
Introduce `S _ _ A _ hA V hV`. Use `hA.smooth` as an intermediate fact. Establish `: GeometricallyIntegral A.hom` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected`. Establish `hAA` using `AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA`. Use `hAA.smooth` as an intermediate fact.

Establish `: GeometricallyIntegral (A ⊗ A).hom` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hAA.smooth hAA.geomConnected`. Set `B : Over S` to `Over.mk (V.ι ≫ A.hom)`. Set `j : B ⟶ A` to `Over.homMk V.ι`. Establish `hBs : Smooth B.hom` using `by dsimp [B]; infer_instance`. Establish `hBsurj : Surjective (V.ι ≫ A.hom)` using `⟨fun s => by`.

Take `⟨x, hx, rfl⟩` from `hV s`. Conclude with `⟨⟨x, hx⟩, rfl⟩⟩`. Establish `hBgi : GeometricallyIntegral B.hom` using `GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ V.ι A.hom hBsurj`. Set `P : Over S` to `(A ⊗ A) ⊗ B`. Set `X : P ⟶ A` to `fst _ _ ≫ fst A A`.

Set `Aa : P ⟶ A` to `fst _ _ ≫ snd A A`. Set `Vv : P ⟶ A` to `snd _ _ ≫ j`. Set `O : P.left.Opens` to `(X * Aa).left ⁻¹ᵁ V ⊓ (X * Aa⁻¹).left ⁻¹ᵁ V ⊓ (Vv * Aa).left ⁻¹ᵁ V ⊓ (Vv * Aa⁻¹).left ⁻¹ᵁ V`. Establish `hsurj : Surjective (O.ι ≫ X.left)` using `GlobalTheory.T.exists_translates_surjective_fibrewise_dense_open S A hA V B j (fun b => b.2) hBs hBgi`. Set `Y : Over S` to `Over.mk (O.ι ≫ P.hom)`.

Set `i : Y ⟶ P` to `Over.homMk O.ι`. Establish `hmem : ∀ (f : P ⟶ A), O ≤ f.left ⁻¹ᵁ V → ∀ y, (i ≫ f).left y ∈ V`. Introduce `f hf y`. Conclude with `hf y.2`. Set `s : B ⟶ P` to `lift (lift j 1) (𝟙 B)`.

Establish `hsX : s ≫ X = j` using `by simp [s, X]`. Establish `hsA : s ≫ Aa = 1` using `by simp [s, Aa]`. Establish `hsV : s ≫ Vv = j` using `by simp [s, Vv]`. Establish `hsO : ∀ b, s.left b ∈ O`. Introduce `b`.

Establish `h1 : ∀ f : P ⟶ A, s ≫ f = j → s.left b ∈ f.left ⁻¹ᵁ V`. Introduce `f hf`. Use `show (s.left ≫ f.left) b ∈ V`. Rewrite using `[← Over.comp_left, hf]`. Conclude with `b.2`.

Use `⟨⟨⟨h1 _ ?_, h1 _ ?_⟩, h1 _ ?_⟩, h1 _ ?_⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, hsX, hsA, _root_.mul_one]`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, hsX, hsA, inv_one, _root_.mul_one]`. Rewrite using `[MonObj.comp_mul, hsV, hsA, _root_.mul_one]`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, hsV, hsA, inv_one, _root_.mul_one]`.

Establish `hrO : Set.range s.left ⊆ Set.range O.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `hsO b`. Set `e0 : V.toScheme ⟶ O.toScheme` to `IsOpenImmersion.lift O.ι s.left hrO`.

Establish `he0 : e0 ≫ O.ι = s.left` using `IsOpenImmersion.lift_fac _ _ _`. Set `x : Y ⟶ A` to `i ≫ X`. Set `a : Y ⟶ A` to `i ≫ Aa`. Set `v : Y ⟶ A` to `i ≫ Vv`. Set `p : Y.left ⟶ V.toScheme` to `O.ι ≫ (snd (A ⊗ A) B).left`.

Establish `hxl : x.left = O.ι ≫ X.left` using `rfl`. Establish `hre : Set.range e0 ⊆ Set.range (x.left ⁻¹ᵁ V).ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨b, rfl⟩`. Use `show (e0 ≫ x.left) b ∈ V`.

Rewrite using `[hxl, ← Category.assoc, he0, ← Over.comp_left, hsX]`. Conclude with `b.2`. Set `e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme` to `IsOpenImmersion.lift _ e0 hre`. Establish `he : e ≫ (x.left ⁻¹ᵁ V).ι = e0` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hsec : e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _`.

Rewrite using `[← Category.assoc, ← Category.assoc, he, he0]`. Use `show (s ≫ snd (A ⊗ A) B).left = _`. Rewrite using `[lift_snd]`. Both sides reduce to the same expression. Take `⟨s0⟩` from `(inferInstance : Nonempty S)`.

Take `⟨x0, hx0, -⟩` from `hV s0`. Establish `: Nonempty V.toScheme` using `⟨⟨x0, hx0⟩⟩`. Establish `: IsIntegral A.left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom`. Establish `: IsIntegral V.toScheme` using `isIntegral_of_isOpenImmersion V.ι`. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`.

Establish `: IsLocallyNoetherian V.toScheme` using `LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ A.hom)`. Establish `: Flat (A ⊗ A).hom` using `inferInstance`. Establish `: UniversallyOpen (A ⊗ A).hom` using `inferInstance`. Establish `: IsIntegral B.left` using `‹IsIntegral V.toScheme›`. Establish `: IsLocallyNoetherian B.left` using `‹IsLocallyNoetherian V.toScheme›`.

Establish `: IsIntegral P.left` using `inferInstanceAs (IsIntegral (pullback (A ⊗ A).hom B.hom))`. Take `⟨b0⟩` from `(inferInstance : Nonempty V.toScheme)`. Establish `: Nonempty O.toScheme` using `⟨⟨s.left b0, hsO b0⟩⟩`. Establish `hYi : IsIntegral O.toScheme` using `isIntegral_of_isOpenImmersion O.ι`. Establish `hgi : GeometricallyIntegral (((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom)`.

Use `GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ _ _ ?_` and prove the remaining obligations. Establish `: Surjective (e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom)`. Rewrite using `[hsec]`. Use `infer_instance`. Conclude with `Surjective.of_comp e _`.

Establish `hxa : x * a = i ≫ (X * Aa)` using `by simp only [x, a, MonObj.comp_mul]`. Establish `hxa' : x * a⁻¹ = i ≫ (X * Aa⁻¹)` using `by simp only [x, a, MonObj.comp_mul, GrpObj.comp_inv]`. Establish `hva : v * a = i ≫ (Vv * Aa)` using `by simp only [v, a, MonObj.comp_mul]`. Establish `hva' : v * a⁻¹ = i ≫ (Vv * Aa⁻¹)` using `by simp only [v, a, MonObj.comp_mul, GrpObj.comp_inv]`. Use `⟨Y, x, a, v, p, e, hYi, ?_, hsurj, ?_, fun y => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show Smooth (O.ι ≫ pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom) infer_instance`. Use `show (O.ι ≫ (snd (A ⊗ A) B).left) ≫ V.ι = O.ι ≫ (snd (A ⊗ A) B ≫ j).left`. Rewrite using `[Category.assoc, Over.comp_left]`. Both sides reduce to the same expression. Rewrite using `[hxa]`.

Conclude with `hmem _ (fun z hz => hz.1.1.1) y`. Rewrite using `[hxa']`. Conclude with `hmem _ (fun z hz => hz.1.1.2) y`. Rewrite using `[hva]`. Conclude with `hmem _ (fun z hz => hz.1.2) y`.

Rewrite using `[hva']`. Conclude with `hmem _ (fun z hz => hz.2) y`. Use `show Smooth ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom) infer_instance`. Use `show GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)`. Rewrite using `[← Category.assoc]`.

Conclude with `hgi`. Use `show e ≫ (x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _`. Rewrite using `[← hsec]`. Simplify using `only [Category.assoc]`.
-/
theorem exists_param : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  intro S _ _ A _ hA V hV
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.smooth
  have : GeometricallyIntegral (A ⊗ A).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hAA.smooth hAA.geomConnected
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let j : B ⟶ A := Over.homMk V.ι
  have hBs : Smooth B.hom := by dsimp [B]; infer_instance
  have hBsurj : Surjective (V.ι ≫ A.hom) := ⟨fun s => by
    obtain ⟨x, hx, rfl⟩ := hV s
    exact ⟨⟨x, hx⟩, rfl⟩⟩
  have hBgi : GeometricallyIntegral B.hom := GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ V.ι A.hom hBsurj
  let P : Over S := (A ⊗ A) ⊗ B
  let X : P ⟶ A := fst _ _ ≫ fst A A
  let Aa : P ⟶ A := fst _ _ ≫ snd A A
  let Vv : P ⟶ A := snd _ _ ≫ j
  let O : P.left.Opens := (X * Aa).left ⁻¹ᵁ V ⊓ (X * Aa⁻¹).left ⁻¹ᵁ V ⊓ (Vv * Aa).left ⁻¹ᵁ V ⊓
    (Vv * Aa⁻¹).left ⁻¹ᵁ V
  have hsurj : Surjective (O.ι ≫ X.left) :=
    GlobalTheory.T.exists_translates_surjective_fibrewise_dense_open S A hA V B j (fun b => b.2) hBs hBgi
  let Y : Over S := Over.mk (O.ι ≫ P.hom)
  let i : Y ⟶ P := Over.homMk O.ι
  have hmem : ∀ (f : P ⟶ A), O ≤ f.left ⁻¹ᵁ V → ∀ y, (i ≫ f).left y ∈ V := by
    intro f hf y
    exact hf y.2

  let s : B ⟶ P := lift (lift j 1) (𝟙 B)
  have hsX : s ≫ X = j := by simp [s, X]
  have hsA : s ≫ Aa = 1 := by simp [s, Aa]
  have hsV : s ≫ Vv = j := by simp [s, Vv]
  have hsO : ∀ b, s.left b ∈ O := by
    intro b
    have h1 : ∀ f : P ⟶ A, s ≫ f = j → s.left b ∈ f.left ⁻¹ᵁ V := by
      intro f hf
      show (s.left ≫ f.left) b ∈ V
      rw [← Over.comp_left, hf]
      exact b.2
    refine ⟨⟨⟨h1 _ ?_, h1 _ ?_⟩, h1 _ ?_⟩, h1 _ ?_⟩
    · rw [MonObj.comp_mul, hsX, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsX, hsA, inv_one, _root_.mul_one]
    · rw [MonObj.comp_mul, hsV, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsV, hsA, inv_one, _root_.mul_one]
  have hrO : Set.range s.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩; exact hsO b
  let e0 : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι s.left hrO
  have he0 : e0 ≫ O.ι = s.left := IsOpenImmersion.lift_fac _ _ _
  let x : Y ⟶ A := i ≫ X
  let a : Y ⟶ A := i ≫ Aa
  let v : Y ⟶ A := i ≫ Vv
  let p : Y.left ⟶ V.toScheme := O.ι ≫ (snd (A ⊗ A) B).left
  have hxl : x.left = O.ι ≫ X.left := rfl
  have hre : Set.range e0 ⊆ Set.range (x.left ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩
    show (e0 ≫ x.left) b ∈ V
    rw [hxl, ← Category.assoc, he0, ← Over.comp_left, hsX]
    exact b.2
  let e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ e0 hre
  have he : e ≫ (x.left ⁻¹ᵁ V).ι = e0 := IsOpenImmersion.lift_fac _ _ _
  have hsec : e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, he, he0]
    show (s ≫ snd (A ⊗ A) B).left = _
    rw [lift_snd]; rfl
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  obtain ⟨x0, hx0, -⟩ := hV s0
  have : Nonempty V.toScheme := ⟨⟨x0, hx0⟩⟩
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ A.hom)
  have : Flat (A ⊗ A).hom := inferInstance
  have : UniversallyOpen (A ⊗ A).hom := inferInstance
  have : IsIntegral B.left := ‹IsIntegral V.toScheme›
  have : IsLocallyNoetherian B.left := ‹IsLocallyNoetherian V.toScheme›
  have : IsIntegral P.left := inferInstanceAs (IsIntegral (pullback (A ⊗ A).hom B.hom))
  obtain ⟨b0⟩ := (inferInstance : Nonempty V.toScheme)
  have : Nonempty O.toScheme := ⟨⟨s.left b0, hsO b0⟩⟩
  have hYi : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have hgi : GeometricallyIntegral (((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
    refine GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ _ _ ?_
    have : Surjective (e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
      rw [hsec]; infer_instance
    exact Surjective.of_comp e _
  have hxa : x * a = i ≫ (X * Aa) := by simp only [x, a, MonObj.comp_mul]
  have hxa' : x * a⁻¹ = i ≫ (X * Aa⁻¹) := by simp only [x, a, MonObj.comp_mul, GrpObj.comp_inv]
  have hva : v * a = i ≫ (Vv * Aa) := by simp only [v, a, MonObj.comp_mul]
  have hva' : v * a⁻¹ = i ≫ (Vv * Aa⁻¹) := by simp only [v, a, MonObj.comp_mul, GrpObj.comp_inv]
  refine ⟨Y, x, a, v, p, e, hYi, ?_, hsurj, ?_, fun y => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show Smooth (O.ι ≫ pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    infer_instance
  · show (O.ι ≫ (snd (A ⊗ A) B).left) ≫ V.ι = O.ι ≫ (snd (A ⊗ A) B ≫ j).left
    rw [Category.assoc, Over.comp_left]; rfl
  · rw [hxa]; exact hmem _ (fun z hz => hz.1.1.1) y
  · rw [hxa']; exact hmem _ (fun z hz => hz.1.1.2) y
  · rw [hva]; exact hmem _ (fun z hz => hz.1.2) y
  · rw [hva']; exact hmem _ (fun z hz => hz.2) y
  · show Smooth ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    infer_instance
  · show GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    rw [← Category.assoc]; exact hgi
  · show e ≫ (x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _
    rw [← hsec]; simp only [Category.assoc]

end GlobalTheory.ParamTriple
