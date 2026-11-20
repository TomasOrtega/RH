import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ResBasic

variable (R : Type) [CommRing R]

def resHom {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    congrArg (fun f => HomologicalComplex.Hom.f f 0)
      (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))⟩

/- English proof (translation)
The claim follows from `mono_of_isLimit_fork (injectiveResolution F).isLimitKernelFork`.
-/
theorem mono_ι_f_zero (F : Shv R) : Mono ((injectiveResolution F).ι.f 0) :=
  mono_of_isLimit_fork (injectiveResolution F).isLimitKernelFork

/- English proof (translation)
Establish `h1` using `mono_ι_f_zero R F`. Express the relevant statement in the definitionally equal form `Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0)`. Rewrite using `[InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]`. Conclude with `@mono_comp _ _ _ _ _ _ h1 _ inferInstance`.
-/
theorem mono_resι (F : Shv R) : Mono (resι R F) := by
  have h1 := mono_ι_f_zero R F
  change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0)
  rw [InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
  exact @mono_comp _ _ _ _ _ _ h1 _ inferInstance

/- English proof (translation)
Use `HomologicalComplex.single_map_f_self (V := Shv R) (ComplexShape.up ℤ) 0 φ` as an intermediate fact. Express the relevant statement in the definitionally equal form `(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ).f 0 = _`. Rewrite using `[this, Iso.inv_hom_id_assoc]`. Both sides reduce to the same expression.
-/
theorem sglι_comp_single_map {F G : Shv R} (φ : F ⟶ G) :
    sglι F ≫ ((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0 = φ ≫ sglι G := by
  have := HomologicalComplex.single_map_f_self (V := Shv R) (ComplexShape.up ℤ) 0 φ
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ).f 0 = _
  rw [this, Iso.inv_hom_id_assoc]
  rfl

/- English proof (translation)
Introduce `R _ F`. Establish `hinj : ∀ n, Injective ((res R F).X n)` using `fun n => inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))`. Establish `hge : (res R F).IsStrictlyGE 0` using `inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)`. Establish `hq : QuasiIso (resAug F)` using `inferInstanceAs (QuasiIso (injectiveResolution F).ι')`. Establish `hι : ∀ F : Shv R, sglι F ≫ (resAug F).f 0 = resι R F` using `fun _ => rfl`.

Establish `hcomm : ∀ (G : Shv R) (φ : F ⟶ G), resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G` using `fun G φ => (resHom R φ).ι'_comp_hom'`. Use `⟨CochainComplex.isKInjective_of_injective _ 0, hinj, hge, hq, hι F, mono_resι R F, ?_, fun G φ => ⟨hcomm G φ, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hι F, Category.assoc, (resAug F).comm 0 1]`. Simplify using the standard rewrite rules. Rewrite using `[← hι F, Category.assoc, ← HomologicalComplex.comp_f, hcomm G φ, HomologicalComplex.comp_f, ← hι G, ← Category.assoc, sglι_comp_single_map, Category.assoc]`.
-/
theorem res_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧
    resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧
      resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  intro R _ F
  have hinj : ∀ n, Injective ((res R F).X n) := fun n =>
    inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  have hge : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  have hq : QuasiIso (resAug F) := inferInstanceAs (QuasiIso (injectiveResolution F).ι')
  have hι : ∀ F : Shv R, sglι F ≫ (resAug F).f 0 = resι R F := fun _ => rfl
  have hcomm : ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G :=
    fun G φ => (resHom R φ).ι'_comp_hom'
  refine ⟨CochainComplex.isKInjective_of_injective _ 0, hinj, hge, hq, hι F, mono_resι R F, ?_,
    fun G φ => ⟨hcomm G φ, ?_⟩⟩
  · rw [← hι F, Category.assoc, (resAug F).comm 0 1]
    simp
  · rw [← hι F, Category.assoc, ← HomologicalComplex.comp_f, hcomm G φ, HomologicalComplex.comp_f, ← hι G,
      ← Category.assoc, sglι_comp_single_map, Category.assoc]

end GlobalTheory.EtC.ResBasic
