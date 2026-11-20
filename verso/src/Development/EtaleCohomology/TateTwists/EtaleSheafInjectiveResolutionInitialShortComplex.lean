import Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionSectionsLocallyExact

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ResSecPf

variable (R : Type) [CommRing R]

noncomputable abbrev secF (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (U : Scheme.{0}) : PreservesLimits (secF R U) := inferInstance

/- English proof (translation)
Establish `h1 : (res R F).ExactAt n`. Unfold `res`. Rewrite using `[← quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))]`. Use `infer_instance`. Conclude with `(HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1 h1`.
-/
lemma exact_pos (F : Shv R) (m n k : ℤ) (hn : 0 < n) (hm : m + 1 = n) (hk : n + 1 = k) :
    (ShortComplex.mk ((res R F).d m n) ((res R F).d n k) (by simp)).Exact := by
  have h1 : (res R F).ExactAt n := by
    unfold res
    rw [← quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))]
    infer_instance
  exact (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1 h1

/- English proof (translation)
Establish `hz : IsZero ((res R F).X n)`. Unfold `res`. Conclude with `CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)`. Use `(hz.of_iso (Iso.refl _)).eq_of_src (𝟙 _) 0` as an intermediate fact. Prove the components needed by the constructor for the conclusion.

Introduce `a b`. Establish `e : ∀ x : Sec ((res R F).X n) U, x = 0`. Introduce `x`. Use `congrArg (fun f => Sec.map f x) (hz.eq_of_src (𝟙 _) 0)` as an intermediate fact. Simplify `this` using `[Sec.map]`.

Rewrite using `[e a, e b]`.
-/
lemma subsing (F : Shv R) (U : Scheme.{0}) (n : ℤ) (hn : n < 0) :
    Subsingleton (Sec ((res R F).X n) U) := by
  have hz : IsZero ((res R F).X n) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have := (hz.of_iso (Iso.refl _)).eq_of_src (𝟙 _) 0
  constructor
  intro a b
  have e : ∀ x : Sec ((res R F).X n) U, x = 0 := by
    intro x
    have := congrArg (fun f => Sec.map f x) (hz.eq_of_src (𝟙 _) 0)
    simpa [Sec.map] using this
  rw [e a, e b]

/- English proof (translation)
Unfold `resι`. Rewrite using `[InjectiveResolution.ι'_f_zero]`. Use `erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]`.
-/
lemma resι_e (F : Shv R) :
    resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom = (injectiveResolution F).ι.f 0 := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/- English proof (translation)
Rewrite using `[InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]`. Simplify using the standard rewrite rules.
-/
lemma d01' (F : Shv R) : ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
    (injectiveResolution F).cocomplex.d 0 1 = (injectiveResolution F).cochainComplex.d 0 1 ≫
      ((injectiveResolution F).cochainComplexXIso 1 1 rfl).hom := by
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  simp

/- English proof (translation)
Establish `h` using `(injectiveResolution F).ι'.comm 0 1`. Unfold `resι res`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations. Use `erw [h]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
lemma etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  unfold resι res
  refine (Category.assoc _ _ _).trans ?_
  erw [h]
  simp
  rfl

noncomputable abbrev S0 (F : Shv R) : ShortComplex (Shv R) := ShortComplex.mk _ _ (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)

/- English proof (translation)
Set `I` to `injectiveResolution F`. Establish `hN : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact` using `ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork`. Use `(ShortComplex.exact_iff_of_iso ?_).2 hN` and prove the remaining obligations. Use `ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl) (I.cochainComplexXIso 1 1 rfl) ?_ ?_` and prove the remaining obligations. Conclude with `(Category.id_comp _).trans (resι_e R F).symm`.

Conclude with `d01' R F`.
-/
lemma etaleSheaf_injectiveResolution_initial_shortComplex_exact (F : Shv R) : (S0 R F).Exact := by
  let I := injectiveResolution F
  have hN : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
    ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork
  refine (ShortComplex.exact_iff_of_iso ?_).2 hN
  refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl) (I.cochainComplexXIso 1 1 rfl) ?_ ?_
  · exact (Category.id_comp _).trans (resι_e R F).symm
  · exact d01' R F

/- English proof (translation)
Establish `: Mono ((injectiveResolution F).ι.f 0)` using `inferInstance`. Establish `h` using `resι_e R F`. Establish `: Mono (resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom)`. Rewrite using `[h]`. Use the matching hypothesis.

Conclude with `mono_of_mono _ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom`.
-/
lemma mono_resι_var (F : Shv R) : Mono (resι R F) := by
  have : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h := resι_e R F
  have : Mono (resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom) := by
    rw [h]; assumption
  exact mono_of_mono _ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom

def exact_loc : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact →
  ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `hE : ((S0 R F).map (secF R U)).Exact` using `(etaleSheaf_injectiveResolution_initial_shortComplex_exact R F).map_of_mono_of_preservesKernel _ (mono_resι_var R F) inferInstance`. Rewrite `hE` using `[ShortComplex.moduleCat_exact_iff]`. Conclude with `hE z hz`.

Introduce and unpack `⟨a, rfl⟩`. Use `congrArg (fun f => Sec.map f a) (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)` as an intermediate fact. Simplify `this` using `[Sec.map]`.
-/
lemma part1 (F : Shv R) (U : Scheme.{0}) (z : Sec ((res R F).X 0) U) :
    Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z := by
  constructor
  · intro hz
    have hE : ((S0 R F).map (secF R U)).Exact :=
      (etaleSheaf_injectiveResolution_initial_shortComplex_exact R F).map_of_mono_of_preservesKernel _ (mono_resι_var R F) inferInstance
    rw [ShortComplex.moduleCat_exact_iff] at hE
    exact hE z hz
  · rintro ⟨a, rfl⟩
    have := congrArg (fun f => Sec.map f a) (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)
    simpa [Sec.map] using this

/- English proof (translation)
Use `mono_resι_var R F` as an intermediate fact. Establish `: Mono ((secF R U).map (resι R F))` using `inferInstance`. Conclude with `(ModuleCat.mono_iff_injective _).1 this`.
-/
lemma part2 (F : Shv R) (U : Scheme.{0}) : Function.Injective (Sec.map (resι R F) (U := U)) := by
  have := mono_resι_var R F
  have : Mono ((secF R U).map (resι R F)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

end LateralTheory.EtaleFoundations.ResSecPf

open LateralTheory.EtaleFoundations.ResSecPf in
/- English proof (translation)
Introduce `R _ F U`. Use `⟨part1 R F U, part2 R F U, ?_, fun n hn => subsing R F U n hn⟩` and prove the remaining obligations. Introduce `m n k hn hm z hk hz`. Conclude with `hL R _ (exact_pos R F m n k hn hm hk) U z hz`.
-/
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_sections_exact_of_local_exactness (hL : exact_loc) : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionSectionsLocallyExact := by
  intro R _ F U
  refine ⟨part1 R F U, part2 R F U, ?_, fun n hn => subsing R F U n hn⟩
  intro m n k hn hm z hk hz
  exact hL R _ (exact_pos R F m n k hn hm hk) U z hz
