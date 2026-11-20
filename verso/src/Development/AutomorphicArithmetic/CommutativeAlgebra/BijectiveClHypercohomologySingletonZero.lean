import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma sec_comp {A B C : Shv ℤ} (p : A ⟶ B) (q : B ⟶ C) {V : Scheme.{0}} (x : Sec A V) :
    Sec.map (p ≫ q) x = Sec.map q (Sec.map p x) := rfl

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Establish `hinj : ∀ U : Scheme, Function.Injective (Sec.map (resι ℤ F) (U` using `U)) := fun U => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).2.1`. Establish `hex : ∀ (U : Scheme) (x : Sec M U), ∃ a : Sec F U, Sec.map (resι ℤ F) a = Sec.map g x`. Introduce `U x`. Use `((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).1 _).1 ?_` and prove the remaining obligations. Rewrite using `[← sec_comp, hg]`.

Both sides reduce to the same expression. Set `φ : ∀ U : Scheme, Sec M U → Sec F U` to `fun U x => (hex U x).choose`. Establish `hφ : ∀ U x, Sec.map (resι ℤ F) (φ U x) = Sec.map g x` using `fun U x => (hex U x).choose_spec`. Set `η : M.obj ⟶ F.obj` to `{ app := fun U => ModuleCat.ofHom { toFun := φ U.unop map_add' := fun x y => hinj _ (by`. Rewrite using `[hφ]`.

Use `show (ModuleCat.Hom.hom _) (x + y) = (ModuleCat.Hom.hom _) (φ _ x + φ _ y)`. Rewrite using `[map_add, map_add]`. Conclude with `congrArg₂ (· + ·) (hφ _ x).symm (hφ _ y).symm)`. Use the proof step `map_smul' := fun r x => hinj _ (by`. Rewrite using `[hφ, RingHom.id_apply]`.

Establish `e1` using `(ModuleCat.Hom.hom (g.hom.app U)).map_smul r x`. Establish `e2` using `(ModuleCat.Hom.hom ((resι ℤ F).hom.app U)).map_smul r (φ _ x)`. Conclude with `e1.trans ((congrArg _ (hφ _ x).symm).trans e2.symm)) }`. Use `naturality := by`. Introduce `U V h`.

Use extensionality with `x`. Apply `hinj` to reduce the goal to its premises. Establish `n1` using `congrArg (fun k => ModuleCat.Hom.hom k x) (g.hom.naturality h)`. Establish `n2` using `congrArg (fun k => ModuleCat.Hom.hom k (φ _ x)) ((resι ℤ F).hom.naturality h)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at n1 n2`.

Use `show Sec.map (resι ℤ F) (φ _ ((ModuleCat.Hom.hom (M.obj.map h)) x)) = Sec.map (resι ℤ F) ((ModuleCat.Hom.hom (F.obj.map h)) (φ _ x))`. Rewrite using `[hφ]`. Use `n1.trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ n2.symm` and prove the remaining obligations. Conclude with `congrArg _ (hφ _ x).symm }`.

Use `⟨⟨η⟩, (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (⟨η⟩ ≫ resι ℤ F)).2.2.2 g (fun U a => ?_)⟩` and prove the remaining obligations. Rewrite using `[sec_comp]`. Conclude with `hφ U a`.
-/
private lemma exists_lift {M F : Shv ℤ} (g : M ⟶ (res ℤ F).X 0) (hg : g ≫ (res ℤ F).d 0 1 = 0) :
    ∃ f : M ⟶ F, f ≫ resι ℤ F = g := by
  classical
  have hinj : ∀ U : Scheme, Function.Injective (Sec.map (resι ℤ F) (U := U)) :=
    fun U => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).2.1
  have hex : ∀ (U : Scheme) (x : Sec M U), ∃ a : Sec F U, Sec.map (resι ℤ F) a = Sec.map g x := by
    intro U x
    refine ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).1 _).1 ?_
    rw [← sec_comp, hg]
    rfl
  let φ : ∀ U : Scheme, Sec M U → Sec F U := fun U x => (hex U x).choose
  have hφ : ∀ U x, Sec.map (resι ℤ F) (φ U x) = Sec.map g x := fun U x => (hex U x).choose_spec
  let η : M.obj ⟶ F.obj :=
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := fun x y => hinj _ (by
            rw [hφ]
            show (ModuleCat.Hom.hom _) (x + y) = (ModuleCat.Hom.hom _) (φ _ x + φ _ y)
            rw [map_add, map_add]
            exact congrArg₂ (· + ·) (hφ _ x).symm (hφ _ y).symm)
          map_smul' := fun r x => hinj _ (by
            rw [hφ, RingHom.id_apply]
            have e1 := (ModuleCat.Hom.hom (g.hom.app U)).map_smul r x
            have e2 := (ModuleCat.Hom.hom ((resι ℤ F).hom.app U)).map_smul r (φ _ x)
            exact e1.trans ((congrArg _ (hφ _ x).symm).trans e2.symm)) }
      naturality := by
        intro U V h
        ext x
        apply hinj
        have n1 := congrArg (fun k => ModuleCat.Hom.hom k x) (g.hom.naturality h)
        have n2 := congrArg (fun k => ModuleCat.Hom.hom k (φ _ x)) ((resι ℤ F).hom.naturality h)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n1 n2
        show Sec.map (resι ℤ F) (φ _ ((ModuleCat.Hom.hom (M.obj.map h)) x)) =
          Sec.map (resι ℤ F) ((ModuleCat.Hom.hom (F.obj.map h)) (φ _ x))
        rw [hφ]
        refine n1.trans ?_
        refine Eq.trans ?_ n2.symm
        exact congrArg _ (hφ _ x).symm }
  refine ⟨⟨η⟩, (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (⟨η⟩ ≫ resι ℤ F)).2.2.2 g (fun U a => ?_)⟩
  rw [sec_comp]
  exact hφ U a

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Rewrite using `[HomologicalComplex.comp_f, ← Category.assoc]`. Establish `h : sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f).f 0 = f ≫ sglι F`. Simplify using `[sglι, CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self]`. Rewrite using `[h, Category.assoc, (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.1]`.
-/
private lemma sgl_f {M F : Shv ℤ} (f : M ⟶ F) :
    sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F).f 0 = f ≫ resι ℤ F := by
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  have h : sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f).f 0 = f ≫ sglι F := by
    simp [sglι, CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self]
  rw [h, Category.assoc, (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.1]

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `M F`. Establish `hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl M).X p)` using `fun p hp => HomologicalComplex.isZero_single_obj_X _ _ _ _ hp`. Establish `hL : IsZero ((res ℤ F).X (-1))` using `by haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.1`. Conclude with `CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by norm_num)`. Establish `hβ0 : ∀ β : Cochain (sgl M) (res ℤ F) (-1), β = 0`.

Introduce `β`. Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : p = 0`. Substitute `hp` using the available equality. Take `rfl : q = -1` from `by omega`.

Conclude with `hL.eq_of_tgt _ _`. Conclude with `(hz p hp).eq_of_src _ _`. Establish `hcob : ∀ x : Cocycle (sgl M) (res ℤ F) 0, x ∈ coboundaries (sgl M) (res ℤ F) 0 → x = 0`. Introduce `x hx`. Take `⟨β, hβ⟩` from `(mem_coboundaries_iff x (-1) (by norm_num)).1 hx`.

Apply `Cocycle.ext` to reduce the goal to its premises. Rewrite using `[← hβ, hβ0 β, δ_zero]`. Both sides reduce to the same expression. Establish `hmono : Mono (resι ℤ F)` using `(GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.1`. Establish `hsg : IsIso (sglι M)` using `by dsimp [sglι] infer_instance`.

Prove the components needed by the constructor for the conclusion. Introduce `f f' h`. Establish `h1 : Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F) = Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f' ≫ resAug F)`. Use `hcob _ ((CohomologyClass.mk_eq_zero_iff _).1 (by rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 h))` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.

Establish `h2` using `congrArg (fun x : Cocycle (sgl M) (res ℤ F) 0 => (x : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0)) h1`. Simplify using `only [Cocycle.ofHom_coe, Cochain.ofHom_v] at h2`. Apply `(cancel_mono (resι ℤ F)).1` to reduce the goal to its premises. Rewrite using `[← sgl_f, ← sgl_f, h2]`. Introduce `c`.

Take `⟨z, rfl⟩` from `CohomologyClass.mk_surjective c`. Establish `hz1 : (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0) ≫ (res ℤ F).d 0 1 = 0`. Establish `e` using `congrArg (fun w : Cochain (sgl M) (res ℤ F) 1 => w.v 0 1 (zero_add 1)) ((Cocycle.mem_iff 0 1 (zero_add 1) _).1 z.2)`. Simplify using `only [δ_zero_cochain_v, Cochain.zero_v] at e`. Rewrite `e` using `[(hz 1 one_ne_zero).eq_of_tgt ((sgl M).d 0 1) 0, zero_comp, sub_zero]`. Then use the resulting hypothesis.

Take `⟨f, hf⟩` from `exists_lift (sglι M ≫ (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0)) (by rw [Category.assoc, hz1, comp_zero])`. Use `⟨f, ?_⟩` and prove the remaining obligations. Use `show CohomologyClass.mk _ = CohomologyClass.mk z`. Use `congr 1`. Apply `Cocycle.ext` to reduce the goal to its premises.

Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations. Rewrite `hpq` using `[add_zero]`. Substitute `hpq` using the available equality. Distinguish the cases in `hp : p = 0`. Substitute `hp` using the available equality.

Rewrite using `[Cocycle.ofHom_coe, Cochain.ofHom_v, ← cancel_epi (sglι M), sgl_f, hf]`. Conclude with `(hz p hp).eq_of_src _ _`.
-/
theorem UpperTheory.bijective_cl_hypercohomology_singleton_zero :
    ∀ (M F : Shv ℤ), Function.Bijective (cl : (M ⟶ F) → HK ℤ (sgl M) F 0) := by
  intro M F
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl M).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
  have hL : IsZero ((res ℤ F).X (-1)) := by
    haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.1
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by norm_num)
  have hβ0 : ∀ β : Cochain (sgl M) (res ℤ F) (-1), β = 0 := by
    intro β
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = -1 := by omega
      exact hL.eq_of_tgt _ _
    · exact (hz p hp).eq_of_src _ _
  have hcob : ∀ x : Cocycle (sgl M) (res ℤ F) 0, x ∈ coboundaries (sgl M) (res ℤ F) 0 → x = 0 := by
    intro x hx
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff x (-1) (by norm_num)).1 hx
    apply Cocycle.ext
    rw [← hβ, hβ0 β, δ_zero]
    rfl
  have hmono : Mono (resι ℤ F) := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.1
  have hsg : IsIso (sglι M) := by
    dsimp [sglι]
    infer_instance
  constructor
  · intro f f' h
    have h1 : Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F)
        = Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f' ≫ resAug F) := by
      have := hcob _ ((CohomologyClass.mk_eq_zero_iff _).1
        (by rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 h))
      exact sub_eq_zero.1 this
    have h2 := congrArg (fun x : Cocycle (sgl M) (res ℤ F) 0 =>
      (x : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0)) h1
    simp only [Cocycle.ofHom_coe, Cochain.ofHom_v] at h2
    apply (cancel_mono (resι ℤ F)).1
    rw [← sgl_f, ← sgl_f, h2]
  · intro c
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
    have hz1 : (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0) ≫ (res ℤ F).d 0 1 = 0 := by
      have e := congrArg (fun w : Cochain (sgl M) (res ℤ F) 1 => w.v 0 1 (zero_add 1))
        ((Cocycle.mem_iff 0 1 (zero_add 1) _).1 z.2)
      simp only [δ_zero_cochain_v, Cochain.zero_v] at e
      rwa [(hz 1 one_ne_zero).eq_of_tgt ((sgl M).d 0 1) 0, zero_comp, sub_zero] at e
    obtain ⟨f, hf⟩ := exists_lift (sglι M ≫ (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0))
      (by rw [Category.assoc, hz1, comp_zero])
    refine ⟨f, ?_⟩
    show CohomologyClass.mk _ = CohomologyClass.mk z
    congr 1
    apply Cocycle.ext
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [add_zero] at hpq
    subst hpq
    by_cases hp : p = 0
    · subst hp
      rw [Cocycle.ofHom_coe, Cochain.ofHom_v, ← cancel_epi (sglι M), sgl_f, hf]
    · exact (hz p hp).eq_of_src _ _
