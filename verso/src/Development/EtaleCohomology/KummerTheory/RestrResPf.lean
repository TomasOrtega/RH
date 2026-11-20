import Development.EtaleCohomology.KummerTheory.BockCut

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RestrResPf

instance restrAdditive (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) : (restr φ).Additive where
  map_add {X Y f g} := by
    ext U x
    rfl

/- English proof (translation)
The claim follows from `(hex R (C.map (restr φ))).2 (fun U b hb => (hex S C).1 h U b hb)`.
-/
theorem restr_exact (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S)
    (C : ShortComplex (Shv S)) (h : C.Exact) : (C.map (restr φ)).Exact :=
  (hex R (C.map (restr φ))).2 (fun U b hb => (hex S C).1 h U b hb)

/- English proof (translation)
The claim follows from `Functor.preservesHomology_of_map_exact _ (restr_exact hex R S φ)`.
-/
theorem restr_preservesHomology (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (R S : Type) [CommRing R] [CommRing S]
    (φ : R →+* S) : (restr φ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (restr_exact hex R S φ)

/- English proof (translation)
Rewrite using `[HomologicalComplex.singleMapHomologicalComplex_inv_app_self]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem single_key (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F).f 0 =
    (restr φ).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp
  rfl

/- English proof (translation)
Introduce `R S _ _ φ F`. Use `haveI := restr_preservesHomology hex R S φ`. Set `M` to `(restr φ).mapHomologicalComplex (ComplexShape.up ℤ)`. Set `T : Cx R` to `M.obj (res S F)`. Set `σ : SemiMap (res S F) T` to `{ app := fun U s => AddMonoidHom.mk' (fun a => (show Sec (T.X s) U from a)) (fun _ _ => rfl) nat := fun _ _ _ => rfl comm := fun _ _ _ _ => rfl }`.

Use `haveI : QuasiIso (resAug F) := (hres S F).2.2.2.1`. Establish `hq2 : QuasiIso (M.map (resAug F))` using `HomologicalComplex.quasiIso_map_of_preservesHomology (resAug F) (restr φ)`. Set `e` to `(HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F`. Establish `hq1 : QuasiIso e` using `@quasiIso_of_isIso _ _ _ _ _ _ _ e inferInstance (fun _ => inferInstance) (fun _ => inferInstance)`. Set `ε : sgl ((restr φ).obj F) ⟶ T` to `e ≫ M.map (resAug F)`.

Use `⟨T, σ, ε, ?_, fun U s => Function.bijective_id, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact quasiIso_comp (hφ := hq1) (hφ' := hq2)`. Consider the case `exact @quasiIso_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq1 hq2`. Introduce `U a`.

Establish `h2 : Sec.map (e.f 0) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv (show Sec ((restr φ).obj F) U from a)) = Sec.map ((restr φ).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv) (show Sec ((restr φ).obj F) U from a)` using `congrArg (fun f => Sec.map f (show Sec ((restr φ).obj F) U from a)) (single_key R S φ F)`. Express the relevant statement in the definitionally equal form `Sec.map ((restr φ).map ((resAug F).f 0)) (Sec.map (e.f 0) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv (show Sec ((restr φ).obj F) U from a))) = _`. Rewrite using `[h2]`. Both sides reduce to the same expression.
-/
theorem RestrRes_of (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) :
    LateralTheory.KummerTheory.BockCut.RestrRes := by
  intro R S _ _ φ F
  haveI := restr_preservesHomology hex R S φ
  let M := (restr φ).mapHomologicalComplex (ComplexShape.up ℤ)
  let T : Cx R := M.obj (res S F)
  let σ : SemiMap (res S F) T :=
    { app := fun U s => AddMonoidHom.mk' (fun a => (show Sec (T.X s) U from a)) (fun _ _ => rfl)
      nat := fun _ _ _ => rfl
      comm := fun _ _ _ _ => rfl }
  haveI : QuasiIso (resAug F) := (hres S F).2.2.2.1
  have hq2 : QuasiIso (M.map (resAug F)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (resAug F) (restr φ)
  let e := (HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F
  have hq1 : QuasiIso e := @quasiIso_of_isIso _ _ _ _ _ _ _ e inferInstance (fun _ => inferInstance) (fun _ => inferInstance)
  let ε : sgl ((restr φ).obj F) ⟶ T := e ≫ M.map (resAug F)
  refine ⟨T, σ, ε, ?_, fun U s => Function.bijective_id, ?_⟩
  · first
      | exact quasiIso_comp (hφ := hq1) (hφ' := hq2)
      | exact @quasiIso_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq1 hq2
  · intro U a
    have h2 : Sec.map (e.f 0) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv
        (show Sec ((restr φ).obj F) U from a)) =
        Sec.map ((restr φ).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv)
        (show Sec ((restr φ).obj F) U from a) :=
      congrArg (fun f => Sec.map f (show Sec ((restr φ).obj F) U from a)) (single_key R S φ F)
    change Sec.map ((restr φ).map ((resAug F).f 0)) (Sec.map (e.f 0)
      (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv
        (show Sec ((restr φ).obj F) U from a))) = _
    rw [h2]
    rfl

end LateralTheory.KummerTheory.RestrResPf
