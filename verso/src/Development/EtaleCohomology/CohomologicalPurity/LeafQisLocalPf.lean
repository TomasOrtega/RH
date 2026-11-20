import Development.EtaleCohomology.CohomologicalPurity.LeafLocCutAug

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.QisLocalPf

variable (R : Type) [CommRing R]

abbrev Fsh := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))

instance wlb : Scheme.etaleTopology.{0}.WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

instance ph : (Fsh R).PreservesHomology := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

/- English proof (translation)
Unfold `chainsN TubeCut.chainsP`. Rewrite using `[Functor.assoc, AlgebraicTopology.map_alternatingFaceMapComplex]`. Both sides reduce to the same expression.
-/
theorem chainsN_eq : chainsN R = TubeCut.chainsP R ⋙ (Fsh R).mapHomologicalComplex _ := by
  unfold chainsN TubeCut.chainsP
  rw [Functor.assoc, AlgebraicTopology.map_alternatingFaceMapComplex]
  rfl

/- English proof (translation)
Conclude with `(GrothendieckTopology.W_iff _ g).1 ((GrothendieckTopology.W_iff_isLocallyBijective _ g).2 ⟨hi, hs⟩)`.
-/
theorem isIso_F_map {P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (g : P ⟶ Q)
    (hi : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} g)
    (hs : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} g) : IsIso ((Fsh R).map g) := by
  exact (GrothendieckTopology.W_iff _ g).1 ((GrothendieckTopology.W_iff_isLocallyBijective _ g).2 ⟨hi, hs⟩)

/- English proof (translation)
Establish `e` using `ShortComplex.mapHomologyIso_hom_naturality φ F`. Rewrite using `[(Iso.eq_comp_inv _).2 e]`. Use `infer_instance`.
-/
theorem sc_iso {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [IsIso (F.map (ShortComplex.homologyMap φ))] :
    IsIso (@ShortComplex.homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _) := by
  have e := ShortComplex.mapHomologyIso_hom_naturality φ F
  rw [(Iso.eq_comp_inv _).2 e]
  infer_instance

/- English proof (translation)
Establish `key : ∀ {K L : ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ} (φ : K ⟶ L), (∀ n, IsIso ((Fsh R).map (HomologicalComplex.homologyMap φ n))) → QuasiIso (((Fsh R).mapHomologicalComplex _).map φ)`. Introduce `K L φ h`. Rewrite using `[quasiIso_iff]`. Introduce `n`. Rewrite using `[quasiIsoAt_iff, ShortComplex.quasiIso_iff]`.

Establish `e` using `ShortComplex.mapHomologyIso_hom_naturality ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (Fsh R)`. Establish `: IsIso ((Fsh R).map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)))` using `h n`. Conclude with `sc_iso (Fsh R) ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)`. Establish `hf` using `key ((TubeCut.chainsP R).map f) (fun n => isIso_F_map R _ (hi n) (hs n))`. Rewrite using `[chainsN_eq]`.

Conclude with `hf`.
-/
theorem quasiIso_chainsN {E E' : Spc} (f : E ⟶ E')
    (hi : ∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n))
    (hs : ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n)) :
    QuasiIso ((chainsN R).map f) := by
  have key : ∀ {K L : ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ} (φ : K ⟶ L),
      (∀ n, IsIso ((Fsh R).map (HomologicalComplex.homologyMap φ n))) →
      QuasiIso (((Fsh R).mapHomologicalComplex _).map φ) := by
    intro K L φ h
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
    have e := ShortComplex.mapHomologyIso_hom_naturality ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (Fsh R)
    have : IsIso ((Fsh R).map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))) := h n
    exact sc_iso (Fsh R) ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)
  have hf := key ((TubeCut.chainsP R).map f) (fun n => isIso_F_map R _ (hi n) (hs n))
  rw [chainsN_eq]
  exact hf

/- English proof (translation)
Introduce `R _ E E' f hi hs`. Establish `h` using `quasiIso_chainsN R f hi hs`. Use `show QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)`. Conclude with `(HomologicalComplex.quasiIso_extendMap_iff _ _).2 h`.
-/
theorem LeafQisLocal_of : TubeCut.LeafQisLocal := by
  intro R _ E E' f hi hs
  have h := quasiIso_chainsN R f hi hs
  show QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h

end LateralTheory.CohomologicalPurity.QisLocalPf
