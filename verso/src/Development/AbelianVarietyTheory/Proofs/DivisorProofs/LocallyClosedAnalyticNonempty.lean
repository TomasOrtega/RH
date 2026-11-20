import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbKer

/- English proof (translation)
Introduce `R _ G _ _ hG N hN`. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Use `set f : G.left ⟶ G.left := ((𝟙 G) ^ N : G ⟶ G).left with hf`.

Use `set e : Sp R ⟶ G.left := η[G].left with he`. Establish `hfw : f ≫ G.hom = G.hom` using `Over.w _`. Establish `hew : e ≫ G.hom = 𝟙 _` using `Over.w η[G]`. Establish `hπ : pullback.fst f e ≫ G.hom = pullback.snd f e`. Rewrite using `[← hfw, ← Category.assoc, pullback.condition, Category.assoc, hew, Category.comp_id]`.

Take `⟨hfl, hqf⟩` from `GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG N hN`. Establish `: LocallyOfFinitePresentation (f ≫ G.hom)` using `by rw [hfw]; infer_instance`. Establish `: LocallyOfFinitePresentation f` using `GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp f G.hom`. Establish `: QuasiCompact (f ≫ G.hom)` using `by rw [hfw]; infer_instance`. Establish `: QuasiCompact f` using `QuasiCompact.of_comp f G.hom`.

Establish `: IsSeparated (f ≫ G.hom)` using `by rw [hfw]; infer_instance`. Establish `: IsSeparated f` using `IsSeparated.of_comp f G.hom`. Establish `: Flat f` using `hfl`. Establish `: LocallyQuasiFinite f` using `hqf`. Rewrite using `[hπ]`.

Use `⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, inferInstance⟩` and prove the remaining obligations. Use `infer_instance`.
-/
theorem kernel_props : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 →
    IsSeparated (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      LocallyOfFinitePresentation (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      QuasiCompact (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      QuasiSeparated (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      LocallyQuasiFinite (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      Flat (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) := by
  intro R _ G _ _ hG N hN
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  set f : G.left ⟶ G.left := ((𝟙 G) ^ N : G ⟶ G).left with hf
  set e : Sp R ⟶ G.left := η[G].left with he
  have hfw : f ≫ G.hom = G.hom := Over.w _
  have hew : e ≫ G.hom = 𝟙 _ := Over.w η[G]
  have hπ : pullback.fst f e ≫ G.hom = pullback.snd f e := by
    rw [← hfw, ← Category.assoc, pullback.condition, Category.assoc, hew, Category.comp_id]
  obtain ⟨hfl, hqf⟩ := GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG N hN
  have : LocallyOfFinitePresentation (f ≫ G.hom) := by rw [hfw]; infer_instance
  have : LocallyOfFinitePresentation f := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp f G.hom
  have : QuasiCompact (f ≫ G.hom) := by rw [hfw]; infer_instance
  have : QuasiCompact f := QuasiCompact.of_comp f G.hom
  have : IsSeparated (f ≫ G.hom) := by rw [hfw]; infer_instance
  have : IsSeparated f := IsSeparated.of_comp f G.hom
  have : Flat f := hfl
  have : LocallyQuasiFinite f := hqf
  rw [hπ]
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, inferInstance⟩
  infer_instance

end GlobalTheory.SemiAbKer
