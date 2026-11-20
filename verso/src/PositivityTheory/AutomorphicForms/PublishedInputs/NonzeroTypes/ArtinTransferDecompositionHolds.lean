import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

/- English proof (translation)
Unfold `ArtinTransferDecompositionCharacter`. Introduce `E Ω _ _ _ _ _ A w h a ha n χ hχ`. Establish `hs : ∀ i, GlobalTheory.WeilDeligne.IsSmooth ((χ i).comp (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h)))`. Introduce `i`. Establish `hc : Continuous fun σ : ReciprocityTheory.Gal.Ine A => Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)` using `continuous_subtype_val.subtype_mk _`.

Conclude with `(hχ i).preimage hc`. Use `choose μ hμ hμe using fun i => ha.factor _ (hs i)`. Conclude with `⟨μ, hμ, fun i σ => DFunLike.congr_fun (hμe i) σ⟩`.
-/
theorem artinTransferDecomposition_holds : ArtinTransferDecompositionCharacter := by
  unfold ArtinTransferDecompositionCharacter
  intro E Ω _ _ _ _ _ A w h a ha n χ hχ
  have hs : ∀ i, GlobalTheory.WeilDeligne.IsSmooth ((χ i).comp (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h))) := by
    intro i
    have hc : Continuous fun σ : ReciprocityTheory.Gal.Ine A =>
        Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ) :=
      continuous_subtype_val.subtype_mk _
    exact (hχ i).preimage hc
  choose μ hμ hμe using fun i => ha.factor _ (hs i)
  exact ⟨μ, hμ, fun i σ => DFunLike.congr_fun (hμe i) σ⟩

end UpperTheory.NonzeroTypeTheory
