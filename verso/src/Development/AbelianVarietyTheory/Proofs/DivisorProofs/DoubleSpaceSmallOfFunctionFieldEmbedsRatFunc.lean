import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFuncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegFunctionFieldEq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.SmallPf

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Z)) isOpen_univ`. Establish `hU : IsAffineOpen U` using `hU`. Take `⟨d, h₁, -⟩` from `GlobalTheory.OpenDim.ringKrullDim_affineOpen F f hU ⟨_, hxU⟩`. Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.OpenDim.topologicalKrullDim_open F f U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]`.

Conclude with `topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec`.
-/
theorem exists_dim (F : Type) [Field F] {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ Sp F) [LocallyOfFiniteType f] :
    ∃ d : ℕ, topologicalKrullDim Z = d := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨d, h₁, -⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen F f hU ⟨_, hxU⟩
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F f U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

/- English proof (translation)
Introduce `F _ Y W j hj`. Establish `hp` using `W.proj`. Establish `hlft : LocallyOfFiniteType (W.p₁ ≫ Y.str)`. Take `⟨N, i, hi, hcomp⟩` from `hp`. Use `haveI : IsProper (PSpace.str F N) := isProper_str F N`.

Rewrite using `[← hcomp]`. Use `infer_instance`. Take `⟨d, hd⟩` from `exists_dim F (W.p₁ ≫ Y.str)`. Establish `hY : Y.X.fromSpecStalk (genericPoint Y.X) ≫ Y.str = spMap (algebraMap F Y.Fn)` using `(ratOf Y).pt_s`. Establish `hZ : W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ ≫ Y.str = spMap (W.α₁.comp (algebraMap F Y.Fn))`.

Establish `h1 : spMap W.α₁ ≫ Y.X.fromSpecStalk (genericPoint Y.X) = W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁` using `specMap_functionFieldMap W.p₁`. Rewrite using `[← Category.assoc, ← h1, Category.assoc, hY]`. Conclude with `(Spec.map_comp (CommRingCat.ofHom (algebraMap F Y.Fn)) (CommRingCat.ofHom W.α₁)).symm`. Establish `t₁` using `GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq _ hY`. Establish `t₂` using `GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F W.Z _ d W.proj hd _ hZ`.

Establish `t₃` using `@GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc F Y.Fn W.Z.functionField _ _ _ (algebraMap F Y.Fn).toAlgebra (W.α₁.comp (algebraMap F Y.Fn)).toAlgebra W.α₁ j Y.dim rfl hj t₁`. Rewrite `t₃` using `[t₂]`. Establish `: d ≤ Y.dim + 1` using `by exact_mod_cast t₃`. Unfold `Dbl.Small`. Rewrite using `[hd]`.

Conclude with `this` after adjusting the coercions.
-/
theorem main : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  intro F _ Y W j hj
  have hp := W.proj
  have hlft : LocallyOfFiniteType (W.p₁ ≫ Y.str) := by
    obtain ⟨N, i, hi, hcomp⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    rw [← hcomp]; infer_instance
  obtain ⟨d, hd⟩ := exists_dim F (W.p₁ ≫ Y.str)
  have hY : Y.X.fromSpecStalk (genericPoint Y.X) ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have hZ : W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ ≫ Y.str = spMap (W.α₁.comp (algebraMap F Y.Fn)) := by
    have h1 : spMap W.α₁ ≫ Y.X.fromSpecStalk (genericPoint Y.X) = W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ :=
      specMap_functionFieldMap W.p₁
    rw [← Category.assoc, ← h1, Category.assoc, hY]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap F Y.Fn)) (CommRingCat.ofHom W.α₁)).symm
  have t₁ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq _ hY
  have t₂ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F W.Z _ d W.proj hd _ hZ
  have t₃ := @GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc F Y.Fn W.Z.functionField _ _ _ (algebraMap F Y.Fn).toAlgebra
    (W.α₁.comp (algebraMap F Y.Fn)).toAlgebra W.α₁ j Y.dim rfl hj t₁
  rw [t₂] at t₃
  have : d ≤ Y.dim + 1 := by exact_mod_cast t₃
  unfold Dbl.Small
  rw [hd]
  exact_mod_cast this

end GlobalTheory.FlagPush.SmallPf
