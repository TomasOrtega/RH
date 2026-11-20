import Formalism.WachLatticeTwists.RamifiedBlockRings.LemmaFiveThreeAnyResidueField
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.AbsIrrOfSpan
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.SpanSingle
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.BigRes

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

/- English proof (translation)
Establish `hg : (IsFractionRing.lift hf : FractionRing O →+* F).comp (algebraMap O (FractionRing O)) = f`. Use extensionality with `y`. Conclude with `IsFractionRing.lift_algebraMap hf y`. Rewrite using `[← hg, ← Polynomial.map_map]`. Conclude with `h.map _`.
-/
theorem split_ext {O : Type} [CommRing O] [IsDomain O] {F : Type} [Field F] (f : O →+* F)
    (hf : Function.Injective f) (P : Polynomial O)
    (h : (P.map (algebraMap O (FractionRing O))).Splits) : (P.map f).Splits := by
  have hg : (IsFractionRing.lift hf : FractionRing O →+* F).comp (algebraMap O (FractionRing O)) = f := by
    ext y
    exact IsFractionRing.lift_algebraMap hf y
  rw [← hg, ← Polynomial.map_map]
  exact h.map _

/- English proof (translation)
Use `⟨fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨α, hα, he⟩` from `h.2.2.2.2 x`. Rewrite using `[he]`. Conclude with `Polynomial.separable_prod_X_sub_C_iff.2 hα`. Take `⟨α, hα, he⟩` from `h.2.2.2.2 x`.

Establish `hinj : Function.Injective ((algebraMap O' (FractionRing O')).comp (algebraMap O O'))`. Rewrite using `[RingHom.coe_comp]`. Conclude with `(IsFractionRing.injective O' (FractionRing O')).comp (FaithfulSMul.algebraMap_injective O O')`. Apply `split_ext ((algebraMap O' (FractionRing O')).comp (algebraMap O O')) hinj` to reduce the goal to its premises. Rewrite using `[blockPoly_map, he]`.

Use `first`. Consider the case `exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _`. Consider the case `exact Polynomial.splits_prod_X_sub_C _`. Consider the case `simp`.
-/
theorem blockPoly_separable_splits {O : Type} (O' : Type) [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O']
    [Algebra O O'] [FaithfulSMul O O'] {X : Type} {T : Subalgebra O (X → O)} {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Group G] {r : G →* (X → Matrix d d O)} {π : X} {t : ℕ} {g₀ : G}
    {eB s : X → Matrix d d O} (h : DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s) :
    (∀ x, (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
      ((eB x * r g₀ x * eB x + s x).map (algebraMap O (FractionRing O)))).Separable) ∧
    (∀ x, ((blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).map
      ((algebraMap O' (FractionRing O')).comp (algebraMap O O'))).Splits) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨α, hα, he⟩ := h.2.2.2.2 x
    rw [he]
    exact Polynomial.separable_prod_X_sub_C_iff.2 hα
  · obtain ⟨α, hα, he⟩ := h.2.2.2.2 x
    have hinj : Function.Injective ((algebraMap O' (FractionRing O')).comp (algebraMap O O')) := by
      rw [RingHom.coe_comp]
      exact (IsFractionRing.injective O' (FractionRing O')).comp
        (FaithfulSMul.algebraMap_injective O O')
    apply split_ext ((algebraMap O' (FractionRing O')).comp (algebraMap O O')) hinj
    rw [blockPoly_map, he]
    first
      | exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
      | exact Polynomial.splits_prod_X_sub_C _
      | simp

/- English proof (translation)
Introduce `O _ _ _ X _ d G _ _ _ t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD _ _ Z NN _ _ g n hn hφ O' _ _ _ _ _ _ e he hk`. Take `⟨hsep, hspl⟩` from `blockPoly_separable_splits O' hX`. Take `⟨cP, cA, cI, cX, cv⟩` from `stageC O O' e he X T d G r π t bl χ₁ ε hP hA eB e₁ hI g₀ s hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1 hsep hspl`. Take `⟨D', hD', ⟨i1, i2, i3, i4, i5⟩, i3', hT⟩` from `ring_objects_exist O' X (bcT O' T) d G (bcR O' r) π t ht bl _ _ cP cA _ _ cI g₀ _ cX`. Take `⟨NN', _, _, n', hn', hφ', hlen⟩` from `hM O O' e he X d G t bl T r π χ₁ ε g₀ eB e₁ s hX D D' hD hD' NN g n hn`.

Establish `hpπ : D'.p D'.π' = π`. Take `⟨-, -, -, -, h, -⟩` from `hD'`. Conclude with `h`. Establish `h1` using `lemma_five_three_holds O' X d G t ht bl (bcT O' T) D' hT Z NN' g n' hn' (hφ' Z hφ) hk`. Rewrite `h1` using `[hpπ, cv Z]`.

Simplify using `only [hlen] at h1`. Rewrite `h1` using `[← Finset.mul_sum]`. Establish `he0 : (e : ℕ∞) ≠ 0`. Introduce `h0`. Establish `h2` using `he 0`.

Rewrite `h2` using `[map_zero, h0, zero_mul]`. Simplify using `at h2`. Conclude with `(ENat.mul_le_mul_left_iff he0 (ENat.natCast_ne_top e)).mp h1`.
-/
theorem lemma_five_three_extension_of_module (hM : StatModuleBc) : LemmaFiveThreeOverExtension := by
  intro O _ _ _ X _ d G _ _ _ t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD _ _ Z NN _ _ g n hn hφ
    O' _ _ _ _ _ _ e he hk
  obtain ⟨hsep, hspl⟩ := blockPoly_separable_splits O' hX
  obtain ⟨cP, cA, cI, cX, cv⟩ := stageC O O' e he X T d G r π t bl χ₁ ε hP hA eB e₁ hI g₀ s hX.1 hX.2.1
    hX.2.2.1 hX.2.2.2.1 hsep hspl
  obtain ⟨D', hD', ⟨i1, i2, i3, i4, i5⟩, i3', hT⟩ := ring_objects_exist O' X (bcT O' T) d G (bcR O' r) π t ht bl _ _
    cP cA _ _ cI g₀ _ cX
  obtain ⟨NN', _, _, n', hn', hφ', hlen⟩ := hM O O' e he X d G t bl T r π χ₁ ε g₀ eB e₁ s hX D D'
    hD hD' NN g n hn
  have hpπ : D'.p D'.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD'
    exact h
  have h1 := lemma_five_three_holds O' X d G t ht bl (bcT O' T) D' hT Z NN' g n' hn' (hφ' Z hφ) hk
  rw [hpπ, cv Z] at h1
  simp only [hlen] at h1
  rw [← Finset.mul_sum] at h1
  have he0 : (e : ℕ∞) ≠ 0 := by
    intro h0
    have h2 := he 0
    rw [map_zero, h0, zero_mul] at h2
    simp at h2
  exact (ENat.mul_le_mul_left_iff he0 (ENat.natCast_ne_top e)).mp h1

/- English proof (translation)
Introduce `O _ _ _ X _ d G _ _ _ t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD _ _ Z NN _ _ g n hn hφ`. Take `⟨O', _, _, _, _, _, _, he, hk⟩` from `hE O (g * Fintype.card d)`. Conclude with `lemma_five_three_extension_of_module hM O X d G t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD Z NN g n hn hφ O' 1 (fun y => by rw [he y, Nat.cast_one, one_mul]) hk`.
-/
theorem any_residue_field_of_module_baseChange_of_big_residue_ext (hM : StatModuleBc) (hE : StatBigResidueExt) : LemmaFiveThreeAnyResidueField := by
  intro O _ _ _ X _ d G _ _ _ t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD _ _ Z NN _ _ g n hn hφ
  obtain ⟨O', _, _, _, _, _, _, he, hk⟩ := hE O (g * Fintype.card d)
  exact lemma_five_three_extension_of_module hM O X d G t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD Z NN g n hn hφ O' 1
    (fun y => by rw [he y, Nat.cast_one, one_mul]) hk

/- English proof (translation)
The claim follows from `lemma_five_three_extension_of_module moduleBc`.
-/
theorem lemma_five_three_over_extension : LemmaFiveThreeOverExtension := lemma_five_three_extension_of_module moduleBc

/- English proof (translation)
The claim follows from `any_residue_field_of_module_baseChange_of_big_residue_ext moduleBc bigResidueExt`.
-/
theorem lemma_five_three_any_residue_field : LemmaFiveThreeAnyResidueField := any_residue_field_of_module_baseChange_of_big_residue_ext moduleBc bigResidueExt

end Formalism.RepresentationBoundsCohomology.ringDataObjects
