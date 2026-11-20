import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

/- English proof (translation)
Distinguish the cases in `hb : b ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)`. Conclude with `⟨1, iff_of_true rfl hb⟩`. Assume the negation of the conclusion as `hne`. Establish `hall : ∀ g : Gal(AlgebraicClosure v.Completion/v.Completion), g = 1` using `fun g =>`. Assume the negation of the conclusion as `fun hg => hne ⟨g, iff_of_false hg hb⟩`.

Establish `hcard : Nat.card Gal(AlgebraicClosure v.Completion/v.Completion) = 1` using `Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => (hall a).trans (hall c).symm⟩, ⟨1⟩⟩`. Rewrite `hcard` using `[IsGalois.card_aut_eq_finrank]`. Conclude with `hb ⟨algebraMap v.Completion _ b, by rw [Algebra.norm_algebraMap, hcard, pow_one]⟩`.
-/
theorem exists_eq_one_iff_mem_range_norm (v : InfinitePlace K.1) (b : v.Completion) :
    ∃ g : Gal(AlgebraicClosure v.Completion/v.Completion),
      (g = 1 ↔ b ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)) := by
  by_cases hb : b ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)
  · exact ⟨1, iff_of_true rfl hb⟩
  · by_contra hne
    have hall : ∀ g : Gal(AlgebraicClosure v.Completion/v.Completion), g = 1 := fun g =>
      by_contra fun hg => hne ⟨g, iff_of_false hg hb⟩
    have hcard : Nat.card Gal(AlgebraicClosure v.Completion/v.Completion) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => (hall a).trans (hall c).symm⟩, ⟨1⟩⟩
    rw [IsGalois.card_aut_eq_finrank] at hcard
    exact hb ⟨algebraMap v.Completion _ b, by rw [Algebra.norm_algebraMap, hcard, pow_one]⟩

variable (ι : LocalEmbeddings K)

def localSymbolAt : Place K.1 → K.1ˣ → K.1.fixingSubgroup
  | .inr v, a => globalDecomp (v.adicCompletion K.1) (ι.fin v)
      ((GroundTheory.LocalField.localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
        (Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* v.adicCompletion K.1) a)).liftNormal
          (AlgebraicClosure (v.adicCompletion K.1)))
  | .inl v, a => globalDecomp v.Completion (ι.inf v)
      (exists_eq_one_iff_mem_range_norm v (algebraMap K.1 v.Completion (a : K.1))).choose

/- English proof (translation)
The claim follows from `| .inr v => placeInv_brauerLocal_globalCupClass_inr ι v χ a _ fun y hy => (AlgEquiv.liftNormal_commutes _ _ (⟨y, hy⟩ : GroundTheory.LocalField.maximalAbelianExtension (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))) | .inl v => placeInv_brauerLocal_globalCupClas …`.
-/
theorem placeInv_brauerLocal_globalCupClass (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) :
    ∀ v : Place K.1, placeInv v (brauerLocal ι (globalCupClass χ a) v) =
      χ (Additive.ofMul (localSymbolAt ι v a))
  | .inr v => placeInv_brauerLocal_globalCupClass_inr ι v χ a _ fun y hy =>
      (AlgEquiv.liftNormal_commutes _ _ (⟨y, hy⟩ : GroundTheory.LocalField.maximalAbelianExtension
        (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))))
  | .inl v => placeInv_brauerLocal_globalCupClass_inl ι v χ a _
      (exists_eq_one_iff_mem_range_norm v (algebraMap K.1 v.Completion (a : K.1))).choose_spec

/- English proof (translation)
Use `((brauerLocal ι (globalCupClass χ a)).support.finite_toSet).subset fun v hv => ?_` and prove the remaining obligations. Rewrite `hv` using `[Function.mem_support, ← placeInv_brauerLocal_globalCupClass]`. Rewrite using `[Finset.mem_coe, DFinsupp.mem_support_iff]`. Introduce `h`. Conclude with `hv (by rw [h, map_zero])`.
-/
theorem finite_support_char_localSymbolAt (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) :
    (Function.support fun v : Place K.1 => χ (Additive.ofMul (localSymbolAt ι v a))).Finite := by
  classical
  refine ((brauerLocal ι (globalCupClass χ a)).support.finite_toSet).subset fun v hv => ?_
  rw [Function.mem_support, ← placeInv_brauerLocal_globalCupClass] at hv
  rw [Finset.mem_coe, DFinsupp.mem_support_iff]
  intro h
  exact hv (by rw [h, map_zero])

/- English proof (translation)
Use `set x := brauerLocal ι (globalCupClass χ a) with hx`. Establish `hsum : brauerSumInv ι (globalCupClass χ a) = ∑ v ∈ x.support, placeInv v (x v)`. Express the relevant statement in the definitionally equal form `sumPlaceInv K x = _`. Use `conv_lhs => rw [← DFinsupp.sum_single (f := x)]`. Rewrite using `[DFinsupp.sum, map_sum]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Conclude with `sumPlaceInv_of v (x v)`. Rewrite using `[hsum, finsum_eq_sum_of_support_subset _ (s := x.support) ?_]`. Conclude with `Finset.sum_congr rfl fun v _ => placeInv_brauerLocal_globalCupClass ι χ a v`. Introduce `v hv`.

Rewrite `hv` using `[Function.mem_support, ← placeInv_brauerLocal_globalCupClass]`. Rewrite using `[Finset.mem_coe, DFinsupp.mem_support_iff]`. Introduce `h`. Conclude with `hv (by rw [h, map_zero])`.
-/
theorem brauerSumInv_globalCupClass (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) :
    brauerSumInv ι (globalCupClass χ a) = ∑ᶠ v : Place K.1, χ (Additive.ofMul (localSymbolAt ι v a)) := by
  classical
  set x := brauerLocal ι (globalCupClass χ a) with hx
  have hsum : brauerSumInv ι (globalCupClass χ a) = ∑ v ∈ x.support, placeInv v (x v) := by
    change sumPlaceInv K x = _
    conv_lhs => rw [← DFinsupp.sum_single (f := x)]
    rw [DFinsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact sumPlaceInv_of v (x v)
  rw [hsum, finsum_eq_sum_of_support_subset _ (s := x.support) ?_]
  · exact Finset.sum_congr rfl fun v _ => placeInv_brauerLocal_globalCupClass ι χ a v
  · intro v hv
    rw [Function.mem_support, ← placeInv_brauerLocal_globalCupClass] at hv
    rw [Finset.mem_coe, DFinsupp.mem_support_iff]
    intro h
    exact hv (by rw [h, map_zero])

end

end GroundTheory.ProfCoh
