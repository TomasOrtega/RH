import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ h4 y hy`. Use `set K := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} with hK`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l`. Establish `hchar : ringChar (ZMod l) ≠ 2` using `by rw [ZMod.ringChar_zmod_n]; omega`. Establish `hm1 : quadraticChar (ZMod l) (-1) = -1`.

Rewrite using `[quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]`. Use `set χ := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom (Om l)) with hχdef`. Establish `hχm1 : χ (-1) = -1`. Simplify using `[χ, MulChar.ringHomComp_apply, hm1]`. Establish `h2 : (2 : Om l) ≠ 0` using `two_ne_zero`.

Establish `hχ1 : χ ≠ 1`. Introduce `h`. Rewrite `hχm1` using `[h, MulChar.one_apply (isUnit_one.neg)]`. Apply `h2` to reduce the goal to its premises. Take the linear combination `hχm1`.

Establish `hq : χ.IsQuadratic` using `(quadraticChar_isQuadratic (ZMod l)).comp _`. Establish `hψ` using `AddChar.zmodChar_primitive_of_primitive_root l hζ`. Establish `hsq` using `gaussSum_sq hχ1 hq hψ`. Rewrite `hsq` using `[hχm1, ZMod.card]`. Use `set g := gaussSum χ (AddChar.zmodChar l hζ.pow_eq_one) with hg`.

Establish `hgK : g ∈ K`. Rewrite using `[hg, gaussSum]`. Use `sum_mem fun a _ => mul_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[hχdef, MulChar.ringHomComp_apply]`. Conclude with `intCast_mem K _`.

Rewrite using `[AddChar.zmodChar_apply]`. Use `pow_mem (IntermediateField.subset_adjoin _ _ ?_) _` and prove the remaining obligations. Use `show ζ ^ (l ^ 1) = 1`. Rewrite using `[pow_one]`. Conclude with `hζ.pow_eq_one`.

Establish `hyg : (y - g) * (y + g) = 0`. Take the linear combination `hy - hsq`. Break down `mul_eq_zero.1 hyg with h | h` into its components or cases. Rewrite using `[sub_eq_zero.1 h]`. Conclude with `hgK`.

Rewrite using `[eq_neg_of_add_eq_zero_left h]`. Conclude with `neg_mem hgK`.
-/
theorem sqrt_neg_l_mem_adjoin_roots_of_unity :
    ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) →
      y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  intro l _ h4 y hy
  set K := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} with hK
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  set χ := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom (Om l)) with hχdef
  have hχm1 : χ (-1) = -1 := by
    simp [χ, MulChar.ringHomComp_apply, hm1]
  have h2 : (2 : Om l) ≠ 0 := two_ne_zero
  have hχ1 : χ ≠ 1 := by
    intro h
    rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
    apply h2; linear_combination hχm1
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
  have hsq := gaussSum_sq hχ1 hq hψ
  rw [hχm1, ZMod.card] at hsq
  set g := gaussSum χ (AddChar.zmodChar l hζ.pow_eq_one) with hg

  have hgK : g ∈ K := by
    rw [hg, gaussSum]
    refine sum_mem fun a _ => mul_mem ?_ ?_
    · rw [hχdef, MulChar.ringHomComp_apply]
      exact intCast_mem K _
    · rw [AddChar.zmodChar_apply]
      refine pow_mem (IntermediateField.subset_adjoin _ _ ?_) _
      show ζ ^ (l ^ 1) = 1
      rw [pow_one]; exact hζ.pow_eq_one

  have hyg : (y - g) * (y + g) = 0 := by
    linear_combination hy - hsq
  rcases mul_eq_zero.1 hyg with h | h
  · rw [sub_eq_zero.1 h]; exact hgK
  · rw [eq_neg_of_add_eq_zero_left h]; exact neg_mem hgK

end GlobalTheory
