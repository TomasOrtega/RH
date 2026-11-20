import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `hdeg : (Polynomial.cyclotomic l (Om l)).degree ≠ 0` using `(Polynomial.degree_cyclotomic_pos l (Om l) hl).ne'`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root _ hdeg`. Use `haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩`. Establish `hζ : IsPrimitiveRoot z l` using `Polynomial.isRoot_cyclotomic_iff.mp hz`.

Establish `hmem : z ∈ Ks K 1`. Use `(le_sup_right : _ ≤ Ks K 1) ?_` and prove the remaining obligations. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `z ^ (l ^ 1) = 1`. Rewrite using `[pow_one]`.

Conclude with `hζ.pow_eq_one`. Establish `hLL : z ∈ LL.1` using `h.2.2.2 (Ks K 1).val ⟨z, hmem⟩`. Establish `hζ' : IsPrimitiveRoot (⟨z, hLL⟩ : ↥LL.1) l` using `IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ Subtype.val_injective`. Establish `hint : IsIntegral ℤ_[l] (⟨z, hLL⟩ : ↥LL.1)` using `IsIntegral.of_pow hl (by rw [hζ'.pow_eq_one]; exact isIntegral_one)`. Conclude with `⟨⟨⟨z, hLL⟩, hint⟩, IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζ' Subtype.val_injective⟩`.
-/
theorem exists_primitiveRoot_coeffRing_of_good {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    (h : Good K 1 LL) : ∃ ζ : ↥(OL LL), IsPrimitiveRoot ζ l := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hdeg : (Polynomial.cyclotomic l (Om l)).degree ≠ 0 :=
    (Polynomial.degree_cyclotomic_pos l (Om l) hl).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩
  have hζ : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hmem : z ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) ?_
    apply IntermediateField.subset_adjoin
    change z ^ (l ^ 1) = 1
    rw [pow_one]
    exact hζ.pow_eq_one
  have hLL : z ∈ LL.1 := h.2.2.2 (Ks K 1).val ⟨z, hmem⟩
  have hζ' : IsPrimitiveRoot (⟨z, hLL⟩ : ↥LL.1) l :=
    IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ Subtype.val_injective
  have hint : IsIntegral ℤ_[l] (⟨z, hLL⟩ : ↥LL.1) :=
    IsIntegral.of_pow hl (by rw [hζ'.pow_eq_one]; exact isIntegral_one)
  exact ⟨⟨⟨z, hLL⟩, hint⟩,
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζ' Subtype.val_injective⟩

end GlobalTheory
