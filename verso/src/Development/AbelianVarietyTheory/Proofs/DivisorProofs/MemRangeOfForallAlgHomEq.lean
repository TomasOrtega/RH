import Mathlib
open scoped TensorProduct

namespace GlobalTheory

open Polynomial in

/- English proof (translation)
Introduce `F K₀ _ _ _ _ halg t ht`. Establish `hint : IsIntegral F t` using `(Algebra.IsAlgebraic.isAlgebraic t).isIntegral`. Use `set Ω := AlgebraicClosure K₀`. Establish `hsep : (minpoly F t).Separable` using `(minpoly.irreducible hint).separable`. Establish `hsplit : Splits ((minpoly F t).map (algebraMap F Ω))` using `IsAlgClosed.splits _`.

Establish `hcard` using `card_rootSet_eq_natDegree (K := Ω) hsep hsplit`. Assume the negation of the conclusion as `hnot`. Establish `h1 : (minpoly F t).natDegree ≠ 1` using `fun h => by`. Take `⟨c, hc⟩` from `minpoly.natDegree_eq_one_iff.mp h`. Conclude with `hnot ⟨c, hc⟩`.

Establish `hpos` using `minpoly.natDegree_pos hint`. Establish `hlt : 1 < Fintype.card ((minpoly F t).rootSet Ω)` using `by omega`. Take `⟨a, b, hab⟩` from `Fintype.exists_pair_of_one_lt_card hlt`. Establish `hK' : ∀ s : K₀, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F Ω))` using `fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩`. Establish `ha : aeval (a : Ω) (minpoly F t) = 0` using `(mem_rootSet.mp a.2).2`.

Establish `hb : aeval (b : Ω) (minpoly F t) = 0` using `(mem_rootSet.mp b.2).2`. Take `⟨φa, hφa⟩` from `IntermediateField.exists_algHom_of_splits_of_aeval hK' ha`. Take `⟨φb, hφb⟩` from `IntermediateField.exists_algHom_of_splits_of_aeval hK' hb`. Apply `hab` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hφa, ← hφb]`. Conclude with `ht Ω φa φb`.
-/
theorem mem_range_of_forall_algHom_eq :
    ∀ (F K₀ : Type) [Field F] [CharZero F] [Field K₀] [Algebra F K₀], Algebra.IsAlgebraic F K₀ →
      ∀ t : K₀, (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (φ₁ φ₂ : K₀ →ₐ[F] Ω), φ₁ t = φ₂ t) →
        t ∈ Set.range (algebraMap F K₀) := by
  intro F K₀ _ _ _ _ halg t ht
  classical
  have hint : IsIntegral F t := (Algebra.IsAlgebraic.isAlgebraic t).isIntegral
  set Ω := AlgebraicClosure K₀
  have hsep : (minpoly F t).Separable := (minpoly.irreducible hint).separable
  have hsplit : Splits ((minpoly F t).map (algebraMap F Ω)) := IsAlgClosed.splits _
  have hcard := card_rootSet_eq_natDegree (K := Ω) hsep hsplit
  by_contra hnot
  have h1 : (minpoly F t).natDegree ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h
    exact hnot ⟨c, hc⟩
  have hpos := minpoly.natDegree_pos hint
  have hlt : 1 < Fintype.card ((minpoly F t).rootSet Ω) := by omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hlt
  have hK' : ∀ s : K₀, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F Ω)) :=
    fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩
  have ha : aeval (a : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp a.2).2
  have hb : aeval (b : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp b.2).2
  obtain ⟨φa, hφa⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' ha
  obtain ⟨φb, hφb⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' hb
  apply hab
  apply Subtype.ext
  rw [← hφa, ← hφb]
  exact ht Ω φa φb

end GlobalTheory
