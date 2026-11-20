import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GrPolys

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem monic_deg_equiv_card (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} = g ^ n ∧
      Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := by
  have e : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} ≃ (Fin n → ZMod g) :=
    (monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · haveI : Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := Finite.of_equiv _ e.symm
    exact Set.toFinite _

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem zero_part_eq (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) :
    {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0} =
      (fun h => X * h) '' {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n - 1} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hm, hd, h0⟩
    obtain ⟨h, rfl⟩ := X_dvd_iff.mpr h0
    have hmh : h.Monic := Monic.of_mul_monic_left monic_X hm
    refine ⟨h, ⟨hmh, ?_⟩, rfl⟩
    rw [natDegree_X_mul hmh.ne_zero] at hd
    omega
  · rintro ⟨h, ⟨hm, hd⟩, rfl⟩
    refine ⟨monic_X.mul hm, ?_, ?_⟩
    · rw [natDegree_X_mul hm.ne_zero]; omega
    · simp [mul_coeff_zero]

end GlobalTheory.GrPolys

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

The claim follows by propositional logic. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero :
    ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} = g ^ n - g ^ (n - 1) ∧ Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} := by
  intro g _ n hn
  obtain ⟨hcS, hfS⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g n
  obtain ⟨hcT, hfT⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g (n - 1)
  set S := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n}
  set A := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}
  set B := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0}
  have hAS : A ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hBS : B ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hfA : A.Finite := hfS.subset hAS
  have hfB : B.Finite := hfS.subset hBS
  have hU : A ∪ B = S := by
    ext f
    simp only [A, B, S, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hD : Disjoint A B := by
    rw [Set.disjoint_left]
    intro f hA hB
    exact hA.2.2 hB.2.2
  have hB : B.ncard = g ^ (n - 1) := by
    rw [show B = _ from GlobalTheory.GrPolys.zero_part_eq g n hn, Set.ncard_image_of_injective _
      (fun a b h => mul_left_cancel₀ X_ne_zero h), hcT]
  have := Set.ncard_union_eq hD hfA hfB
  rw [hU, hcS, hB] at this
  exact ⟨by omega, hfA⟩
