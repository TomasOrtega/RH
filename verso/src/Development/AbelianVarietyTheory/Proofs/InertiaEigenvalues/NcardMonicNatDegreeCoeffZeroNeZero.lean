import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GrPolys

/- English proof (translation)
Establish `e : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} ≃ (Fin n → ZMod g)` using `(monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]`. Use `haveI : Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := Finite.of_equiv _ e.symm`. Conclude with `Set.toFinite _`.
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
Use extensionality with `f`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hm, hd, h0⟩`. Take `⟨h, rfl⟩` from `X_dvd_iff.mpr h0`.

Establish `hmh : h.Monic` using `Monic.of_mul_monic_left monic_X hm`. Use `⟨h, ⟨hmh, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite `hd` using `[natDegree_X_mul hmh.ne_zero]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨h, ⟨hm, hd⟩, rfl⟩`.

Use `⟨monic_X.mul hm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[natDegree_X_mul hm.ne_zero]`. Use linear arithmetic over natural numbers and integers. Simplify using `[mul_coeff_zero]`.
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
Introduce `g _ n hn`. Take `⟨hcS, hfS⟩` from `GlobalTheory.GrPolys.monic_deg_equiv_card g n`. Take `⟨hcT, hfT⟩` from `GlobalTheory.GrPolys.monic_deg_equiv_card g (n - 1)`. Use `set S := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n}`. Use `set A := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}`.

Use `set B := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0}`. Establish `hAS : A ⊆ S` using `fun f hf => ⟨hf.1, hf.2.1⟩`. Establish `hBS : B ⊆ S` using `fun f hf => ⟨hf.1, hf.2.1⟩`. Establish `hfA : A.Finite` using `hfS.subset hAS`. Establish `hfB : B.Finite` using `hfS.subset hBS`.

Establish `hU : A ∪ B = S`. Use extensionality with `f`. Simplify using `only [A, B, S, Set.mem_union, Set.mem_setOf_eq]`. The claim follows by propositional logic. Establish `hD : Disjoint A B`.

Rewrite using `[Set.disjoint_left]`. Introduce `f hA hB`. Conclude with `hA.2.2 hB.2.2`. Establish `hB : B.ncard = g ^ (n - 1)`. Rewrite using `[show B = _ from GlobalTheory.GrPolys.zero_part_eq g n hn, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel₀ X_ne_zero h), hcT]`.

Use `Set.ncard_union_eq hD hfA hfB` as an intermediate fact. Rewrite `this` using `[hU, hcS, hB]`. Conclude with `⟨by omega, hfA⟩`.
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
