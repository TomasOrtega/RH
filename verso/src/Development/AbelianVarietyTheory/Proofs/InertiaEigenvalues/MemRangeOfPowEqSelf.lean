import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading

open Polynomial

namespace GlobalTheory.RangeOfPowerFixed

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Simplify using `only [not_exists] at hne`. Establish `hg : 1 < g` using `(Fact.out : Nat.Prime g).one_lt`. Use `set P : K[X] := X ^ g - X with hPeq`. Establish `hP0 : P ≠ 0` using `FiniteField.X_pow_card_sub_X_ne_zero K hg`.

Establish `hdeg : P.natDegree = g` using `FiniteField.X_pow_card_sub_X_natDegree_eq K hg`. Establish `hroot : ∀ x : K, x ^ g = x → x ∈ P.roots.toFinset`. Introduce `x hx`. Rewrite using `[Multiset.mem_toFinset, mem_roots hP0, hPeq]`. Simplify using `[hx]`.

Use `set S : Finset K := insert z (Finset.univ.image (algebraMap (ZMod g) K)) with hSeq`. Establish `hzS : z ∉ Finset.univ.image (algebraMap (ZMod g) K)`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]`. Conclude with `hne`. Establish `hcard : S.card = g + 1`.

Rewrite using `[hSeq, Finset.card_insert_of_notMem hzS, Finset.card_image_of_injective _ (algebraMap (ZMod g) K).injective, Finset.card_univ, ZMod.card]`. Establish `hsub : S ⊆ P.roots.toFinset`. Introduce `x hx`. Rewrite `hx` using `[hSeq, Finset.mem_insert, Finset.mem_image]`. Break down `hx with rfl | ⟨c, -, rfl⟩` into its components or cases.

Conclude with `hroot _ hz`. Conclude with `hroot _ (by rw [← map_pow, ZMod.pow_card])`. Use `(Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_roots' P))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_range_of_pow_eq_self {g : ℕ} [Fact (Nat.Prime g)] {K : Type*} [Field K] [Algebra (ZMod g) K]
    (z : K) (hz : z ^ g = z) : ∃ c : ZMod g, algebraMap (ZMod g) K c = z := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  have hg : 1 < g := (Fact.out : Nat.Prime g).one_lt
  set P : K[X] := X ^ g - X with hPeq
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hg
  have hdeg : P.natDegree = g := FiniteField.X_pow_card_sub_X_natDegree_eq K hg

  have hroot : ∀ x : K, x ^ g = x → x ∈ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hP0, hPeq]
    simp [hx]

  set S : Finset K := insert z (Finset.univ.image (algebraMap (ZMod g) K)) with hSeq
  have hzS : z ∉ Finset.univ.image (algebraMap (ZMod g) K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hcard : S.card = g + 1 := by
    rw [hSeq, Finset.card_insert_of_notMem hzS,
      Finset.card_image_of_injective _ (algebraMap (ZMod g) K).injective, Finset.card_univ, ZMod.card]
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [hSeq, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨c, -, rfl⟩
    · exact hroot _ hz
    · exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' P))
  omega

/- English proof (translation)
Introduce `g _ z hz`. Conclude with `mem_range_of_pow_eq_self z hz`.
-/
theorem main : ∀ {g : ℕ} [inst : Fact (Nat.Prime g)] (z : Formalism.CyclotomicNorms.Fbar g), z ^ g = z →
    ∃ (c : ZMod g), (Algebra.algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) : ZMod g → Formalism.CyclotomicNorms.Fbar g) c = z := by
  intro g _ z hz
  exact mem_range_of_pow_eq_self z hz

end GlobalTheory.RangeOfPowerFixed
