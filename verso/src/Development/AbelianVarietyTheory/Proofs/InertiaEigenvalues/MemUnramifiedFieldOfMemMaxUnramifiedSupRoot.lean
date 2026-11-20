import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeMinpolyRootNegPrimeUnramifiedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.KunrDisj

/- English proof (translation)
Introduce `l _ a e _ _ ϖ n x hxK hx`. Establish `hN : 0 < l ^ n * e` using `Nat.mul_pos (pow_pos (Fact.out : l.Prime).pos n) (Nat.pos_of_ne_zero (NeZero.ne e))`. Establish `hπ : ϖ.seq n ^ (l ^ n * e) = -(l : Om l)` using `ϖ.seq_pow_mul n`. Use `set U := Kunr l a with hU`. Use `set π := ϖ.seq n with hπdef`.

Establish `hdeg` using `fun (E : Type) [Field E] [Algebra E (Om l)] (h : ∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) => GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified l (l ^ n * e) π hN hπ E h`. Establish `hint : ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → IsIntegral E π`. Introduce `E _ _ h`. Assume the negation of the conclusion as `hni`. Use `hdeg E h` as an intermediate fact.

Rewrite `this` using `[minpoly.eq_zero hni, Polynomial.natDegree_zero]`. Use linear arithmetic over natural numbers and integers. Set `K2 : IntermediateField U (Om l)` to `IntermediateField.adjoin U {π}`. Establish `hxK2 : x ∈ K2`. Establish `: x ∈ K2.restrictScalars ℚ_[l]`.

Rewrite using `[IntermediateField.restrictScalars_adjoin_eq_sup]`. Conclude with `hx`. Conclude with `this`. Set `K1 : IntermediateField U (Om l)` to `IntermediateField.adjoin U {x}`. Establish `hK1K2 : K1 ≤ K2` using `IntermediateField.adjoin_simple_le_iff.2 hxK2`.

Establish `hUK : ∀ y : U, algebraMap U (Om l) y ∈ MaximalUnramifiedExtension l` using `fun y => Kunr_le_Kur l a y.2`. Establish `hK1K : ∀ y : K1, algebraMap K1 (Om l) y ∈ MaximalUnramifiedExtension l`. Introduce `y`. Establish `hy : (y : Om l) ∈ K1.restrictScalars ℚ_[l]` using `y.2`. Rewrite `hy` using `[IntermediateField.restrictScalars_adjoin]`.

Use `(IntermediateField.adjoin_le_iff.2 ?_) hy` and prove the remaining obligations. Introduce and unpack `z (hz | hz)`. Conclude with `Kunr_le_Kur l a hz`. Rewrite using `[Set.mem_singleton_iff.1 hz]`. Conclude with `hxK`.

Set `L : IntermediateField K1 (Om l)` to `IntermediateField.adjoin K1 {π}`. Establish `hLK2 : L.restrictScalars U = K2`. Rewrite using `[IntermediateField.restrictScalars_adjoin]`. Use `le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)` and prove the remaining obligations. Introduce and unpack `z (hz | hz)`.

Conclude with `hK1K2 hz`. Rewrite using `[Set.mem_singleton_iff.1 hz]`. Conclude with `IntermediateField.mem_adjoin_simple_self U π`. Establish `hK2r : Module.finrank U K2 = l ^ n * e`. Rewrite using `[IntermediateField.adjoin.finrank (hint U hUK)]`.

Conclude with `hdeg U hUK`. Establish `hLr : Module.finrank K1 L = l ^ n * e`. Rewrite using `[IntermediateField.adjoin.finrank (hint K1 hK1K)]`. Conclude with `hdeg K1 hK1K`. Establish `hLU : Module.finrank U L = l ^ n * e`.

Rewrite using `[← hK2r, ← hLK2]`. Both sides reduce to the same expression. Establish `htower` using `Module.finrank_mul_finrank U K1 L`. Rewrite `htower` using `[hLr, hLU]`. Establish `h1 : Module.finrank U K1 = 1`.

Use `Nat.eq_of_mul_eq_mul_right hN (htower.trans (one_mul _).symm)` as an intermediate fact. Conclude with `this`. Establish `hbot : K1 = ⊥` using `IntermediateField.finrank_eq_one_iff.1 h1`. Establish `: x ∈ K1` using `IntermediateField.mem_adjoin_simple_self U x`. Rewrite `this` using `[hbot, IntermediateField.mem_bot]`.

Take `⟨y, rfl⟩` from `this`. Conclude with `y.2`.
-/
theorem mem_Kunr_of_mem_Kur_of_mem_sup : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l →
    x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  intro l _ a e _ _ ϖ n x hxK hx
  have hN : 0 < l ^ n * e :=
    Nat.mul_pos (pow_pos (Fact.out : l.Prime).pos n) (Nat.pos_of_ne_zero (NeZero.ne e))
  have hπ : ϖ.seq n ^ (l ^ n * e) = -(l : Om l) := ϖ.seq_pow_mul n
  set U := Kunr l a with hU
  set π := ϖ.seq n with hπdef

  have hdeg := fun (E : Type) [Field E] [Algebra E (Om l)] (h : ∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) =>
    GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified l (l ^ n * e) π hN hπ E h
  have hint : ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) →
      IsIntegral E π := by
    intro E _ _ h
    by_contra hni
    have := hdeg E h
    rw [minpoly.eq_zero hni, Polynomial.natDegree_zero] at this
    omega
  let K2 : IntermediateField U (Om l) := IntermediateField.adjoin U {π}
  have hxK2 : x ∈ K2 := by
    have : x ∈ K2.restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact hx
    exact this
  let K1 : IntermediateField U (Om l) := IntermediateField.adjoin U {x}
  have hK1K2 : K1 ≤ K2 := IntermediateField.adjoin_simple_le_iff.2 hxK2
  have hUK : ∀ y : U, algebraMap U (Om l) y ∈ MaximalUnramifiedExtension l := fun y => Kunr_le_Kur l a y.2
  have hK1K : ∀ y : K1, algebraMap K1 (Om l) y ∈ MaximalUnramifiedExtension l := by
    intro y
    have hy : (y : Om l) ∈ K1.restrictScalars ℚ_[l] := y.2
    rw [IntermediateField.restrictScalars_adjoin] at hy
    refine (IntermediateField.adjoin_le_iff.2 ?_) hy
    rintro z (hz | hz)
    · exact Kunr_le_Kur l a hz
    · rw [Set.mem_singleton_iff.1 hz]; exact hxK

  let L : IntermediateField K1 (Om l) := IntermediateField.adjoin K1 {π}
  have hLK2 : L.restrictScalars U = K2 := by
    rw [IntermediateField.restrictScalars_adjoin]
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · exact hK1K2 hz
    · rw [Set.mem_singleton_iff.1 hz]; exact IntermediateField.mem_adjoin_simple_self U π
  have hK2r : Module.finrank U K2 = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint U hUK)]; exact hdeg U hUK
  have hLr : Module.finrank K1 L = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint K1 hK1K)]; exact hdeg K1 hK1K
  have hLU : Module.finrank U L = l ^ n * e := by
    rw [← hK2r, ← hLK2]; rfl
  have htower := Module.finrank_mul_finrank U K1 L
  rw [hLr, hLU] at htower
  have h1 : Module.finrank U K1 = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hN (htower.trans (one_mul _).symm)
    exact this
  have hbot : K1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  have : x ∈ K1 := IntermediateField.mem_adjoin_simple_self U x
  rw [hbot, IntermediateField.mem_bot] at this
  obtain ⟨y, rfl⟩ := this
  exact y.2

end GlobalTheory.KunrDisj
