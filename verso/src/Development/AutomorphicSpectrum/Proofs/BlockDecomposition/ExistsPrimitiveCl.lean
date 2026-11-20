import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.RootsC

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih`. Rewrite using `[← Nat.add_assoc, pow_succ', pow_mul, GroundTheory.PAdicHodge.rootSeq_succ_pow, ih]`.
-/
theorem seq_add_pow (m d : ℕ) : rootSeq l (m + d) ^ l ^ d = rootSeq l m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, pow_succ', pow_mul, GroundTheory.PAdicHodge.rootSeq_succ_pow, ih]

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[pow_zero, IsPrimitiveRoot.one_right_iff]`. Simplify using `using (GroundTheory.PAdicHodge.rootSeq_pow (p := l) 0)`. Consider the case `succ k`.

Establish `h1 : ¬ rootSeq l (k + 1) ^ l ^ k = 1`. Rewrite using `[Nat.add_comm, seq_add_pow]`. Conclude with `GroundTheory.PAdicHodge.rootSeq_one_ne_one`. Establish `h2` using `orderOf_eq_prime_pow h1 (GroundTheory.PAdicHodge.rootSeq_pow (p := l) (k + 1))`. Rewrite using `[← h2]`.

Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem seq_primitive (n : ℕ) : IsPrimitiveRoot (rootSeq l n) (l ^ n) := by
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    simpa using (GroundTheory.PAdicHodge.rootSeq_pow (p := l) 0)
  | succ k =>
    have h1 : ¬ rootSeq l (k + 1) ^ l ^ k = 1 := by
      rw [Nat.add_comm, seq_add_pow]
      exact GroundTheory.PAdicHodge.rootSeq_one_ne_one
    have h2 := orderOf_eq_prime_pow h1 (GroundTheory.PAdicHodge.rootSeq_pow (p := l) (k + 1))
    rw [← h2]
    exact IsPrimitiveRoot.orderOf _

/- English proof (translation)
Establish `hq : (l ^ n : ℕ) ≠ 0` using `pow_ne_zero n hl.out.ne_zero`. Use `haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by exact_mod_cast hq⟩`. Establish `hdeg : (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l)).degree ≠ 0`. Rewrite using `[Polynomial.degree_cyclotomic]`. Establish `ht : 0 < Nat.totient (l ^ n)` using `Nat.totient_pos.2 (Nat.pos_of_ne_zero hq)`.

Conclude with `ht.ne'` after adjusting the coercions. Take `⟨η, hη⟩` from `IsAlgClosed.exists_root _ hdeg`. Conclude with `⟨η, Polynomial.isRoot_cyclotomic_iff.1 hη⟩`.
-/
theorem exists_primitive_cl (n : ℕ) : ∃ η : PadicAlgCl l, IsPrimitiveRoot η (l ^ n) := by
  have hq : (l ^ n : ℕ) ≠ 0 := pow_ne_zero n hl.out.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by exact_mod_cast hq⟩
  have hdeg : (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have ht : 0 < Nat.totient (l ^ n) := Nat.totient_pos.2 (Nat.pos_of_ne_zero hq)
    exact_mod_cast ht.ne'
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨η, Polynomial.isRoot_cyclotomic_iff.1 hη⟩

/- English proof (translation)
Take `⟨η, hη⟩` from `exists_primitive_cl (l := l) n`. Establish `hinj : Function.Injective (clToC l)` using `(clToC l).injective`. Establish `hη' : IsPrimitiveRoot (clToC l η) (l ^ n)` using `(IsPrimitiveRoot.map_iff_of_injective hinj).2 hη`. Take `⟨i, -, hi⟩` from `hη'.eq_pow_of_pow_eq_one (GroundTheory.PAdicHodge.rootSeq_pow (p := l) n)`. Use `⟨η ^ i, ?_, by rw [map_pow, hi]⟩` and prove the remaining obligations.

Rewrite using `[← IsPrimitiveRoot.map_iff_of_injective hinj, map_pow, hi]`. Conclude with `seq_primitive n`.
-/
theorem exists_lift (n : ℕ) :
    ∃ ρ : PadicAlgCl l, IsPrimitiveRoot ρ (l ^ n) ∧ clToC l ρ = rootSeq l n := by
  obtain ⟨η, hη⟩ := exists_primitive_cl (l := l) n
  have hinj : Function.Injective (clToC l) := (clToC l).injective
  have hη' : IsPrimitiveRoot (clToC l η) (l ^ n) :=
    (IsPrimitiveRoot.map_iff_of_injective hinj).2 hη
  obtain ⟨i, -, hi⟩ := hη'.eq_pow_of_pow_eq_one (GroundTheory.PAdicHodge.rootSeq_pow (p := l) n)
  refine ⟨η ^ i, ?_, by rw [map_pow, hi]⟩
  rw [← IsPrimitiveRoot.map_iff_of_injective hinj, map_pow, hi]
  exact seq_primitive n

/- English proof (translation)
Use `⟨isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hq), ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `h.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)`.
-/
theorem prim_of_primitive {q : ℕ} (hq : q ≠ 0) {F : Type} [Field F] [CharZero F] {ρ : F}
    (h : IsPrimitiveRoot ρ q) :
    IsUnit ((q : ℕ) : F) ∧ Polynomial.aeval ρ (Polynomial.cyclotomic q ℤ) = 0 := by
  refine ⟨isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hq), ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact h.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)

/- English proof (translation)
Introduce `l _`. Use `choose ρ hρ using fun n => exists_lift (l := l) n`. Conclude with `⟨⟨fun n => Subtype.mk (ρ n) (prim_of_primitive (pow_ne_zero n (Fact.out : l.Prime).ne_zero) (hρ n).1), fun n => (hρ n).2⟩⟩`.
-/
theorem rootsEx : CrystallineSemistableComparison.E.RootsEx := by
  intro l _
  choose ρ hρ using fun n => exists_lift (l := l) n
  exact ⟨⟨fun n => Subtype.mk (ρ n)
      (prim_of_primitive (pow_ne_zero n (Fact.out : l.Prime).ne_zero) (hρ n).1),
    fun n => (hρ n).2⟩⟩

end GlobalTheory.CompanionTheory.RootsC
