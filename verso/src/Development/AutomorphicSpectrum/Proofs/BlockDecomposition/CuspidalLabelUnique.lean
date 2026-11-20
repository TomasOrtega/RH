import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OrthogonalIntVectorsNotAgreeOnRegular
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGL
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEq

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq

def orb (q d N s : ℕ) : Finset ℕ := (Finset.range d).image fun i => s * q ^ i % N

def ind (S : Finset ℕ) (k : ℕ) : ℤ := if k ∈ S then 1 else 0

section Field

variable {K : Type} [Field K] [Fintype K]

/- English proof (translation)
Establish `hint : IsIntegral K x` using `Algebra.IsIntegral.isIntegral x`. Establish `hfin : Module.finrank K (IntermediateField.adjoin K {x}) = d`. Rewrite using `[IntermediateField.adjoin.finrank hint, hd]`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hint`. Use `haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K`.

Use `letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ d`. Rewrite using `[Module.card_fintype (Module.finBasis K (IntermediateField.adjoin K {x})), Fintype.card_fin, hfin]`. Establish `h` using `FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x})`. Rewrite `h` using `[hcard]`.

Simplify using `using congrArg (fun y : IntermediateField.adjoin K {x} => (y : AlgebraicClosure K)) h`.
-/
theorem pow_card_pow_self (x : AlgebraicClosure K) {d : ℕ} (hd : (minpoly K x).natDegree = d) :
    x ^ (Fintype.card K ^ d) = x := by
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfin : Module.finrank K (IntermediateField.adjoin K {x}) = d := by
    rw [IntermediateField.adjoin.finrank hint, hd]
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ d := by
    rw [Module.card_fintype (Module.finBasis K (IntermediateField.adjoin K {x})), Fintype.card_fin, hfin]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x})
  rw [hcard] at h
  simpa using congrArg (fun y : IntermediateField.adjoin K {x} => (y : AlgebraicClosure K)) h

/- English proof (translation)
Establish `hint : IsIntegral K x` using `Algebra.IsIntegral.isIntegral x`. Use `symm`. Apply `minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint)` to reduce the goal to its premises. Rewrite using `[← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, minpoly.aeval, zero_pow Fintype.card_ne_zero]`. Conclude with `minpoly.monic hint`.
-/
private theorem minpoly_pow_card_pow_lemma (x : AlgebraicClosure K) :
    minpoly K (x ^ Fintype.card K) = minpoly K x := by
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  symm
  apply minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint)
  · rw [← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, minpoly.aeval,
      zero_pow Fintype.card_ne_zero]
  · exact minpoly.monic hint

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [pow_succ, pow_mul, minpoly_pow_card_pow_lemma, ih]`.
-/
theorem minpoly_pow_card_pow (x : AlgebraicClosure K) (i : ℕ) :
    minpoly K (x ^ (Fintype.card K ^ i)) = minpoly K x := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, minpoly_pow_card_pow_lemma, ih]

end Field

end GlobalTheory.CompanionTheory.TyFin.LabelUniq

namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq

section Label

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/- English proof (translation)
Establish `hint : IsIntegral K α` using `Algebra.IsIntegral.isIntegral α`. Establish `hq : 1 < Fintype.card K` using `Fintype.one_lt_card`. Establish `hexp : ∀ n (f : K[X]), f ^ (Fintype.card K ^ n) = expand K (Fintype.card K ^ n) f`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro f`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `f`. Rewrite using `[pow_succ, pow_mul, ih, ← FiniteField.expand_card, ← Polynomial.expand_mul, Nat.mul_comm]`.

Establish `hg : (IntermediateField.AdjoinSimple.gen K α) ^ Fintype.card K ^ e = IntermediateField.AdjoinSimple.gen K α` using `Subtype.ext (by simpa using h)`. Establish `hfix' : ∀ y : IntermediateField.adjoin K {α}, y ^ Fintype.card K ^ e = y`. Introduce `y`. Take `⟨f, -, rfl⟩` from `(IntermediateField.adjoin.powerBasis hint).exists_eq_aeval y`. Rewrite using `[IntermediateField.adjoin.powerBasis_gen, ← map_pow, hexp, Polynomial.expand_aeval, hg]`.

Establish `hfix : ∀ y : IntermediateField.adjoin K {α}, (y : AlgebraicClosure K) ^ Fintype.card K ^ e = y`. Introduce `y`. Simplify using `using congrArg (fun z : IntermediateField.adjoin K {α} => (z : AlgebraicClosure K)) (hfix' y)`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) := IntermediateField.adjoin.finiteDimensional hint`. Use `haveI : Finite (IntermediateField.adjoin K {α}) := Module.finite_of_finite K`.

Use `letI : Fintype (IntermediateField.adjoin K {α}) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (IntermediateField.adjoin K {α}) = Fintype.card K ^ (minpoly K α).natDegree`. Rewrite using `[Module.card_fintype (Module.finBasis K (IntermediateField.adjoin K {α})), Fintype.card_fin, IntermediateField.adjoin.finrank hint]`. Establish `hqe : 1 < Fintype.card K ^ e` using `Nat.one_lt_pow he.ne' hq`. Establish `hdeg : (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).natDegree = Fintype.card K ^ e`.

Apply the tactic sequence `rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hqe]`. Establish `hF0 : (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]) ≠ 0`. Introduce `h0`. Rewrite `hdeg` using `[h0, Polynomial.natDegree_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `hle : Fintype.card (IntermediateField.adjoin K {α}) ≤ Fintype.card K ^ e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]`. Use `_ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).roots.toFinset.card := by`. Apply `Finset.card_le_card` to reduce the goal to its premises.

Introduce `z hz`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and] at hz`. Take `⟨y, rfl⟩` from `hz`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hF0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]`. Conclude with `hfix y`.

Use `_ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).roots.card := Multiset.toFinset_card_le _`. Use `_ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).natDegree := Polynomial.card_roots' _`. Use `_ = Fintype.card K ^ e := hdeg`. Rewrite `hle` using `[hcard]`. Assume the negation of the conclusion as `hlt`.

Rewrite `hlt` using `[not_le]`. Use `Nat.pow_lt_pow_right hq hlt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem regular_iff_degree_lemma (α : AlgebraicClosure K) {e : ℕ} (he : 0 < e)
    (h : α ^ Fintype.card K ^ e = α) : (minpoly K α).natDegree ≤ e := by
  classical
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hexp : ∀ n (f : K[X]), f ^ (Fintype.card K ^ n) = expand K (Fintype.card K ^ n) f := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
      intro f
      rw [pow_succ, pow_mul, ih, ← FiniteField.expand_card, ← Polynomial.expand_mul, Nat.mul_comm]
  have hg : (IntermediateField.AdjoinSimple.gen K α) ^ Fintype.card K ^ e = IntermediateField.AdjoinSimple.gen K α :=
    Subtype.ext (by simpa using h)
  have hfix' : ∀ y : IntermediateField.adjoin K {α}, y ^ Fintype.card K ^ e = y := by
    intro y
    obtain ⟨f, -, rfl⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval y
    rw [IntermediateField.adjoin.powerBasis_gen, ← map_pow, hexp, Polynomial.expand_aeval, hg]
  have hfix : ∀ y : IntermediateField.adjoin K {α}, (y : AlgebraicClosure K) ^ Fintype.card K ^ e = y := by
    intro y
    simpa using congrArg (fun z : IntermediateField.adjoin K {α} => (z : AlgebraicClosure K)) (hfix' y)
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {α}) := Module.finite_of_finite K
  letI : Fintype (IntermediateField.adjoin K {α}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin K {α}) = Fintype.card K ^ (minpoly K α).natDegree := by
    rw [Module.card_fintype (Module.finBasis K (IntermediateField.adjoin K {α})), Fintype.card_fin,
      IntermediateField.adjoin.finrank hint]
  have hqe : 1 < Fintype.card K ^ e := Nat.one_lt_pow he.ne' hq
  have hdeg : (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).natDegree = Fintype.card K ^ e := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hqe]
  have hF0 : (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hle : Fintype.card (IntermediateField.adjoin K {α}) ≤ Fintype.card K ^ e := by
    calc Fintype.card (IntermediateField.adjoin K {α})
        = (Finset.univ.image (fun y : IntermediateField.adjoin K {α} => (y : AlgebraicClosure K))).card := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
      _ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).roots.toFinset.card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
          obtain ⟨y, rfl⟩ := hz
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hF0, Polynomial.IsRoot, Polynomial.eval_sub,
            Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
          exact hfix y
      _ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).natDegree := Polynomial.card_roots' _
      _ = Fintype.card K ^ e := hdeg
  rw [hcard] at hle
  by_contra hlt
  rw [not_le] at hlt
  have := Nat.pow_lt_pow_right hq hlt
  omega

/- English proof (translation)
Establish `hint : IsIntegral K α` using `Algebra.IsIntegral.isIntegral α`. Establish `hq : 1 < Fintype.card K` using `Fintype.one_lt_card`. Establish `hM : 0 < Fintype.card K ^ d - 1`. Use `Nat.le_self_pow hd.ne' (Fintype.card K)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`. Rewrite `hα` using `[zero_pow hM.ne']`. Conclude with `zero_ne_one hα`. Establish `hαd : α ^ Fintype.card K ^ d = α`.

Establish `e : Fintype.card K ^ d = (Fintype.card K ^ d - 1) + 1` using `by omega`. Rewrite using `[e, pow_succ, hα, one_mul]`. Establish `hle` using `regular_iff_degree_lemma α hd hαd`. Establish `hpos : 0 < (minpoly K α).natDegree` using `minpoly.natDegree_pos hint`. Establish `hm` using `pow_card_pow_self α (d := (minpoly K α).natDegree) rfl`.

Use `⟨⟨fun h => ?_, fun h e he hed heq => ?_⟩, fun h => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `h _ hpos (lt_of_le_of_ne hle hne) hm`. Use `regular_iff_degree_lemma α he heq` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hdim : (IntermediateField.adjoin.powerBasis hint).dim = d`. Rewrite using `[IntermediateField.adjoin.powerBasis_dim, h]`. Establish `hchar : (Matrix.reindex (finCongr hdim) (finCongr hdim) (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hint).basis (IntermediateField.adjoin.powerBasis hint).gen)).charpoly = minpoly K α`. Rewrite using `[Matrix.charpoly_reindex, charpoly_leftMulMatrix, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) := IntermediateField.adjoin.finiteDimensional hint`.

Establish `hdet : (Matrix.reindex (finCongr hdim) (finCongr hdim) (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hint).basis (IntermediateField.adjoin.powerBasis hint).gen)).det ≠ 0`. Rewrite using `[Matrix.det_reindex_self, ← Algebra.norm_eq_matrix_det, Ne, Algebra.norm_eq_zero_iff, IntermediateField.adjoin.powerBasis_gen]`. Introduce `h0`. Apply `hα0` to reduce the goal to its premises. Simplify using `using congrArg (fun y : IntermediateField.adjoin K {α} => (y : AlgebraicClosure K)) h0`.

Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)`. Conclude with `⟨hu.unit, by rw [IsUnit.unit_spec]; exact hchar⟩`.
-/
theorem regular_iff_degree {d : ℕ} (hd : 0 < d) (α : AlgebraicClosure K)
    (hα : α ^ (Fintype.card K ^ d - 1) = 1) :
    ((∀ e : ℕ, 0 < e → e < d → α ^ Fintype.card K ^ e ≠ α) ↔ (minpoly K α).natDegree = d) ∧
      ((minpoly K α).natDegree = d →
        ∃ x : GL (Fin d) K, Matrix.charpoly (x : Matrix (Fin d) (Fin d) K) = minpoly K α) := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hM : 0 < Fintype.card K ^ d - 1 := by
    have := Nat.le_self_pow hd.ne' (Fintype.card K)
    omega
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hα
    exact zero_ne_one hα
  have hαd : α ^ Fintype.card K ^ d = α := by
    have e : Fintype.card K ^ d = (Fintype.card K ^ d - 1) + 1 := by omega
    rw [e, pow_succ, hα, one_mul]
  have hle := regular_iff_degree_lemma α hd hαd
  have hpos : 0 < (minpoly K α).natDegree := minpoly.natDegree_pos hint
  have hm := pow_card_pow_self α (d := (minpoly K α).natDegree) rfl
  refine ⟨⟨fun h => ?_, fun h e he hed heq => ?_⟩, fun h => ?_⟩
  · by_contra hne
    exact h _ hpos (lt_of_le_of_ne hle hne) hm
  · have := regular_iff_degree_lemma α he heq
    omega
  · have hdim : (IntermediateField.adjoin.powerBasis hint).dim = d := by
      rw [IntermediateField.adjoin.powerBasis_dim, h]
    have hchar : (Matrix.reindex (finCongr hdim) (finCongr hdim)
        (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hint).basis
          (IntermediateField.adjoin.powerBasis hint).gen)).charpoly = minpoly K α := by
      rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.minpoly_gen]
    haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hdet : (Matrix.reindex (finCongr hdim) (finCongr hdim)
        (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hint).basis
          (IntermediateField.adjoin.powerBasis hint).gen)).det ≠ 0 := by
      rw [Matrix.det_reindex_self, ← Algebra.norm_eq_matrix_det, Ne, Algebra.norm_eq_zero_iff,
        IntermediateField.adjoin.powerBasis_gen]
      intro h0
      apply hα0
      simpa using congrArg (fun y : IntermediateField.adjoin K {α} => (y : AlgebraicClosure K)) h0
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hchar⟩

/- English proof (translation)
Conclude with `Fintype.one_lt_card`.
-/
theorem two_le_card : 2 ≤ Fintype.card K := by
  exact Fintype.one_lt_card

/- English proof (translation)
Rewrite using `[← C.gen_order d hd]`. Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem gen_primitive (C : LabelConv K) {d : ℕ} (hd : 0 < d) :
    IsPrimitiveRoot (C.gen d) (Fintype.card K ^ d - 1) := by
  rw [← C.gen_order d hd]
  exact IsPrimitiveRoot.orderOf _

/- English proof (translation)
Establish `h2 : 2 ≤ Fintype.card K` using `two_le_card`. Establish `h3 : Fintype.card K ≤ Fintype.card K ^ d` using `Nat.le_self_pow hd.ne' _`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_pow_sub_one_pos {d : ℕ} (hd : 0 < d) : 0 < Fintype.card K ^ d - 1 := by
  have h2 : 2 ≤ Fintype.card K := two_le_card
  have h3 : Fintype.card K ≤ Fintype.card K ^ d := Nat.le_self_pow hd.ne' _
  omega

/- English proof (translation)
Conclude with `(gen_primitive C hd).ne_zero (card_pow_sub_one_pos hd).ne'`.
-/
theorem gen_ne_zero (C : LabelConv K) {d : ℕ} (hd : 0 < d) : C.gen d ≠ 0 := by
  exact (gen_primitive C hd).ne_zero (card_pow_sub_one_pos hd).ne'

/- English proof (translation)
Take `⟨x, hx⟩` from `IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P (Polynomial.degree_pos_of_irreducible hi).ne'`. Establish `hmin : minpoly K x = P` using `(minpoly.eq_of_irreducible_of_monic hi hx hm).symm`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hX (by rw [← hmin, minpoly.zero])`.

Establish `hdeg' : (minpoly K x).natDegree = d` using `by rw [hmin, hdeg]`. Establish `hxq : x ^ Fintype.card K ^ d = x` using `pow_card_pow_self x hdeg'`. Establish `hpos` using `card_pow_sub_one_pos (K := K) hd`. Establish `hx1 : x ^ (Fintype.card K ^ d - 1) = 1`. Establish `h1 : x ^ (Fintype.card K ^ d - 1) * x = 1 * x`.

Rewrite using `[← pow_succ, Nat.sub_add_cancel (by omega), hxq, one_mul]`. Conclude with `mul_right_cancel₀ hx0 h1`. Use `haveI : NeZero (Fintype.card K ^ d - 1) := ⟨hpos.ne'⟩`. Establish `hord : orderOf (C.gen d) = Fintype.card K ^ d - 1` using `C.gen_order d hd`. Establish `hfin : IsOfFinOrder (C.gen d)` using `orderOf_pos_iff.mp (by rw [hord]; exact hpos)`.

Establish `hmodq : ∀ a b : ℕ, C.gen d ^ a = C.gen d ^ b ↔ a ≡ b [MOD Fintype.card K ^ d - 1]`. Introduce `a b`. Rewrite using `[← hord]`. Conclude with `hfin.pow_eq_pow_iff_modEq`. Take `⟨s, -, hs⟩` from `(gen_primitive C hd).eq_pow_of_pow_eq_one hx1`.

Use `⟨x, s, hx, hmin, hs, ?_⟩` and prove the remaining obligations. Introduce `e he hed hmod`. Apply `((regular_iff_degree hd x hx1).1.mpr hdeg') e he hed` to reduce the goal to its premises. Rewrite using `[← hs, ← pow_mul]`. Conclude with `(hmodq _ _).mpr hmod`.
-/
theorem exists_root (C : LabelConv K) {d : ℕ} (hd : 0 < d) {P : K[X]} (hm : P.Monic)
    (hi : Irreducible P) (hX : P ≠ X) (hdeg : P.natDegree = d) :
    ∃ (x : AlgebraicClosure K) (s : ℕ), aeval x P = 0 ∧ minpoly K x = P ∧ C.gen d ^ s = x ∧
      ∀ e, 0 < e → e < d → ¬ s * Fintype.card K ^ e ≡ s [MOD Fintype.card K ^ d - 1] := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P (Polynomial.degree_pos_of_irreducible hi).ne'
  have hmin : minpoly K x = P := (minpoly.eq_of_irreducible_of_monic hi hx hm).symm
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hX (by rw [← hmin, minpoly.zero])
  have hdeg' : (minpoly K x).natDegree = d := by rw [hmin, hdeg]
  have hxq : x ^ Fintype.card K ^ d = x := pow_card_pow_self x hdeg'
  have hpos := card_pow_sub_one_pos (K := K) hd
  have hx1 : x ^ (Fintype.card K ^ d - 1) = 1 := by
    have h1 : x ^ (Fintype.card K ^ d - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hxq, one_mul]
    exact mul_right_cancel₀ hx0 h1
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨hpos.ne'⟩
  have hord : orderOf (C.gen d) = Fintype.card K ^ d - 1 := C.gen_order d hd
  have hfin : IsOfFinOrder (C.gen d) := orderOf_pos_iff.mp (by rw [hord]; exact hpos)
  have hmodq : ∀ a b : ℕ, C.gen d ^ a = C.gen d ^ b ↔ a ≡ b [MOD Fintype.card K ^ d - 1] := by
    intro a b
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq
  obtain ⟨s, -, hs⟩ := (gen_primitive C hd).eq_pow_of_pow_eq_one hx1
  refine ⟨x, s, hx, hmin, hs, ?_⟩
  intro e he hed hmod
  apply ((regular_iff_degree hd x hx1).1.mpr hdeg') e he hed
  rw [← hs, ← pow_mul]
  exact (hmodq _ _).mpr hmod

/- English proof (translation)
Establish `hprim` using `gen_primitive C hd`. Establish `hα1 : (C.gen (Fintype.card ι) ^ j) ^ (Fintype.card K ^ Fintype.card ι - 1) = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]`. Establish `hpos` using `card_pow_sub_one_pos (K := K) hd`. Establish `hord : orderOf (C.gen (Fintype.card ι)) = Fintype.card K ^ Fintype.card ι - 1` using `C.gen_order _ hd`.

Establish `hfin : IsOfFinOrder (C.gen (Fintype.card ι))` using `orderOf_pos_iff.mp (by rw [hord]; exact hpos)`. Establish `hreg : ∀ e : ℕ, 0 < e → e < Fintype.card ι → (C.gen (Fintype.card ι) ^ j) ^ Fintype.card K ^ e ≠ C.gen (Fintype.card ι) ^ j`. Introduce `e he hed heq`. Apply `hj e he hed` to reduce the goal to its premises. Rewrite `heq` using `[← pow_mul]`.

Rewrite using `[← hord]`. Conclude with `hfin.pow_eq_pow_iff_modEq.mp heq`. Take `⟨hiff, hex⟩` from `regular_iff_degree hd (C.gen (Fintype.card ι) ^ j) hα1`. Take `⟨x, hx⟩` from `hex (hiff.mp hreg)`. Establish `hMchar : (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm (x : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K)).charpoly = minpoly K (C.gen (Fintype.card ι) ^ j)`.

Rewrite using `[Matrix.charpoly_reindex, hx]`. Establish `hMu : IsUnit (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm (x : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, ← Matrix.isUnit_iff_isUnit_det]`. Conclude with `x.isUnit`. Use `⟨hMu.unit, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsUnit.unit_spec, hMchar]`. Conclude with `minpoly.irreducible (Algebra.IsIntegral.isIntegral _)`. Rewrite using `[IsUnit.unit_spec, hMchar]`. Conclude with `minpoly.aeval K _`.
-/
theorem exists_elliptic (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hd : 0 < Fintype.card ι) (j : ℕ)
    (hj : ∀ e, 0 < e → e < Fintype.card ι →
      ¬ j * Fintype.card K ^ e ≡ j [MOD Fintype.card K ^ Fintype.card ι - 1]) :
    ∃ γ : GL ι K, Irreducible (Matrix.charpoly (γ : Matrix ι ι K)) ∧
      aeval (C.gen (Fintype.card ι) ^ j) (Matrix.charpoly (γ : Matrix ι ι K)) = 0 := by
  have hprim := gen_primitive C hd
  have hα1 : (C.gen (Fintype.card ι) ^ j) ^ (Fintype.card K ^ Fintype.card ι - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hpos := card_pow_sub_one_pos (K := K) hd
  have hord : orderOf (C.gen (Fintype.card ι)) = Fintype.card K ^ Fintype.card ι - 1 := C.gen_order _ hd
  have hfin : IsOfFinOrder (C.gen (Fintype.card ι)) := orderOf_pos_iff.mp (by rw [hord]; exact hpos)
  have hreg : ∀ e : ℕ, 0 < e → e < Fintype.card ι →
      (C.gen (Fintype.card ι) ^ j) ^ Fintype.card K ^ e ≠ C.gen (Fintype.card ι) ^ j := by
    intro e he hed heq
    apply hj e he hed
    rw [← pow_mul] at heq
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp heq
  obtain ⟨hiff, hex⟩ := regular_iff_degree hd (C.gen (Fintype.card ι) ^ j) hα1
  obtain ⟨x, hx⟩ := hex (hiff.mp hreg)
  have hMchar : (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm
      (x : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K)).charpoly =
      minpoly K (C.gen (Fintype.card ι) ^ j) := by
    rw [Matrix.charpoly_reindex, hx]
  have hMu : IsUnit (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm
      (x : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, ← Matrix.isUnit_iff_isUnit_det]
    exact x.isUnit
  refine ⟨hMu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hMchar]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  · rw [IsUnit.unit_spec, hMchar]
    exact minpoly.aeval K _

/- English proof (translation)
Introduce `m hm`. Proceed by induction on `m with`. Consider the case `zero => omega`. Consider the case `succ m ih`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases.

Substitute `h` using the available equality. Evaluate the numerical expressions. Establish `h1` using `ih h`. Establish `h2 : 2 ≤ 2 ^ m`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[pow_succ]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem two_mul_le_two_pow_lemma_2 : ∀ m : ℕ, 1 ≤ m → 2 * m ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      norm_num
    · have h1 := ih h
      have h2 : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ]
      omega

/- English proof (translation)
Establish `hB : d ≤ q ^ (d - e)`. Establish `h1 : d ≤ 2 * (d - e)` using `by omega`. Establish `h2` using `two_mul_le_two_pow_lemma_2 (d - e) (by omega)`. Establish `h3 : 2 ^ (d - e) ≤ q ^ (d - e)` using `Nat.pow_le_pow_left hq _`. Use linear arithmetic over natural numbers and integers.

Establish `hsplit : q ^ d = q ^ e * q ^ (d - e)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' (by omega)]`. Establish `hA : 1 ≤ q ^ e` using `Nat.one_le_pow _ _ (by omega)`. Take `⟨A', hA'⟩ : ∃ A', q ^ e = A' + 1` from `⟨q ^ e - 1, by omega⟩`. Rewrite using `[hsplit, hA', Nat.add_sub_cancel]`.

Establish `key : d * A' ≤ A' * q ^ (d - e)`. Rewrite using `[mul_comm A']`. Conclude with `Nat.mul_le_mul_right A' hB`. Establish `h5 : (A' + 1) * q ^ (d - e) = A' * q ^ (d - e) + q ^ (d - e)` using `by ring`. Rewrite using `[h5]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem small_lt_lemma_3 {q d e : ℕ} (hq : 2 ≤ q) (he : 1 ≤ e) (hed : 2 * e ≤ d) :
    d * (q ^ e - 1) < q ^ d - 1 := by
  have hB : d ≤ q ^ (d - e) := by
    have h1 : d ≤ 2 * (d - e) := by omega
    have h2 := two_mul_le_two_pow_lemma_2 (d - e) (by omega)
    have h3 : 2 ^ (d - e) ≤ q ^ (d - e) := Nat.pow_le_pow_left hq _
    omega
  have hsplit : q ^ d = q ^ e * q ^ (d - e) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  have hA : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
  obtain ⟨A', hA'⟩ : ∃ A', q ^ e = A' + 1 := ⟨q ^ e - 1, by omega⟩
  rw [hsplit, hA', Nat.add_sub_cancel]
  have key : d * A' ≤ A' * q ^ (d - e) := by
    rw [mul_comm A']
    exact Nat.mul_le_mul_right A' hB
  have h5 : (A' + 1) * q ^ (d - e) = A' * q ^ (d - e) + q ^ (d - e) := by ring
  rw [h5]
  omega

/- English proof (translation)
Establish `hqd : q ^ d ≡ 1 [MOD q ^ d - 1]`. Establish `h1 : 1 ≤ q ^ d` using `Nat.one_le_pow _ _ (by omega)`. Establish `e1 : q ^ d = (q ^ d - 1) + 1` using `by omega`. Rewrite using `[e1, Nat.add_sub_cancel]`. Conclude with `Nat.add_modEq_left`.

Establish `hsmall : ∀ e', 0 < e' → 2 * e' ≤ d → ¬ j * q ^ e' ≡ j [MOD q ^ d - 1]`. Introduce `e' he' h2e hmod`. Establish `hle : j ≤ j * q ^ e'` using `Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))`. Establish `hdvd : q ^ d - 1 ∣ j * q ^ e' - j` using `(Nat.modEq_iff_dvd' hle).1 hmod.symm`. Establish `hpos : 0 < j * q ^ e' - j`.

Establish `h1 : q ≤ q ^ e'` using `Nat.le_self_pow he'.ne' q`. Establish `h2 : j * q ≤ j * q ^ e'` using `Nat.mul_le_mul_left _ h1`. Establish `h3 : j * 2 ≤ j * q` using `Nat.mul_le_mul_left _ hq`. Use linear arithmetic over natural numbers and integers. Establish `hlt : j * q ^ e' - j < q ^ d - 1`.

Establish `h1` using `small_lt_lemma_3 hq he' h2e`. Establish `h2 : j * (q ^ e' - 1) ≤ d * (q ^ e' - 1)` using `Nat.mul_le_mul_right _ hjd`. Establish `h3 : j * q ^ e' - j = j * (q ^ e' - 1)` using `by rw [Nat.mul_sub_one]`. Use linear arithmetic over natural numbers and integers. Conclude with `absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hlt)`.

Distinguish the cases in `h2e : 2 * e ≤ d`. Conclude with `hsmall e he h2e`. Introduce `hmod`. Apply `hsmall (d - e) (by omega) (by omega)` to reduce the goal to its premises. Establish `h1 : j * q ^ e * q ^ (d - e) ≡ j * q ^ (d - e) [MOD q ^ d - 1]` using `hmod.mul_right _`.

Establish `e2 : j * q ^ e * q ^ (d - e) = j * q ^ d`. Rewrite using `[mul_assoc, ← pow_add, Nat.add_sub_cancel' hed.le]`. Rewrite `h1` using `[e2]`. Establish `h3 : j * q ^ d ≡ j [MOD q ^ d - 1]` using `by simpa using hqd.mul_left j`. Conclude with `h1.symm.trans h3`.
-/
private theorem reg_small_lemma_4 {q d : ℕ} (hq : 2 ≤ q) {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (e : ℕ) (he : 0 < e) (hed : e < d) : ¬ j * q ^ e ≡ j [MOD q ^ d - 1] := by
  have hqd : q ^ d ≡ 1 [MOD q ^ d - 1] := by
    have h1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
    have e1 : q ^ d = (q ^ d - 1) + 1 := by omega
    rw [e1, Nat.add_sub_cancel]
    exact Nat.add_modEq_left
  have hsmall : ∀ e', 0 < e' → 2 * e' ≤ d → ¬ j * q ^ e' ≡ j [MOD q ^ d - 1] := by
    intro e' he' h2e hmod
    have hle : j ≤ j * q ^ e' := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    have hdvd : q ^ d - 1 ∣ j * q ^ e' - j := (Nat.modEq_iff_dvd' hle).1 hmod.symm
    have hpos : 0 < j * q ^ e' - j := by
      have h1 : q ≤ q ^ e' := Nat.le_self_pow he'.ne' q
      have h2 : j * q ≤ j * q ^ e' := Nat.mul_le_mul_left _ h1
      have h3 : j * 2 ≤ j * q := Nat.mul_le_mul_left _ hq
      omega
    have hlt : j * q ^ e' - j < q ^ d - 1 := by
      have h1 := small_lt_lemma_3 hq he' h2e
      have h2 : j * (q ^ e' - 1) ≤ d * (q ^ e' - 1) := Nat.mul_le_mul_right _ hjd
      have h3 : j * q ^ e' - j = j * (q ^ e' - 1) := by rw [Nat.mul_sub_one]
      omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hlt)
  by_cases h2e : 2 * e ≤ d
  · exact hsmall e he h2e
  · intro hmod
    apply hsmall (d - e) (by omega) (by omega)
    have h1 : j * q ^ e * q ^ (d - e) ≡ j * q ^ (d - e) [MOD q ^ d - 1] := hmod.mul_right _
    have e2 : j * q ^ e * q ^ (d - e) = j * q ^ d := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hed.le]
    rw [e2] at h1
    have h3 : j * q ^ d ≡ j [MOD q ^ d - 1] := by simpa using hqd.mul_left j
    exact h1.symm.trans h3

/- English proof (translation)
Establish `hps : ∀ j, 1 ≤ j → j ≤ d → MvPolynomial.aeval u (MvPolynomial.psum (Fin d) ℂ j) = MvPolynomial.aeval v (MvPolynomial.psum (Fin d) ℂ j)`. Introduce `j h1 h2`. Simplify using `only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]`. Conclude with `h j h1 h2`. Establish `hes : ∀ k, k ≤ d → MvPolynomial.aeval u (MvPolynomial.esymm (Fin d) ℂ k) = MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℂ k)`.

Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `hk`. Break down `Nat.eq_zero_or_pos k with h0 | hpos` into its components or cases.

Substitute `h0` using the available equality. Simplify using `[MvPolynomial.esymm_zero]`. Establish `hu` using `congrArg (MvPolynomial.aeval u) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k)`. Establish `hv` using `congrArg (MvPolynomial.aeval v) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k)`. Simplify using `only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at hu hv`.

Establish `hk0 : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hpos.ne'`. Apply `mul_left_cancel₀ hk0` to reduce the goal to its premises. Rewrite using `[hu, hv]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun a ha => ?_)` and prove the remaining obligations.

Rewrite `ha` using `[Finset.mem_filter]`. Establish `hsum` using `Finset.HasAntidiagonal.mem_antidiagonal.1 ha.1`. Rewrite using `[ih a.1 ha.2 (by omega), hps a.2 (by omega) (by omega)]`. Establish `hUc : (Multiset.map u Finset.univ.val).card = d` using `by simp`. Establish `hVc : (Multiset.map v Finset.univ.val).card = d` using `by simp`.

Establish `hE : ∀ k, k ≤ d → (Multiset.map u Finset.univ.val).esymm k = (Multiset.map v Finset.univ.val).esymm k`. Introduce `k hk`. Establish `h1` using `hes k hk`. Rewrite `h1` using `[MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm]`. Then use the resulting hypothesis. Establish `hprod : ((Multiset.map u Finset.univ.val).map fun t => X - C t).prod = ((Multiset.map v Finset.univ.val).map fun t => X - C t).prod`.

Use extensionality with `n`. Distinguish the cases in `hn : n ≤ d`. Rewrite using `[Multiset.prod_X_sub_C_coeff _ (by omega), Multiset.prod_X_sub_C_coeff _ (by omega), hUc, hVc, hE _ (by omega)]`. Use `push Not at hn`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]`.

Apply the tactic sequence `all_goals first`. Consider the case `(rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hUc]; exact hn)`. Consider the case `(rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hVc]; exact hn)`. Establish `h2` using `congrArg Polynomial.roots hprod`. Rewrite `h2` using `[Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C]`. Then use the resulting hypothesis.
-/
private theorem multiset_eq_of_psum_lemma_5 {d : ℕ} (u v : Fin d → ℂ)
    (h : ∀ j, 1 ≤ j → j ≤ d → ∑ a, u a ^ j = ∑ a, v a ^ j) :
    Multiset.map u Finset.univ.val = Multiset.map v Finset.univ.val := by
  have hps : ∀ j, 1 ≤ j → j ≤ d → MvPolynomial.aeval u (MvPolynomial.psum (Fin d) ℂ j) =
      MvPolynomial.aeval v (MvPolynomial.psum (Fin d) ℂ j) := by
    intro j h1 h2
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
    exact h j h1 h2
  have hes : ∀ k, k ≤ d → MvPolynomial.aeval u (MvPolynomial.esymm (Fin d) ℂ k) =
      MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        simp [MvPolynomial.esymm_zero]
      · have hu := congrArg (MvPolynomial.aeval u) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k)
        have hv := congrArg (MvPolynomial.aeval v) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k)
        simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at hu hv
        have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
        apply mul_left_cancel₀ hk0
        rw [hu, hv]
        congr 1
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_filter] at ha
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 ha.1
        rw [ih a.1 ha.2 (by omega), hps a.2 (by omega) (by omega)]
  have hUc : (Multiset.map u Finset.univ.val).card = d := by simp
  have hVc : (Multiset.map v Finset.univ.val).card = d := by simp
  have hE : ∀ k, k ≤ d → (Multiset.map u Finset.univ.val).esymm k =
      (Multiset.map v Finset.univ.val).esymm k := by
    intro k hk
    have h1 := hes k hk
    rwa [MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm] at h1
  have hprod : ((Multiset.map u Finset.univ.val).map fun t => X - C t).prod =
      ((Multiset.map v Finset.univ.val).map fun t => X - C t).prod := by
    ext n
    by_cases hn : n ≤ d
    · rw [Multiset.prod_X_sub_C_coeff _ (by omega), Multiset.prod_X_sub_C_coeff _ (by omega), hUc, hVc,
        hE _ (by omega)]
    · push Not at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
      all_goals first
        | (rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hUc]; exact hn)
        | (rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hVc]; exact hn)
  have h2 := congrArg Polynomial.roots hprod
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h2

/- English proof (translation)
Introduce `K _ _ _ C ι _ _ τ P P' hP hP'`. Take `⟨hm, hi, hX, hdeg, htr⟩` from `hP`. Take `⟨hm', hi', hX', hdeg', htr'⟩` from `hP'`. Establish `hd : 0 < Fintype.card ι`. Rewrite using `[← hdeg]`.

Conclude with `Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hi)`. Take `⟨x, s, hx, hmin, hs, -⟩` from `exists_root C hd hm hi hX hdeg`. Take `⟨x', s', hx', hmin', hs', -⟩` from `exists_root C hd hm' hi' hX' hdeg'`. Establish `hx0 : x ≠ 0`. Rewrite using `[← hs]`.

Conclude with `pow_ne_zero _ (gen_ne_zero C hd)`. Establish `hx0' : x' ≠ 0`. Rewrite using `[← hs']`. Conclude with `pow_ne_zero _ (gen_ne_zero C hd)`. Establish `hq : 2 ≤ Fintype.card K` using `two_le_card`.

Establish `epow : ∀ (y : ℂ) (a j : ℕ), (y ^ Fintype.card K ^ a) ^ j = y ^ (j * Fintype.card K ^ a)`. Introduce `y a j`. Rewrite using `[← pow_mul, mul_comm]`. Establish `hpow : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → ∑ a : Fin (Fintype.card ι), (C.ι x ^ Fintype.card K ^ (a : ℕ)) ^ j = ∑ a : Fin (Fintype.card ι), (C.ι x' ^ Fintype.card K ^ (a : ℕ)) ^ j`. Introduce `j hj1 hjd`.

Take `⟨γ, hγ, hγr⟩` from `exists_elliptic C hd j (fun e he hed => reg_small_lemma_4 hq hj1 hjd e he hed)`. Establish `h1` using `htr x hx γ hγ _ hγr j rfl`. Establish `h2` using `htr' x' hx' γ hγ _ hγr j rfl`. Rewrite `h2` using `[h1]`. Establish `h3` using `mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h2`.

Rewrite `h3` using `[Finset.sum_range, Finset.sum_range]`. Simplify using `only [epow]`. Conclude with `h3`. Establish `hmult` using `multiset_eq_of_psum_lemma_5 _ _ hpow`. Establish `hmem : C.ι x ∈ Multiset.map (fun a : Fin (Fintype.card ι) => C.ι x' ^ Fintype.card K ^ (a : ℕ)) Finset.univ.val`.

Rewrite using `[← hmult]`. Use `Multiset.mem_map.2 ⟨⟨0, hd⟩, Finset.mem_univ_val _, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Take `⟨a, -, ha⟩` from `Multiset.mem_map.1 hmem`. Establish `hxa : x = x' ^ Fintype.card K ^ (a : ℕ)`.

Apply `C.ι_inj _ _ hx0 (pow_ne_zero _ hx0')` to reduce the goal to its premises. Rewrite using `[map_pow]`. Conclude with `ha.symm`. Rewrite using `[← hmin, ← hmin', hxa, minpoly_pow_card_pow]`.
-/
theorem hasCuspLabel_unique : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (ι : Type)
    [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) (P P' : K[X]),
    HasCuspLabel C τ P → HasCuspLabel C τ P' → P = P' := by
  intro K _ _ _ C ι _ _ τ P P' hP hP'
  obtain ⟨hm, hi, hX, hdeg, htr⟩ := hP
  obtain ⟨hm', hi', hX', hdeg', htr'⟩ := hP'
  have hd : 0 < Fintype.card ι := by
    rw [← hdeg]
    exact Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hi)
  obtain ⟨x, s, hx, hmin, hs, -⟩ := exists_root C hd hm hi hX hdeg
  obtain ⟨x', s', hx', hmin', hs', -⟩ := exists_root C hd hm' hi' hX' hdeg'
  have hx0 : x ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero _ (gen_ne_zero C hd)
  have hx0' : x' ≠ 0 := by
    rw [← hs']
    exact pow_ne_zero _ (gen_ne_zero C hd)
  have hq : 2 ≤ Fintype.card K := two_le_card
  have epow : ∀ (y : ℂ) (a j : ℕ), (y ^ Fintype.card K ^ a) ^ j = y ^ (j * Fintype.card K ^ a) := by
    intro y a j
    rw [← pow_mul, mul_comm]
  have hpow : ∀ j, 1 ≤ j → j ≤ Fintype.card ι →
      ∑ a : Fin (Fintype.card ι), (C.ι x ^ Fintype.card K ^ (a : ℕ)) ^ j =
      ∑ a : Fin (Fintype.card ι), (C.ι x' ^ Fintype.card K ^ (a : ℕ)) ^ j := by
    intro j hj1 hjd
    obtain ⟨γ, hγ, hγr⟩ :=
      exists_elliptic C hd j (fun e he hed => reg_small_lemma_4 hq hj1 hjd e he hed)
    have h1 := htr x hx γ hγ _ hγr j rfl
    have h2 := htr' x' hx' γ hγ _ hγr j rfl
    rw [h1] at h2
    have h3 := mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h2
    rw [Finset.sum_range, Finset.sum_range] at h3
    simp only [epow]
    exact h3
  have hmult := multiset_eq_of_psum_lemma_5 _ _ hpow
  have hmem : C.ι x ∈ Multiset.map (fun a : Fin (Fintype.card ι) => C.ι x' ^ Fintype.card K ^ (a : ℕ))
      Finset.univ.val := by
    rw [← hmult]
    refine Multiset.mem_map.2 ⟨⟨0, hd⟩, Finset.mem_univ_val _, ?_⟩
    simp
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 hmem
  have hxa : x = x' ^ Fintype.card K ^ (a : ℕ) := by
    apply C.ι_inj _ _ hx0 (pow_ne_zero _ hx0')
    rw [map_pow]
    exact ha.symm
  rw [← hmin, ← hmin', hxa, minpoly_pow_card_pow]

end Label

end GlobalTheory.CompanionTheory.TyFin.LabelUniq
