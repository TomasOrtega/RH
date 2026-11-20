import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.NCInhab
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsAvoidProgression
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HostPrimes
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsIsPrimitiveRootIff
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.HeckeCharacterLocalChoice
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDisc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HvQuadInertia

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

open KStar.Ram DirichletCharacter

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : K, ∀ c : ℚ, c • (1 : K) ≠ x := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `(finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero).2 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `li : LinearIndependent ℚ ![(1 : K), x]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality.

Simplify using `at hst`. Conclude with `⟨hst, rfl⟩`. It suffices to derive a contradiction. Apply `hx (-(s / t))` to reduce the goal to its premises. Rewrite using `[neg_smul, neg_eq_iff_add_eq_zero, ← one_smul ℚ x, ← inv_mul_cancel₀ ht, mul_smul, div_eq_inv_mul, mul_smul, ← smul_add, hst, smul_zero]`.

Set `b` to `basisOfLinearIndependentOfCardEqFinrank li (by simp [hK])`. Establish `hb : ⇑b = ![(1 : K), x]` using `coe_basisOfLinearIndependentOfCardEqFinrank _ _`. Use `set A := b.repr (x ^ 2) 0`. Use `set B := b.repr (x ^ 2) 1`. Establish `hx2 : x ^ 2 = A • (1 : K) + B • x` using `by conv_lhs => rw [← b.sum_repr (x ^ 2)]`.

Simplify using `[Fin.sum_univ_two, hb, A, B]`. Establish `hrx : b.repr x = Finsupp.single 1 1`. Rewrite using `[show x = b 1 by simp [hb]]`. Conclude with `b.repr_self 1`. Establish `t1 : Algebra.trace ℚ K 1 = 2`.

Use `Algebra.trace_algebraMap (R := ℚ) (S := K) 1` as an intermediate fact. Simplify `this` using `[hK]`. Establish `tx : Algebra.trace ℚ K x = B`. Rewrite using `[Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]`. Simplify using `[hb, hrx, ← sq, B]`.

Establish `tx2 : Algebra.trace ℚ K (x ^ 2) = 2 * A + B ^ 2`. Rewrite using `[hx2, map_add, map_smul, map_smul, t1, tx]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `db : Algebra.discr ℚ b = 4 * A + B ^ 2`.

Rewrite using `[Algebra.discr_def, Matrix.det_fin_two]`. Simplify using `[Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb, t1, tx, tx2, ← sq]`. Expand and normalize the polynomial expressions, which then agree. Set `I` to `integralBasis K`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2`.

Rewrite using `[← Module.finrank_eq_card_basis I, hK]`. Set `e` to `Fintype.equivFinOfCardEq hcard`. Set `c` to `b.reindex e.symm`. Set `P` to `c.toMatrix I`. Establish `hI : Algebra.discr ℚ I = P.det ^ 2 * Algebra.discr ℚ b`.

Establish `h1 : Matrix.vecMul (⇑c) (P.map (algebraMap ℚ K)) = ⇑I` using `c.toMatrix_map_vecMul I`. Rewrite using `[← h1, Algebra.discr_of_matrix_vecMul]`. Use `congr 1`. Rewrite using `[Module.Basis.coe_reindex]`. Conclude with `Algebra.discr_reindex ℚ b e.symm`.

Establish `key : ((Algebra.discr ℚ I : ℚ) : K) = -(d : K)`. Rewrite using `[← coe_discr, hKd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(P.det : K) * (2 * x - B), ?_⟩` and prove the remaining obligations.

Rewrite using `[← key, hI, db]`. Simplify using `only [Rat.smul_def, mul_one] at hx2`. Simplify using `only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat]`. Take the linear combination `(4 * (P.det : K) ^ 2) * hx2`.
-/
private theorem exists_sq_eq_neg_of_quadratic_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hKd : discr K = -(d : ℤ)) : ∃ δ : K, δ ^ 2 = -(d : K) := by
  obtain ⟨x, hx⟩ : ∃ x : K, ∀ c : ℚ, c • (1 : K) ≠ x := by
    by_contra h
    push_neg at h
    have := (finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero).2 h
    omega
  have li : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hx (-(s / t))
      rw [neg_smul, neg_eq_iff_add_eq_zero, ← one_smul ℚ x, ← inv_mul_cancel₀ ht, mul_smul, div_eq_inv_mul, mul_smul, ← smul_add, hst, smul_zero]
  let b := basisOfLinearIndependentOfCardEqFinrank li (by simp [hK])
  have hb : ⇑b = ![(1 : K), x] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  set A := b.repr (x ^ 2) 0
  set B := b.repr (x ^ 2) 1
  have hx2 : x ^ 2 = A • (1 : K) + B • x := by
    conv_lhs => rw [← b.sum_repr (x ^ 2)]
    simp [Fin.sum_univ_two, hb, A, B]
  have hrx : b.repr x = Finsupp.single 1 1 := by
    rw [show x = b 1 by simp [hb]]
    exact b.repr_self 1
  have t1 : Algebra.trace ℚ K 1 = 2 := by
    have := Algebra.trace_algebraMap (R := ℚ) (S := K) 1
    simpa [hK] using this
  have tx : Algebra.trace ℚ K x = B := by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul]
    simp [hb, hrx, ← sq, B]
  have tx2 : Algebra.trace ℚ K (x ^ 2) = 2 * A + B ^ 2 := by
    rw [hx2, map_add, map_smul, map_smul, t1, tx]
    simp
    ring
  have db : Algebra.discr ℚ b = 4 * A + B ^ 2 := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb, t1, tx, tx2, ← sq]
    ring
  classical
  let I := integralBasis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis I, hK]
  let e := Fintype.equivFinOfCardEq hcard
  let c := b.reindex e.symm
  let P := c.toMatrix I
  have hI : Algebra.discr ℚ I = P.det ^ 2 * Algebra.discr ℚ b := by
    have h1 : Matrix.vecMul (⇑c) (P.map (algebraMap ℚ K)) = ⇑I := c.toMatrix_map_vecMul I
    rw [← h1, Algebra.discr_of_matrix_vecMul]
    congr 1
    rw [Module.Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ b e.symm
  have key : ((Algebra.discr ℚ I : ℚ) : K) = -(d : K) := by
    rw [← coe_discr, hKd]
    push_cast
    ring
  refine ⟨(P.det : K) * (2 * x - B), ?_⟩
  rw [← key, hI, db]
  simp only [Rat.smul_def, mul_one] at hx2
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat]
  linear_combination (4 * (P.det : K) ^ 2) * hx2

/- English proof (translation)
Establish `hs` using `NumberField.sign_discr (K := K)`. Rewrite `hs` using `[hKd]`. Establish `hneg : (-(d : ℤ)).sign = -1` using `Int.sign_eq_neg_one_of_neg (by omega)`. Rewrite `hs` using `[hneg, eq_comm, neg_one_pow_eq_neg_one_iff_odd (by decide)]`. Take `⟨k, hk⟩` from `hs`.

Establish `hr` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K`. Rewrite `hr` using `[hK]`. Apply `NumberField.nrRealPlaces_eq_zero_iff.mp` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
private theorem isTotallyComplex_of_quadratic_neg_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hd : d ≠ 0) (hKd : discr K = -(d : ℤ)) : IsTotallyComplex K := by
  have hs := NumberField.sign_discr (K := K)
  rw [hKd] at hs
  have hneg : (-(d : ℤ)).sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
  rw [hneg, eq_comm, neg_one_pow_eq_neg_one_iff_odd (by decide)] at hs
  obtain ⟨k, hk⟩ := hs
  have hr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hK] at hr
  apply NumberField.nrRealPlaces_eq_zero_iff.mp
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_sq_eq_neg_of_quadratic_discr hK hKd, isTotallyComplex_of_quadratic_neg_discr hK hd hKd⟩`.
-/
theorem exists_sq_eq_neg_of_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hd : d ≠ 0) (hKd : discr K = -(d : ℤ)) :
    (∃ δ : K, δ ^ 2 = -(d : K)) ∧ IsTotallyComplex K := ⟨exists_sq_eq_neg_of_quadratic_discr hK hKd, isTotallyComplex_of_quadratic_neg_discr hK hd hKd⟩

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps : DirichletCharacter ℂ N}
  {Y : Subgroup (DirichletCharacter ℂ N)}
  {L : Type} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]

end KStar.Choice
