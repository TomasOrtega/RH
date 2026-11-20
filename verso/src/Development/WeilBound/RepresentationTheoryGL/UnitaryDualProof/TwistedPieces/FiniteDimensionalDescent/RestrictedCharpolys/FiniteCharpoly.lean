import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
import Mathlib
import GroundTheory.AutomorphicForms.StableConjInvariant
import GroundTheory.LocalFields.Interface

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

/- English proof (translation)
Establish `hinf : Infinite k`. Take `⟨r, hr0, hr1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)`. Assume the negation of the conclusion as `hfin`. Rewrite `hfin` using `[not_infinite_iff_finite]`. Use `haveI := Fintype.ofFinite k`.

Establish `hr : r ≠ 0` using `by simpa using hr0`. Establish `h1` using `FiniteField.pow_card_sub_one_eq_one r hr`. Establish `h2` using `congrArg (ValuativeRel.valuation k) h1`. Rewrite `h2` using `[map_pow, map_one]`. Establish `hc : Fintype.card k - 1 ≠ 0`.

Use `Fintype.one_lt_card (α := k)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `(pow_lt_one₀ zero_le' hr1 hc).ne h2`. Use `haveI : Nontrivial (Matrix (Fin N) (Fin N) k) := by haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩ infer_instance`. Set `f : k →+* Matrix (Fin N) (Fin N) k` to `φ.comp (algebraMap k _)`.

Establish `hfinj : Function.Injective f` using `f.injective`. Establish `hfq : ∀ a : k, f (a ^ q) = algebraMap k _ a` using `fun a => hd.scal a`. Establish `hq : 1 ≤ q`. Assume the negation of the conclusion as `h`. Establish `h0 : q = 0` using `by omega`.

Establish `h3` using `hfq 0`. Rewrite `h3` using `[h0, pow_zero, map_one, map_zero]`. Conclude with `one_ne_zero h3`. Establish `hadd : ∀ a b : k, (a + b) ^ q = a ^ q + b ^ q`. Introduce `a b`.

Apply `hfinj` to reduce the goal to its premises. Rewrite using `[hfq, map_add, map_add, hfq, hfq]`. Use `⟨hq, fun i hi1 hi2 => ?_⟩` and prove the remaining obligations. Establish `hP : ((X + 1 : k[X]) ^ q - X ^ q - 1) = 0`. Apply `Polynomial.funext` to reduce the goal to its premises.

Introduce `a`. Simplify using `[hadd a 1]`. Establish `h4` using `congrArg (fun p => p.coeff i) hP`. Establish `hi0 : i ≠ 0` using `by omega`. Establish `hiq : i ≠ q` using `by omega`.

Simplify `h4` using `[coeff_X_add_one_pow, coeff_X_pow, coeff_one, hi0, hiq, Ne.symm hi0]`.
-/
theorem choose_zero (hd : PhiData q Z Z' φ e) (hN : 0 < N) :
    1 ≤ q ∧ ∀ i, 0 < i → i < q → (q.choose i : k) = 0 := by
  have hinf : Infinite k := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    classical
    haveI := Fintype.ofFinite k
    have hr : r ≠ 0 := by simpa using hr0
    have h1 := FiniteField.pow_card_sub_one_eq_one r hr
    have h2 := congrArg (ValuativeRel.valuation k) h1
    rw [map_pow, map_one] at h2
    have hc : Fintype.card k - 1 ≠ 0 := by
      have := Fintype.one_lt_card (α := k)
      omega
    exact (pow_lt_one₀ zero_le' hr1 hc).ne h2
  haveI : Nontrivial (Matrix (Fin N) (Fin N) k) := by
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    infer_instance
  let f : k →+* Matrix (Fin N) (Fin N) k := φ.comp (algebraMap k _)
  have hfinj : Function.Injective f := f.injective
  have hfq : ∀ a : k, f (a ^ q) = algebraMap k _ a := fun a => hd.scal a
  have hq : 1 ≤ q := by
    by_contra h
    have h0 : q = 0 := by omega
    have h3 := hfq 0
    rw [h0, pow_zero, map_one, map_zero] at h3
    exact one_ne_zero h3
  have hadd : ∀ a b : k, (a + b) ^ q = a ^ q + b ^ q := by
    intro a b
    apply hfinj
    rw [hfq, map_add, map_add, hfq, hfq]
  refine ⟨hq, fun i hi1 hi2 => ?_⟩
  have hP : ((X + 1 : k[X]) ^ q - X ^ q - 1) = 0 := by
    apply Polynomial.funext
    intro a
    simp [hadd a 1]
  have h4 := congrArg (fun p => p.coeff i) hP
  have hi0 : i ≠ 0 := by omega
  have hiq : i ≠ q := by omega
  simpa [coeff_X_add_one_pow, coeff_X_pow, coeff_one, hi0, hiq, Ne.symm hi0] using h4

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (by omega)]`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, ← ih]`. Establish `hc' : Commute (a j) (∑ i ∈ s, a i)` using `Commute.sum_right _ _ _ fun i _ => hcomm j i`.

Rewrite using `[hc'.add_pow, Finset.sum_eq_add q 0 (by omega)]`. Simplify using the standard rewrite rules. Introduce `m hm hm'`. Rewrite using `[hc m (by omega) (by have := Finset.mem_range.1 hm; omega), mul_zero]`. Introduce `h`.

Simplify using `at h`. Introduce `h`. Simplify using `at h`.
-/
theorem pow_sum {R : Type*} [Ring R] {q : ℕ} (hq : 1 ≤ q) (hc : ∀ i, 0 < i → i < q → (q.choose i : R) = 0)
    {ι : Type*} (s : Finset ι) (a : ι → R) (hcomm : ∀ i j, Commute (a i) (a j)) :
    (∑ i ∈ s, a i) ^ q = ∑ i ∈ s, a i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (by omega)]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    have hc' : Commute (a j) (∑ i ∈ s, a i) := Commute.sum_right _ _ _ fun i _ => hcomm j i
    rw [hc'.add_pow, Finset.sum_eq_add q 0 (by omega)]
    · simp
    · intro m hm hm'
      rw [hc m (by omega) (by have := Finset.mem_range.1 hm; omega), mul_zero]
    · intro h
      simp at h
    · intro h
      simp at h

/- English proof (translation)
Take `⟨hq, hc⟩` from `choose_zero hd hN`. Establish `hcM : ∀ i, 0 < i → i < q → (q.choose i : Matrix (Fin N) (Fin N) k) = 0`. Introduce `i h1 h2`. Rewrite using `[← map_natCast (algebraMap k (Matrix (Fin N) (Fin N) k)), hc i h1 h2, map_zero]`. Establish `hsum : φ (aeval x χ) = ∑ i ∈ Finset.range (χ.natDegree + 1), φ (χ.coeff i • x ^ i)`.

Rewrite using `[aeval_eq_sum_range, map_sum]`. Rewrite `hsum` using `[hx, map_zero]`. Establish `hp` using `pow_sum hq hcM (Finset.range (χ.natDegree + 1)) (fun i => φ (χ.coeff i • x ^ i)) (fun i j => (((Commute.pow_pow_self x i j).smul_left _).smul_right _).map φ)`. Use `beta_reduce at hp`. Rewrite `hp` using `[← hsum, zero_pow (by omega)]`.

Rewrite using `[expand_aeval, aeval_eq_sum_range, hp]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← map_pow φ (χ.coeff i • x ^ i) q, _root_.smul_pow, ← pow_mul, ← pow_mul, Algebra.smul_def, Algebra.smul_def, map_mul, hd.scal, map_pow, mul_comm q i]`.
-/
theorem aeval_expand (hd : PhiData q Z Z' φ e) (hN : 0 < N) (χ : k[X]) (x : Matrix (Fin n) (Fin n) k)
    (hx : aeval x χ = 0) : aeval (φ x) (expand k q χ) = 0 := by
  obtain ⟨hq, hc⟩ := choose_zero hd hN
  have hcM : ∀ i, 0 < i → i < q → (q.choose i : Matrix (Fin N) (Fin N) k) = 0 := by
    intro i h1 h2
    rw [← map_natCast (algebraMap k (Matrix (Fin N) (Fin N) k)), hc i h1 h2, map_zero]
  have hsum : φ (aeval x χ) = ∑ i ∈ Finset.range (χ.natDegree + 1), φ (χ.coeff i • x ^ i) := by
    rw [aeval_eq_sum_range, map_sum]
  rw [hx, map_zero] at hsum
  have hp := pow_sum hq hcM (Finset.range (χ.natDegree + 1)) (fun i => φ (χ.coeff i • x ^ i))
    (fun i j => (((Commute.pow_pow_self x i j).smul_left _).smul_right _).map φ)
  beta_reduce at hp
  rw [← hsum, zero_pow (by omega)] at hp
  rw [expand_aeval, aeval_eq_sum_range, hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow φ (χ.coeff i • x ^ i) q, _root_.smul_pow, ← pow_mul, ← pow_mul, Algebra.smul_def,
    Algebra.smul_def, map_mul, hd.scal, map_pow, mul_comm q i]

/- English proof (translation)
Use `⟨∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • ∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j), ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_sub, smul_mul_assoc, h.geom_sum₂_mul]`.
-/
private theorem sub_dvd_lemma {R : Type*} [Ring R] [Algebra k R] (P : k[X]) (x y : R) (h : Commute x y) :
    ∃ Q : R, aeval x P - aeval y P = Q * (x - y) := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • ∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j), ?_⟩
  rw [aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, smul_mul_assoc, h.geom_sum₂_mul]

/- English proof (translation)
Set `F` to `Polynomial.fintypeSubtypeMonicDvd (P ^ N) (pow_ne_zero N hP)`. Use `⟨((@Finset.univ _ F).image Subtype.val).toList, Finset.nodup_toList _, fun A hA => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_toList, Finset.mem_image]`. Use `⟨⟨A.charpoly, A.charpoly_monic, ?_⟩, Finset.mem_univ _, rfl⟩` and prove the remaining obligations. Set `ψ` to `(Algebra.ofId k k[X]).mapMatrix (m := Fin N)`.

Set `T : Matrix (Fin N) (Fin N) k[X]` to `algebraMap k[X] _ X`. Take `⟨Q, hQ⟩` from `sub_dvd_lemma P T (ψ A) (Algebra.commute_algebraMap_left X (ψ A))`. Establish `h1 : aeval (ψ A) P = 0` using `by rw [aeval_algHom_apply, hA, map_zero]`. Establish `h2 : aeval T P = algebraMap k[X] _ P`. Rewrite using `[aeval_algebraMap_apply, aeval_X_left_apply]`.

Establish `h3 : T - ψ A = charmatrix A`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply]`.

Simplify using `[T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply, hij]`. Rewrite `hQ` using `[h1, h2, sub_zero, h3]`. Establish `h4` using `congrArg Matrix.det hQ`. Rewrite `h4` using `[det_mul, Matrix.algebraMap_eq_diagonal]`. Simplify using `only [det_diagonal] at h4`.

Simplify using `at h4`. Conclude with `⟨Q.det, by rw [h4, mul_comm]; rfl⟩`.
-/
theorem finite_charpoly (N : ℕ) (P : k[X]) (hP : P ≠ 0) :
    ∃ l : List k[X], l.Nodup ∧ ∀ A : Matrix (Fin N) (Fin N) k, aeval A P = 0 → A.charpoly ∈ l := by
  classical
  let F := Polynomial.fintypeSubtypeMonicDvd (P ^ N) (pow_ne_zero N hP)
  refine ⟨((@Finset.univ _ F).image Subtype.val).toList, Finset.nodup_toList _, fun A hA => ?_⟩
  rw [Finset.mem_toList, Finset.mem_image]
  refine ⟨⟨A.charpoly, A.charpoly_monic, ?_⟩, Finset.mem_univ _, rfl⟩
  let ψ := (Algebra.ofId k k[X]).mapMatrix (m := Fin N)
  let T : Matrix (Fin N) (Fin N) k[X] := algebraMap k[X] _ X
  obtain ⟨Q, hQ⟩ := sub_dvd_lemma P T (ψ A) (Algebra.commute_algebraMap_left X (ψ A))
  have h1 : aeval (ψ A) P = 0 := by rw [aeval_algHom_apply, hA, map_zero]
  have h2 : aeval T P = algebraMap k[X] _ P := by
    rw [aeval_algebraMap_apply, aeval_X_left_apply]
  have h3 : T - ψ A = charmatrix A := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply]
    · simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply, hij]
  rw [h1, h2, sub_zero, h3] at hQ
  have h4 := congrArg Matrix.det hQ
  rw [det_mul, Matrix.algebraMap_eq_diagonal] at h4
  simp only [det_diagonal] at h4
  simp at h4
  exact ⟨Q.det, by rw [h4, mul_comm]; rfl⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A
