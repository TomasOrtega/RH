import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.IsoOfTrace

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Alg.Trall

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable (k : Type) [Field k] [CharZero k]

/- English proof (translation)
Establish `h : trace (z * x ^ m * aeval x p) = 0` using `by rw [hp, mul_zero, trace_zero]`. Rewrite `h` using `[aeval_eq_sum_range, Finset.mul_sum, trace_sum]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, trace_smul, smul_eq_mul, mul_assoc, ← pow_add]`.
-/
theorem sum_coeff_trace {n : ℕ} (x z : Matrix (Fin n) (Fin n) k) (p : k[X]) (hp : aeval x p = 0) (m : ℕ) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * trace (z * x ^ (m + i)) = 0 := by
  have h : trace (z * x ^ m * aeval x p) = 0 := by rw [hp, mul_zero, trace_zero]
  rw [aeval_eq_sum_range, Finset.mul_sum, trace_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, trace_smul, smul_eq_mul, mul_assoc, ← pow_add]

/- English proof (translation)
Introduce `n Z x x' h z hz j`. Establish `key : ∀ w : Z, ∀ j, j < 2 * n + 1 → trace ((w : Matrix (Fin n) (Fin n) k) * x ^ j) = trace ((w : Matrix (Fin n) (Fin n) k) * x' ^ j)`. Introduce `w j hj`. Establish `hw : (w : Matrix (Fin n) (Fin n) k) = ∑ i, (Module.finBasis k Z).repr w i • ((Module.finBasis k Z) i : Matrix (Fin n) (Fin n) k)` using `by nth_rewrite 1 [← (Module.finBasis k Z).sum_repr w]`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]`.

Rewrite using `[hw, Finset.sum_mul, Finset.sum_mul, trace_sum, trace_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul]`. Use `congr 1`. Conclude with `congrFun h (⟨j, hj⟩, i)`.

Use `set q := x.charpoly * x'.charpoly with hqdef`. Establish `hqm : q.Monic` using `x.charpoly_monic.mul x'.charpoly_monic`. Establish `hdeg : q.natDegree = 2 * n`. Rewrite using `[hqdef, x.charpoly_monic.natDegree_mul x'.charpoly_monic, charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hx0 : aeval x q = 0` using `by rw [hqdef, map_mul, aeval_self_charpoly, zero_mul]`. Establish `hx'0 : aeval x' q = 0` using `by rw [hqdef, map_mul, aeval_self_charpoly, mul_zero]`. Establish `hrec : ∀ m, ∑ i ∈ Finset.range (2 * n + 1), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0`. Introduce `m`. Establish `h1` using `sum_coeff_trace k x z q hx0 m`.

Establish `h2` using `sum_coeff_trace k x' z q hx'0 m`. Rewrite `h1`, `h2` using `[hdeg]`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]`. Establish `hlead : q.coeff (2 * n) = 1`. Rewrite using `[← hdeg]`.

Conclude with `hqm`. It suffices to establish `hall : ∀ j, trace (z * x ^ j) - trace (z * x' ^ j) = 0 from sub_eq_zero.mp (hall j)`. Introduce `j`. Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`.

Distinguish the cases in `hj : j < 2 * n + 1`. Conclude with `sub_eq_zero.mpr (key ⟨z, hz⟩ j hj)`. Take `⟨m, rfl⟩ : ∃ m, j = m + 2 * n` from `⟨j - 2 * n, by omega⟩`. Establish `hm` using `hrec m`. Rewrite `hm` using `[Finset.sum_range_succ, hlead, one_mul]`.

Establish `hs : ∑ i ∈ Finset.range (2 * n), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0` using `Finset.sum_eq_zero fun i hi => by`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[ih (m + i) (by omega), mul_zero]`. Rewrite `hm` using `[hs, zero_add]`. Conclude with `hm`.
-/
theorem trace_all_holds : TrAll k := by
  intro n Z x x' h z hz j
  have key : ∀ w : Z, ∀ j, j < 2 * n + 1 → trace ((w : Matrix (Fin n) (Fin n) k) * x ^ j) = trace ((w : Matrix (Fin n) (Fin n) k) * x' ^ j) := by
    intro w j hj
    have hw : (w : Matrix (Fin n) (Fin n) k) = ∑ i, (Module.finBasis k Z).repr w i • ((Module.finBasis k Z) i : Matrix (Fin n) (Fin n) k) := by
      nth_rewrite 1 [← (Module.finBasis k Z).sum_repr w]
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rw [hw, Finset.sum_mul, Finset.sum_mul, trace_sum, trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul]
    congr 1
    exact congrFun h (⟨j, hj⟩, i)
  set q := x.charpoly * x'.charpoly with hqdef
  have hqm : q.Monic := x.charpoly_monic.mul x'.charpoly_monic
  have hdeg : q.natDegree = 2 * n := by
    rw [hqdef, x.charpoly_monic.natDegree_mul x'.charpoly_monic, charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim, Fintype.card_fin]
    ring
  have hx0 : aeval x q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, zero_mul]
  have hx'0 : aeval x' q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, mul_zero]
  have hrec : ∀ m, ∑ i ∈ Finset.range (2 * n + 1), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 := by
    intro m
    have h1 := sum_coeff_trace k x z q hx0 m
    have h2 := sum_coeff_trace k x' z q hx'0 m
    rw [hdeg] at h1 h2
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have hlead : q.coeff (2 * n) = 1 := by
    rw [← hdeg]
    exact hqm
  suffices hall : ∀ j, trace (z * x ^ j) - trace (z * x' ^ j) = 0 from sub_eq_zero.mp (hall j)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 2 * n + 1
    · exact sub_eq_zero.mpr (key ⟨z, hz⟩ j hj)
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 * n := ⟨j - 2 * n, by omega⟩
      have hm := hrec m
      rw [Finset.sum_range_succ, hlead, one_mul] at hm
      have hs : ∑ i ∈ Finset.range (2 * n), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_range] at hi
          rw [ih (m + i) (by omega), mul_zero]
      rw [hs, zero_add] at hm
      exact hm

end PositivityTheory.RgUd.T.Alg.Trall
