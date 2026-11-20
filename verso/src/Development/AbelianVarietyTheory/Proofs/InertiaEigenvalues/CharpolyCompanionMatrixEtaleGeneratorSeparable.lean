import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

/- English proof (translation)
Introduce `F E _ _ _ _ hU A r τ p hG`. Use `haveI : CharZero F := hU.charZero`. Use `set P := (companion p).charpoly with hP`. Establish `hmon : P.Monic` using `Matrix.charpoly_monic _`. Establish `hdeg : P.natDegree = r` using `by rw [hP, Matrix.charpoly_natDegree_eq_dim]; simp`.

Establish `hroot : Polynomial.aeval τ P = 0`. Apply `Algebra.leftMulMatrix_injective (bas A hG)` to reduce the goal to its premises. Rewrite using `[map_zero, ← Polynomial.aeval_algHom_apply, leftMul_tau A hG]`. Conclude with `Matrix.aeval_self_charpoly _`. Establish `hsmall : ∀ Q : Polynomial F, Q.natDegree < r → Polynomial.aeval τ Q = 0 → Q = 0`.

Introduce `Q hQ h0`. Rewrite `h0` using `[Polynomial.aeval_eq_sum_range' hQ]`. Rewrite `h0` using `[← Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • τ ^ i) r]`. Use `Fintype.linearIndependent_iff.mp hG.1 (fun i => Q.coeff i) h0` as an intermediate fact. Use extensionality with `n`.

Distinguish the cases in `hn : n < r`. Simplify using `using this ⟨n, hn⟩`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp`. Rewrite using `[PerfectField.separable_iff_squarefree]`. Introduce `q hq`.

Take `⟨s, hs⟩` from `hq`. Assume the negation of the conclusion as `hqu`. Establish `hP0 : P ≠ 0` using `hmon.ne_zero`. Establish `hq0 : q ≠ 0` using `by rintro rfl; simp at hs; exact hP0 hs`. Establish `hs0 : s ≠ 0` using `by rintro rfl; simp at hs; exact hP0 hs`.

Establish `hqdeg : 0 < q.natDegree` using `Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_ne_zero_of_nonunit hq0 hqu)`. Establish `hQ0 : q * s ≠ 0` using `mul_ne_zero hq0 hs0`. Establish `hdegQ : (q * s).natDegree < r`. Establish `: P.natDegree = q.natDegree + (q * s).natDegree`. Rewrite using `[hs, mul_assoc, Polynomial.natDegree_mul hq0 hQ0]`.

Use linear arithmetic over natural numbers and integers. Apply `hQ0` to reduce the goal to its premises. Apply `hsmall _ hdegQ` to reduce the goal to its premises. Establish `hnil : IsNilpotent (Polynomial.aeval τ (q * s))` using `⟨2, by`. Rewrite using `[pow_two, ← map_mul]`.

Establish `: q * s * (q * s) = P * s` using `by rw [hs]; ring`. Rewrite using `[this, map_mul, hroot, zero_mul]⟩`. Conclude with `hnil.eq_zero`.
-/
theorem charpoly_companion_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F),
    A.IsGen τ p → (companion p).charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : CharZero F := hU.charZero
  set P := (companion p).charpoly with hP
  have hmon : P.Monic := Matrix.charpoly_monic _
  have hdeg : P.natDegree = r := by rw [hP, Matrix.charpoly_natDegree_eq_dim]; simp
  have hroot : Polynomial.aeval τ P = 0 := by
    apply Algebra.leftMulMatrix_injective (bas A hG)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, leftMul_tau A hG]
    exact Matrix.aeval_self_charpoly _
  have hsmall : ∀ Q : Polynomial F, Q.natDegree < r → Polynomial.aeval τ Q = 0 → Q = 0 := by
    intro Q hQ h0
    rw [Polynomial.aeval_eq_sum_range' hQ] at h0
    rw [← Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • τ ^ i) r] at h0
    have := Fintype.linearIndependent_iff.mp hG.1 (fun i => Q.coeff i) h0
    ext n
    by_cases hn : n < r
    · simpa using this ⟨n, hn⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  rw [PerfectField.separable_iff_squarefree]
  intro q hq
  obtain ⟨s, hs⟩ := hq
  by_contra hqu
  have hP0 : P ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hqdeg : 0 < q.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_ne_zero_of_nonunit hq0 hqu)
  have hQ0 : q * s ≠ 0 := mul_ne_zero hq0 hs0
  have hdegQ : (q * s).natDegree < r := by
    have : P.natDegree = q.natDegree + (q * s).natDegree := by
      rw [hs, mul_assoc, Polynomial.natDegree_mul hq0 hQ0]
    omega
  apply hQ0
  apply hsmall _ hdegQ
  have hnil : IsNilpotent (Polynomial.aeval τ (q * s)) := ⟨2, by
    rw [pow_two, ← map_mul]
    have : q * s * (q * s) = P * s := by rw [hs]; ring
    rw [this, map_mul, hroot, zero_mul]⟩
  exact hnil.eq_zero

end GlobalTheory.JR.LinDesc
