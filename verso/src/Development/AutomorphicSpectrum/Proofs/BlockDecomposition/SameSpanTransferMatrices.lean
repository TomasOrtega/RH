import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCoeffs

/- English proof (translation)
Establish `hT0 : ∀ j, ∃ t : Fin r → K, ∑ i, t i • c i = C j`. Introduce `j`. Establish `hj : C j ∈ Submodule.span K (Set.range c)`. Rewrite using `[hs]`. Conclude with `Submodule.subset_span (Set.mem_range_self j)`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun K).mp hj`. Establish `hL0 : ∀ i, ∃ t : Fin n → K, ∑ j, t j • C j = c i`. Introduce `i`. Establish `hi : c i ∈ Submodule.span K (Set.range C)`. Rewrite using `[← hs]`.

Conclude with `Submodule.subset_span (Set.mem_range_self i)`. Conclude with `(Submodule.mem_span_range_iff_exists_fun K).mp hi`. Take `⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin r) K, ∀ j, ∑ i, T j i • c i = C j` from `⟨fun j => (hT0 j).choose, fun j => (hT0 j).choose_spec⟩`. Take `⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) K, ∀ i, ∑ j, L i j • C j = c i` from `⟨fun i => (hL0 i).choose, fun i => (hL0 i).choose_spec⟩`. Establish `hCT : C = T * c`.

Use extensionality with `j k`. Rewrite using `[← hT j, Matrix.mul_apply]`. Simplify using `[Finset.sum_apply]`. Establish `hcL : c = L * C`. Use extensionality with `i k`.

Rewrite using `[← hL i, Matrix.mul_apply]`. Simplify using `[Finset.sum_apply]`. Use `⟨T, L, hCT, hcL, ?_⟩` and prove the remaining obligations. Establish `hLT : L * T * c = c` using `by rw [Matrix.mul_assoc, ← hCT, ← hcL]`. Establish `hz0 : (L * T - 1) * c = 0` using `by rw [Matrix.sub_mul, hLT, Matrix.one_mul, sub_self]`.

Establish `hc'` using `Fintype.linearIndependent_iff.mp hc`. Use extensionality with `i0 i`. Establish `hrow : ∑ i, (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i • c i = 0`. Use function extensionality and compare the values at `k`. Establish `h0` using `congrFun (congrFun hz0 i0) k`.

Rewrite `h0` using `[Matrix.mul_apply]`. Simplify `h0` using `[Finset.sum_apply]`. Establish `h1 : (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i = 0` using `hc' (fun i => (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i) hrow i`. Rewrite `h1` using `[Matrix.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem exists_coeff_matrices_of_span_eq {K : Type} [Field K] {n r : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c)
    (hs : Submodule.span K (Set.range c) = Submodule.span K (Set.range C)) :
    ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
      C = T * c ∧ c = L * C ∧ L * T = 1 := by
  have hT0 : ∀ j, ∃ t : Fin r → K, ∑ i, t i • c i = C j := by
    intro j
    have hj : C j ∈ Submodule.span K (Set.range c) := by
      rw [hs]
      exact Submodule.subset_span (Set.mem_range_self j)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hj
  have hL0 : ∀ i, ∃ t : Fin n → K, ∑ j, t j • C j = c i := by
    intro i
    have hi : c i ∈ Submodule.span K (Set.range C) := by
      rw [← hs]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hi
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin r) K, ∀ j, ∑ i, T j i • c i = C j :=
    ⟨fun j => (hT0 j).choose, fun j => (hT0 j).choose_spec⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) K, ∀ i, ∑ j, L i j • C j = c i :=
    ⟨fun i => (hL0 i).choose, fun i => (hL0 i).choose_spec⟩
  have hCT : C = T * c := by
    ext j k
    rw [← hT j, Matrix.mul_apply]
    simp [Finset.sum_apply]
  have hcL : c = L * C := by
    ext i k
    rw [← hL i, Matrix.mul_apply]
    simp [Finset.sum_apply]
  refine ⟨T, L, hCT, hcL, ?_⟩
  have hLT : L * T * c = c := by rw [Matrix.mul_assoc, ← hCT, ← hcL]
  have hz0 : (L * T - 1) * c = 0 := by rw [Matrix.sub_mul, hLT, Matrix.one_mul, sub_self]
  have hc' := Fintype.linearIndependent_iff.mp hc
  ext i0 i
  have hrow : ∑ i, (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i • c i = 0 := by
    funext k
    have h0 := congrFun (congrFun hz0 i0) k
    rw [Matrix.mul_apply] at h0
    simpa [Finset.sum_apply] using h0
  have h1 : (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i = 0 := hc' (fun i => (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i) hrow i
  rwa [Matrix.sub_apply, sub_eq_zero] at h1

end GlobalTheory.CompanionTheory.BruhatCoeffs
