import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference

open scoped NNReal

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

section Core

variable {C : Type} [Field C]

/- English proof (translation)
Use `⟨Matrix.vecMul f (Matrix.of U)⁻¹, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (Matrix.of U).det` using `isUnit_iff_ne_zero.mpr h`. Establish `key : Matrix.vecMul (Matrix.vecMul f (Matrix.of U)⁻¹) (Matrix.of U) = f`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]`. Use function extensionality and compare the values at `j`.

Use `conv_lhs => rw [← key]`. Simplify using `[Matrix.vecMul, dotProduct, Finset.sum_apply]`.
-/
theorem eq_sum_rows {n : ℕ} (U : Fin n → Fin n → C) (h : (Matrix.of U).det ≠ 0)
    (f : Fin n → C) : ∃ γ : Fin n → C, f = ∑ s, γ s • U s := by
  refine ⟨Matrix.vecMul f (Matrix.of U)⁻¹, ?_⟩
  have hu : IsUnit (Matrix.of U).det := isUnit_iff_ne_zero.mpr h
  have key : Matrix.vecMul (Matrix.vecMul f (Matrix.of U)⁻¹) (Matrix.of U) = f := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  funext j
  conv_lhs => rw [← key]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

/- English proof (translation)
Take `⟨γ, hγ⟩` from `eq_sum_rows _ hN f`. Rewrite `hγ` using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right] at hγ`. Establish `hz : ∑ i, γ (Fin.castAdd q i) • F.mkQ (u0 i) = 0`. Establish `h1` using `congrArg F.mkQ hγ`.

Establish `hf0 : F.mkQ f = 0` using `by simpa using hf`. Establish `hm : ∑ k, γ (Fin.natAdd p k) • F.mkQ (m0 k) = 0` using `Finset.sum_eq_zero fun k _ => by simp [hm0 k]`. Rewrite `h1` using `[hf0, map_add, map_sum, map_sum]`. Simplify using `only [map_smul] at h1`. Rewrite `h1` using `[hm, add_zero]`.

Conclude with `h1.symm`. Establish `h0` using `Fintype.linearIndependent_iff.1 hli _ hz`. Conclude with `⟨fun k => γ (Fin.natAdd p k), by rw [hγ]; simp [h0]⟩`.
-/
theorem exists_eq_sum_of_mem {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u0 : Fin p → Fin (p + q) → C) (m0 : Fin q → Fin (p + q) → C)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i)) (hm0 : ∀ k, m0 k ∈ F)
    (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) (f : Fin (p + q) → C) (hf : f ∈ F) :
    ∃ β : Fin q → C, f = ∑ k, β k • m0 k := by
  obtain ⟨γ, hγ⟩ := eq_sum_rows _ hN f
  rw [Fin.sum_univ_add] at hγ
  simp only [Fin.append_left, Fin.append_right] at hγ
  have hz : ∑ i, γ (Fin.castAdd q i) • F.mkQ (u0 i) = 0 := by
    have h1 := congrArg F.mkQ hγ
    have hf0 : F.mkQ f = 0 := by simpa using hf
    have hm : ∑ k, γ (Fin.natAdd p k) • F.mkQ (m0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hm0 k]
    rw [hf0, map_add, map_sum, map_sum] at h1
    simp only [map_smul] at h1
    rw [hm, add_zero] at h1
    exact h1.symm
  have h0 := Fintype.linearIndependent_iff.1 hli _ hz
  exact ⟨fun k => γ (Fin.natAdd p k), by rw [hγ]; simp [h0]⟩

/- English proof (translation)
Establish `hmem : ∀ i, u i - ∑ j, A i j • u0 j ∈ F`. Introduce `i`. Establish `: F.mkQ (u i - ∑ j, A i j • u0 j) = 0`. Rewrite using `[map_sub, map_sum, hu i]`. Simplify using `only [map_smul]`.

Conclude with `sub_self _`. Rewrite `this` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Use `choose β hβ using fun i => exists_eq_sum_of_mem F u0 m0 hli hm0 hN _ (hmem i)`. Establish `key : (Matrix.of (Fin.append u m)).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks A (Matrix.of β) 0 B * (Matrix.of (Fin.append u0 m0)).submatrix finSumFinEquiv finSumFinEquiv`. Use extensionality with `r c`.

Rewrite using `[Matrix.mul_apply, Fintype.sum_sum_type]`. Break down `r with i | k` into its components or cases. Establish `hi : u i = ∑ j, A i j • u0 j + ∑ k, β i k • m0 k` using `by rw [← hβ i]; abel`. Simplify using `[Matrix.fromBlocks, hi, Finset.sum_apply]`. Simplify using `[Matrix.fromBlocks, hm k, Finset.sum_apply]`.

Rewrite using `[← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_submatrix_equiv_self]`.
-/
theorem det_append_eq {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u u0 : Fin p → Fin (p + q) → C) (m m0 : Fin q → Fin (p + q) → C)
    (A : Matrix (Fin p) (Fin p) C) (B : Matrix (Fin q) (Fin q) C)
    (hu : ∀ i, F.mkQ (u i) = ∑ j, A i j • F.mkQ (u0 j))
    (hm : ∀ i, m i = ∑ j, B i j • m0 j)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i))
    (hm0 : ∀ k, m0 k ∈ F) (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) :
    (Matrix.of (Fin.append u m)).det = A.det * B.det * (Matrix.of (Fin.append u0 m0)).det := by
  have hmem : ∀ i, u i - ∑ j, A i j • u0 j ∈ F := by
    intro i
    have : F.mkQ (u i - ∑ j, A i j • u0 j) = 0 := by
      rw [map_sub, map_sum, hu i]; simp only [map_smul]; exact sub_self _
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  choose β hβ using fun i => exists_eq_sum_of_mem F u0 m0 hli hm0 hN _ (hmem i)
  have key : (Matrix.of (Fin.append u m)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A (Matrix.of β) 0 B *
        (Matrix.of (Fin.append u0 m0)).submatrix finSumFinEquiv finSumFinEquiv := by
    ext r c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | k
    · have hi : u i = ∑ j, A i j • u0 j + ∑ k, β i k • m0 k := by rw [← hβ i]; abel
      simp [Matrix.fromBlocks, hi, Finset.sum_apply]
    · simp [Matrix.fromBlocks, hm k, Finset.sum_apply]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_submatrix_equiv_self]

/- English proof (translation)
Introduce `i`. Simplify using `only [hc i, hb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem comp_sum {W : Type} [AddCommGroup W] [Module C W] {n k l : ℕ} (a : Fin n → W)
    (b : Fin k → W) (c : Fin l → W) (P : Matrix (Fin k) (Fin n) C)
    (Q : Matrix (Fin l) (Fin k) C) (hb : ∀ i, b i = ∑ j, P i j • a j)
    (hc : ∀ i, c i = ∑ j, Q i j • b j) : ∀ i, c i = ∑ j, (Q * P) i j • a j := by
  intro i
  simp only [hc i, hb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

end Core

section Lattice

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

/- English proof (translation)
Use `choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1 (h i)`. Conclude with `⟨Matrix.of P, fun i => by`. Rewrite using `[← hP i]`. Conclude with `Finset.sum_congr rfl fun j _ => (algebraMap_smul C (P i j) (a j)).symm⟩`.
-/
theorem coeffs {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n k : ℕ} (a : Fin n → W) (b : Fin k → W)
    (h : ∀ i, b i ∈ Submodule.span w.valuationSubring (Set.range a)) :
    ∃ P : Matrix (Fin k) (Fin n) w.valuationSubring,
      ∀ i, b i = ∑ j, algebraMap w.valuationSubring C (P i j) • a j := by
  choose P hP using fun i =>
    (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1 (h i)
  exact ⟨Matrix.of P, fun i => by
    rw [← hP i]; exact Finset.sum_congr rfl fun j _ => (algebraMap_smul C (P i j) (a j)).symm⟩

/- English proof (translation)
Rewrite using `[ha.2, ← hb.2]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.
-/
theorem mem_span_of_isLatticeBasis {W : Type} [AddCommGroup W] [Module C W]
    [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] {n k : ℕ}
    {a : Fin n → W} {b : Fin k → W} {Y : Submodule w.valuationSubring W}
    (ha : IsLatticeBasis w a Y) (hb : IsLatticeBasis w b Y) (i : Fin k) :
    b i ∈ Submodule.span w.valuationSubring (Set.range a) := by
  rw [ha.2, ← hb.2]; exact Submodule.subset_span ⟨i, rfl⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `coeffs a b (mem_span_of_isLatticeBasis ha hb)`. Take `⟨Q, hQ⟩` from `coeffs b a (mem_span_of_isLatticeBasis hb ha)`. Establish `hQP` using `comp_sum a b a (P.map (algebraMap w.valuationSubring C)) (Q.map (algebraMap w.valuationSubring C)) hP hQ`. Establish `hone : (Q.map (algebraMap w.valuationSubring C)) * (P.map (algebraMap w.valuationSubring C)) = 1`. Use extensionality with `i j`.

Establish `h` using `Fintype.linearIndependent_iff.1 ha.1 (fun j => ((Q.map (algebraMap w.valuationSubring C)) * (P.map (algebraMap w.valuationSubring C))) i j - (1 : Matrix (Fin n) (Fin n) C) i j) (by`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hQP i]`. Simplify using `[Matrix.one_apply])`. Use `j`.

Conclude with `sub_eq_zero.1 h`. Establish `hdet` using `congrArg Matrix.det hone`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_one]`. Establish `hle : ∀ R : Matrix (Fin n) (Fin n) w.valuationSubring, w (R.map (algebraMap w.valuationSubring C)).det ≤ 1`. Introduce `R`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, ValuationSubring.algebraMap_apply]`. Conclude with `(w.mem_valuationSubring_iff _).1 R.det.2`. Use `⟨P.map (algebraMap w.valuationSubring C), fun i => hP i, le_antisymm (hle P) ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem transition {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (a b : Fin n → W)
    (Y : Submodule w.valuationSubring W) (ha : IsLatticeBasis w a Y)
    (hb : IsLatticeBasis w b Y) :
    ∃ P : Matrix (Fin n) (Fin n) C, (∀ i, b i = ∑ j, P i j • a j) ∧ w P.det = 1 := by
  obtain ⟨P, hP⟩ := coeffs a b (mem_span_of_isLatticeBasis ha hb)
  obtain ⟨Q, hQ⟩ := coeffs b a (mem_span_of_isLatticeBasis hb ha)
  have hQP := comp_sum a b a (P.map (algebraMap w.valuationSubring C))
    (Q.map (algebraMap w.valuationSubring C)) hP hQ
  have hone : (Q.map (algebraMap w.valuationSubring C)) * (P.map (algebraMap w.valuationSubring C))
      = 1 := by
    ext i j
    have h := Fintype.linearIndependent_iff.1 ha.1
      (fun j => ((Q.map (algebraMap w.valuationSubring C)) *
        (P.map (algebraMap w.valuationSubring C))) i j - (1 : Matrix (Fin n) (Fin n) C) i j)
      (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hQP i]
        simp [Matrix.one_apply])
      j
    exact sub_eq_zero.1 h
  have hdet := congrArg Matrix.det hone
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hle : ∀ R : Matrix (Fin n) (Fin n) w.valuationSubring,
      w (R.map (algebraMap w.valuationSubring C)).det ≤ 1 := by
    intro R
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ValuationSubring.algebraMap_apply]
    exact (w.mem_valuationSubring_iff _).1 R.det.2
  refine ⟨P.map (algebraMap w.valuationSubring C), fun i => hP i, le_antisymm (hle P) ?_⟩
  calc (1 : ℝ≥0) = w (Q.map (algebraMap w.valuationSubring C)).det *
        w (P.map (algebraMap w.valuationSubring C)).det := by rw [← map_mul, hdet, map_one]
    _ ≤ w (P.map (algebraMap w.valuationSubring C)).det :=
        mul_le_of_le_one_left (by positivity) (hle Q)

end Lattice

end GlobalTheory.DetRelCompare

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

end GlobalTheory.DetRelCompare
