import Mathlib

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Establish `hsym : (Matrix.toBilin' A).IsSymm` using `Matrix.isSymm_toBilin'_iff_isSymm.mpr hs`. Take `⟨v₀, hv₀⟩` from `LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := Fin n → ℚ) (B := Matrix.toBilin' A) (LinearMap.BilinForm.isSymm_iff.mp hsym)`. Establish `hr : Module.finrank ℚ (Fin n → ℚ) = n` using `by simp`. Set `e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n` to `finCongr hr`. Set `v` to `v₀.reindex e`.

Establish `hv : ∀ i j, i ≠ j → v i ⬝ᵥ A *ᵥ v j = 0`. Introduce `i j hij`. Establish `h` using `hv₀ (e.symm.injective.ne hij)`. Simplify using `only [Function.onFun] at h`. Rewrite `h` using `[Matrix.toBilin'_apply']`.

Simplify `h` using `only [v, Module.Basis.reindex_apply]`. Set `P : Matrix (Fin n) (Fin n) ℚ` to `Matrix.of fun i j => v i j`. Establish `hP : IsUnit P` using `Matrix.linearIndependent_rows_iff_isUnit.mp v.linearIndependent`. Establish `hPd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP`. Establish `hdiag : P * A * Pᵀ = Matrix.diagonal fun i => v i ⬝ᵥ A *ᵥ v i`.

Use extensionality with `i j`. Establish `: (P * A * Pᵀ) i j = v i ⬝ᵥ A *ᵥ v j`. Rewrite using `[Matrix.mul_assoc]`. Simplify using `[Matrix.mul_apply, P, dotProduct, Matrix.mulVec]`. Rewrite using `[this]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ hij, hv i j hij]`. Use `⟨fun i => v i ⬝ᵥ A *ᵥ v i, (P⁻¹)ᵀ, fun i => hp _ (v.ne_zero i), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_transpose]`. Conclude with `(Matrix.isUnit_nonsing_inv_det P hPd).ne_zero`. Rewrite using `[← hdiag, Matrix.transpose_transpose]`. Establish `h1 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hPd`. Establish `h2 : Pᵀ * (P⁻¹)ᵀ = 1` using `by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_rat_eq_transpose_mul_diagonal_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hs : A.IsSymm) (hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) :
    ∃ (d : Fin n → ℚ) (Q : Matrix (Fin n) (Fin n) ℚ), (∀ i, 0 < d i) ∧ Q.det ≠ 0 ∧
      A = Qᵀ * Matrix.diagonal d * Q := by
  have hsym : (Matrix.toBilin' A).IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := Fin n → ℚ)
    (B := Matrix.toBilin' A) (LinearMap.BilinForm.isSymm_iff.mp hsym)
  have hr : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr hr
  let v := v₀.reindex e
  have hv : ∀ i j, i ≠ j → v i ⬝ᵥ A *ᵥ v j = 0 := by
    intro i j hij
    have h := hv₀ (e.symm.injective.ne hij)
    simp only [Function.onFun] at h
    rw [Matrix.toBilin'_apply'] at h
    simpa only [v, Module.Basis.reindex_apply] using h
  let P : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => v i j
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp v.linearIndependent
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdiag : P * A * Pᵀ = Matrix.diagonal fun i => v i ⬝ᵥ A *ᵥ v i := by
    ext i j
    have : (P * A * Pᵀ) i j = v i ⬝ᵥ A *ᵥ v j := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, P, dotProduct, Matrix.mulVec]
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hv i j hij]
  refine ⟨fun i => v i ⬝ᵥ A *ᵥ v i, (P⁻¹)ᵀ, fun i => hp _ (v.ne_zero i), ?_, ?_⟩
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det P hPd).ne_zero
  · rw [← hdiag, Matrix.transpose_transpose]
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
    have h2 : Pᵀ * (P⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc A = (P⁻¹ * P) * A * (Pᵀ * (P⁻¹)ᵀ) := by rw [h1, h2]; simp
      _ = P⁻¹ * (P * A * Pᵀ) * (P⁻¹)ᵀ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f`. Use `choose g hg using hb`. Establish `hb0 : (b : ℤ) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`. Use `⟨((b : ℤ) * b).toNat, fun i => b * g i, ?_, fun i => ?_⟩` and prove the remaining obligations. Use `mul_self_pos.mpr hb0` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h1 : ((((b : ℤ) * b).toNat : ℕ) : ℤ) = b * b` using `Int.toNat_of_nonneg (mul_self_nonneg _)`. Establish `h2 : ((((b : ℤ) * b).toNat : ℕ) : ℚ) = ((b : ℤ) : ℚ) * (b : ℤ)` using `by exact_mod_cast h1`. Establish `h3 : (g i : ℚ) = ((b : ℤ) : ℚ) * f i`. Use `hg i` as an intermediate fact.

Simplify `this` using `[zsmul_eq_mul]`. Rewrite using `[h2]`. Use `push_cast`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pos_nat_mul_eq_intCast {ι : Type} [Finite ι] (f : ι → ℚ) :
    ∃ (b : ℕ) (g : ι → ℤ), 0 < b ∧ ∀ i, (g i : ℚ) = b * f i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose g hg using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  refine ⟨((b : ℤ) * b).toNat, fun i => b * g i, ?_, fun i => ?_⟩
  · have := mul_self_pos.mpr hb0
    omega
  · have h1 : ((((b : ℤ) * b).toNat : ℕ) : ℤ) = b * b := Int.toNat_of_nonneg (mul_self_nonneg _)
    have h2 : ((((b : ℤ) * b).toNat : ℕ) : ℚ) = ((b : ℤ) : ℚ) * (b : ℤ) := by exact_mod_cast h1
    have h3 : (g i : ℚ) = ((b : ℤ) : ℚ) * f i := by
      have := hg i
      simpa [zsmul_eq_mul] using this
    rw [h2]
    push_cast
    rw [h3]
    ring

/- English proof (translation)
Introduce `n A hA`. Establish `hs : (A.map (fun x : ℤ => (x : ℚ))).IsSymm`. Use extensionality with `i j`. Use `hA.isHermitian.apply j i` as an intermediate fact. Simplify using `only [Matrix.map_apply, star_trivial, Int.cast_inj] at this`.

Simplify using `[this]`. Establish `hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x`. Introduce `x hx`. Establish `hx' : (fun i => (x i : ℝ)) ≠ 0`. Introduce `h`.

Apply `hx` to reduce the goal to its premises. Use extensionality with `i`. Use `congrFun h i` as an intermediate fact. Simplify using `using this`. Establish `h` using `hA.dotProduct_mulVec_pos hx'`.

Establish `h2 : star (fun i => (x i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (x i : ℝ)) = ((x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x : ℚ) : ℝ)`. Simplify using `[dotProduct, Matrix.mulVec]`. Rewrite `h` using `[h2]`. Conclude with `h` after adjusting the coercions. Take `⟨d, Q, hd, hQ, hAQ⟩` from `exists_rat_eq_transpose_mul_diagonal_mul _ hs hp`.

Take `⟨a, g, ha, hg⟩` from `exists_pos_nat_mul_eq_intCast (fun p : Fin n × Fin n => Q p.1 p.2)`. Take `⟨b, k, hb, hk⟩` from `exists_pos_nat_mul_eq_intCast d`. Establish `hkpos : ∀ i, 0 < k i`. Introduce `i`. Establish `: (0 : ℚ) < k i`.

Rewrite using `[hk i]`. Conclude with `mul_pos (by exact_mod_cast hb) (hd i)`. Conclude with `this` after adjusting the coercions. Set `l : Matrix (Fin n) (Fin n) ℤ` to `Matrix.of fun i j => g (i, j)`. Establish `hl : l.map (Int.castRingHom ℚ) = (a : ℚ) • Q`.

Use extensionality with `i j`. Simplify using `[l, hg]`. Establish `hc : (Matrix.diagonal fun i => (((k i).toNat : ℕ) : ℤ)).map (Int.castRingHom ℚ) = (b : ℚ) • Matrix.diagonal d`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `only [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[Int.toNat_of_nonneg (hkpos i).le]`. Conclude with `hk i`. Simplify using `[Matrix.diagonal_apply_ne _ hij]`.

Use `⟨a * b * a, fun i => (k i).toNat, l, by positivity, fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hkpos i show 0 < (k i).toNat` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `h0`. Establish `h1 : (l.map (Int.castRingHom ℚ)).det = 0`.

Use `(Int.castRingHom ℚ).map_det l` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, h0]`. Simplify using `using this.symm`. Rewrite `h1` using `[hl, Matrix.det_smul]`. Establish `ha' : (a : ℚ) ≠ 0` using `by exact_mod_cast ha.ne'`.

Conclude with `(mul_ne_zero (pow_ne_zero _ ha') hQ) h1`. Apply `Matrix.map_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hl, hc]`. Establish `: (((a * b * a : ℕ) : ℤ) • A).map (Int.castRingHom ℚ) = ((a : ℚ) * b * a) • A.map (fun x : ℤ => (x : ℚ))`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hAQ]`.

Simplify using `only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_smul_eq_transpose_mul_diagonal_mul :
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), (A.map (fun x : ℤ => (x : ℝ))).PosDef → ∃ (N : ℕ) (c : Fin n → ℕ) (l : Matrix (Fin n) (Fin n) ℤ), 0 < N ∧ (∀ i, 0 < c i) ∧ l.det ≠ 0 ∧ (N : ℤ) • A = lᵀ * Matrix.diagonal (fun i => (c i : ℤ)) * l) := by
  intro n A hA
  have hs : (A.map (fun x : ℤ => (x : ℚ))).IsSymm := by
    ext i j
    have := hA.isHermitian.apply j i
    simp only [Matrix.map_apply, star_trivial, Int.cast_inj] at this
    simp [this]
  have hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x := by
    intro x hx
    have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
      intro h
      apply hx
      ext i
      have := congrFun h i
      simpa using this
    have h := hA.dotProduct_mulVec_pos hx'
    have h2 : star (fun i => (x i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (x i : ℝ))
        = ((x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x : ℚ) : ℝ) := by
      simp [dotProduct, Matrix.mulVec]
    rw [h2] at h
    exact_mod_cast h
  obtain ⟨d, Q, hd, hQ, hAQ⟩ := exists_rat_eq_transpose_mul_diagonal_mul _ hs hp
  obtain ⟨a, g, ha, hg⟩ := exists_pos_nat_mul_eq_intCast (fun p : Fin n × Fin n => Q p.1 p.2)
  obtain ⟨b, k, hb, hk⟩ := exists_pos_nat_mul_eq_intCast d
  have hkpos : ∀ i, 0 < k i := by
    intro i
    have : (0 : ℚ) < k i := by
      rw [hk i]
      exact mul_pos (by exact_mod_cast hb) (hd i)
    exact_mod_cast this
  let l : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => g (i, j)
  have hl : l.map (Int.castRingHom ℚ) = (a : ℚ) • Q := by
    ext i j
    simp [l, hg]
  have hc : (Matrix.diagonal fun i => (((k i).toNat : ℕ) : ℤ)).map (Int.castRingHom ℚ)
      = (b : ℚ) • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rw [Int.toNat_of_nonneg (hkpos i).le]
      exact hk i
    · simp [Matrix.diagonal_apply_ne _ hij]
  refine ⟨a * b * a, fun i => (k i).toNat, l, by positivity, fun i => ?_, ?_, ?_⟩
  · have := hkpos i
    show 0 < (k i).toNat
    omega
  · intro h0
    have h1 : (l.map (Int.castRingHom ℚ)).det = 0 := by
      have := (Int.castRingHom ℚ).map_det l
      rw [RingHom.mapMatrix_apply, h0] at this
      simpa using this.symm
    rw [hl, Matrix.det_smul] at h1
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    exact (mul_ne_zero (pow_ne_zero _ ha') hQ) h1
  · apply Matrix.map_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hl, hc]
    have : (((a * b * a : ℕ) : ℤ) • A).map (Int.castRingHom ℚ)
        = ((a : ℚ) * b * a) • A.map (fun x : ℤ => (x : ℚ)) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      push_cast
      ring
    rw [this, hAQ]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
