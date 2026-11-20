import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertSpan

section Vec

variable {L : Type} [Field L] {N : ℕ}

def vec3 (x : L) (w : Fin N → L) (t : L) : Fin (N + 2) → L :=
  Fin.cons (α := fun _ => L) x (Fin.snoc (α := fun _ => L) w t)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blockVector_first (x : L) (w : Fin N → L) (t : L) : vec3 x w t 0 = x := rfl

/- English proof (translation)
Simplify using `[vec3, mid]`.
-/
@[simp] theorem blockVector_middle (x : L) (w : Fin N → L) (t : L) (j : Fin N) : vec3 x w t (mid j) = w j := by
  simp [vec3, mid]

/- English proof (translation)
Simplify using `[vec3, ← Fin.succ_last]`.
-/
@[simp] theorem blockVector_last (x : L) (w : Fin N → L) (t : L) : vec3 x w t (Fin.last (N + 1)) = t := by
  simp [vec3, ← Fin.succ_last]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Conclude with `h0`. Conclude with `hm j`. Conclude with `hl`.
-/
theorem vec_ext {f h : Fin (N + 2) → L} (h0 : f 0 = h 0) (hm : ∀ j, f (mid j) = h (mid j))
    (hl : f (Fin.last (N + 1)) = h (Fin.last (N + 1))) : f = h := by
  funext i
  rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
  · exact h0
  · exact hm j
  · exact hl

/- English proof (translation)
The claim follows from `vec_ext (by simp) (fun j => by simp) (by simp)`.
-/
theorem vec3_add (x x' : Fin N → L) (t t' : L) :
    vec3 (0 : L) x t + vec3 0 x' t' = vec3 0 (x + x') (t + t') :=
  vec_ext (by simp) (fun j => by simp) (by simp)

/- English proof (translation)
The claim follows from `vec_ext (by simp) (fun j => by simp) (by simp)`.
-/
theorem blockVector_sub (x x' : Fin N → L) (t t' : L) :
    vec3 (0 : L) x t - vec3 0 x' t' = vec3 0 (x - x') (t - t') :=
  vec_ext (by simp) (fun j => by simp) (by simp)

/- English proof (translation)
The claim follows from `vec_ext (by simp [Finset.sum_apply]) (fun j => by simp [Finset.sum_apply, Matrix.vecMul, dotProduct]) (by simp [Finset.sum_apply, dotProduct])`.
-/
theorem sum_smul_blockVector (ρ : Fin N → L) (M : Matrix (Fin N) (Fin N) L) (s : Fin N → L) :
    ∑ k, ρ k • vec3 (0 : L) (M k) (s k) = vec3 0 (ρ ᵥ* M) (ρ ⬝ᵥ s) :=
  vec_ext (by simp [Finset.sum_apply]) (fun j => by simp [Finset.sum_apply, Matrix.vecMul, dotProduct])
    (by simp [Finset.sum_apply, dotProduct])

def mat3 (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) L :=
  Matrix.of (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blockMatrix_first (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    mat3 p M l 0 = p := rfl

/- English proof (translation)
Use `show (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l)) (mid j) = M j`. Simplify using `[mid]`.
-/
@[simp] theorem blockMatrix_middle (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) (j : Fin N) :
    mat3 p M l (mid j) = M j := by
  show (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l)) (mid j) = M j
  simp [mid]

/- English proof (translation)
Use `show (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l)) (Fin.last (N + 1)) = l`. Simplify using `[← Fin.succ_last]`.
-/
@[simp] theorem blockMatrix_last (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    mat3 p M l (Fin.last (N + 1)) = l := by
  show (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l))
    (Fin.last (N + 1)) = l
  simp [← Fin.succ_last]

/- English proof (translation)
Rewrite using `[Matrix.vecMul_eq_sum, sum_idx]`. Simplify using the standard rewrite rules.
-/
theorem vecMul_blockMatrix (ρ p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    ρ ᵥ* mat3 p M l = ρ 0 • p + ∑ j, ρ (mid j) • M j + ρ (Fin.last (N + 1)) • l := by
  rw [Matrix.vecMul_eq_sum, sum_idx]
  simp

/- English proof (translation)
Establish `e : (A.submatrix Fin.succ Fin.succ).det = A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det`. Rewrite using `[Matrix.det_succ_row _ (Fin.last N), Finset.sum_eq_single (Fin.last N)]`. Establish `: ((A.submatrix Fin.succ Fin.succ).submatrix (Fin.last N).succAbove (Fin.last N).succAbove) = B`. Use extensionality with `i j`. Simplify `hm i j` using `[mid]`.

Rewrite using `[this]`. Simplify using `[← two_mul, Fin.succ_last]`. Introduce `j _ hj`. Establish `: j.succ ≠ Fin.last (N + 1)` using `fun h => hj (by simpa [← Fin.succ_last] using h)`. Establish `h2 : A.submatrix Fin.succ Fin.succ (Fin.last N) j = 0`.

Rewrite using `[Matrix.submatrix_apply, Fin.succ_last]`. Conclude with `hl _ this`. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.det_succ_column_zero, Finset.sum_eq_single 0 (fun i _ hi => by rw [h0 i hi]; simp) (by simp)]`. Simplify using `only [Fin.succAbove_zero, e]`. Simplify using `[mul_assoc]`.
-/
theorem det_tri (A : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (B : Matrix (Fin N) (Fin N) L)
    (h0 : ∀ i, i ≠ 0 → A i 0 = 0) (hl : ∀ j, j ≠ Fin.last (N + 1) → A (Fin.last (N + 1)) j = 0)
    (hm : ∀ i j, A (mid i) (mid j) = B i j) :
    A.det = A 0 0 * A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det := by
  have e : (A.submatrix Fin.succ Fin.succ).det = A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det := by
    rw [Matrix.det_succ_row _ (Fin.last N), Finset.sum_eq_single (Fin.last N)]
    · have : ((A.submatrix Fin.succ Fin.succ).submatrix (Fin.last N).succAbove (Fin.last N).succAbove) = B := by
        ext i j
        simpa [mid] using hm i j
      rw [this]
      simp [← two_mul, Fin.succ_last]
    · intro j _ hj
      have : j.succ ≠ Fin.last (N + 1) := fun h => hj (by simpa [← Fin.succ_last] using h)
      have h2 : A.submatrix Fin.succ Fin.succ (Fin.last N) j = 0 := by
        rw [Matrix.submatrix_apply, Fin.succ_last]
        exact hl _ this
      rw [h2]
      simp
    · simp
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0 (fun i _ hi => by rw [h0 i hi]; simp) (by simp)]
  simp only [Fin.succAbove_zero, e]
  simp [mul_assoc]

end Vec

section Lat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

/- English proof (translation)
Establish `e : vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) = ∑ k, X i k • vec3 (0 : L) (M k) (s k)`. Rewrite using `[sum_smul_blockVector]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `R.sum_mem fun k _ => R.smul_mem ⟨X i k, hX i k⟩ (h k)`.
-/
theorem comb (R : Submodule (intL L) (Fin (N + 2) → L)) {X : Matrix (Fin N) (Fin N) L} (hX : IsInt X)
    (M : Matrix (Fin N) (Fin N) L) (s : Fin N → L) (h : ∀ k, vec3 (0 : L) (M k) (s k) ∈ R) (i : Fin N) :
    vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) ∈ R := by
  have e : vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) = ∑ k, X i k • vec3 (0 : L) (M k) (s k) := by
    rw [sum_smul_blockVector]
    rfl
  rw [e]
  exact R.sum_mem fun k _ => R.smul_mem ⟨X i k, hX i k⟩ (h k)

/- English proof (translation)
Establish `hi : t / w ∈ intL L`. Rewrite using `[GlobalTheory.UnitarySwap.mem_int, map_div₀]`. Conclude with `div_le_one_of_le₀ hv zero_le'`. Establish `e : vec3 (0 : L) (0 : Fin N → L) t = (t / w) • vec3 (0 : L) (0 : Fin N → L) w` using `vec_ext (by simp) (fun j => by simp) (by simp [hw])`. Rewrite using `[e]`.

Conclude with `R.smul_mem ⟨t / w, hi⟩ h`.
-/
theorem scale (R : Submodule (intL L) (Fin (N + 2) → L)) {w t : L} (hw : w ≠ 0)
    (hv : Valued.v t ≤ Valued.v w) (h : vec3 (0 : L) 0 w ∈ R) : vec3 (0 : L) 0 t ∈ R := by
  have hi : t / w ∈ intL L := by
    rw [GlobalTheory.UnitarySwap.mem_int, map_div₀]
    exact div_le_one_of_le₀ hv zero_le'
  have e : vec3 (0 : L) (0 : Fin N → L) t = (t / w) • vec3 (0 : L) (0 : Fin N → L) w :=
    vec_ext (by simp) (fun j => by simp) (by simp [hw])
  rw [e]
  exact R.smul_mem ⟨t / w, hi⟩ h

/- English proof (translation)
Rewrite using `[map_zpow₀, hϖ, ← WithZero.exp_zsmul]`. Simplify using the standard rewrite rules.
-/
theorem v_zpow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  simp

/- English proof (translation)
Take `⟨hU, hV, hC, hgC, e⟩` from `hf`. Establish `e' : C * (U + V * g₀) = 1` using `mul_eq_one_comm.1 e`. Establish `h1' : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) ((0 : Fin N → L) k) ∈ R` using `h1`. Establish `c1 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i, vec3 (0 : L) (X i) 0 ∈ R` using `fun {X} hX i => by`. Simplify using `using comb R hX 1 0 h1' i`.

Establish `c2 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i, vec3 (0 : L) ((X * g₀) i) (((X * g₀) *ᵥ b) i) ∈ R` using `fun {X} hX i => by`. Simplify `comb R hX g₀ (g₀ *ᵥ b) h2 i` using `[Matrix.mulVec_mulVec]`. Establish `eA : C * V * g₀ = 1 - C * U`. Rewrite using `[← e', Matrix.mul_add, Matrix.mul_assoc C V g₀]`. Normalize the expressions using the abelian group laws.

Establish `iA : IsInt (C * V * g₀)` using `fun i j => by`. Rewrite using `[eA]`. Conclude with `sub_mem (isInt_one i j) ((hC.mul hU) i j)`. Establish `eB : (1 - g₀ * C * V) * g₀ = g₀ * C * U`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc g₀ C V, Matrix.mul_assoc g₀ (C * V) g₀, eA, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc g₀ C U]`.

Normalize the expressions using the abelian group laws. Establish `iB : IsInt (1 - g₀ * C * V)` using `fun i j => sub_mem (isInt_one i j) ((hgC.mul hV) i j)`. Use `⟨fun k => ?_, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `R.add_mem (c1 hU k) (c2 hV k)` as an intermediate fact. Rewrite `this` using `[vec3_add, zero_add]`. Then use the resulting hypothesis.

Use `R.sub_mem (c2 (hC.mul hV) i) (c1 iA i)` as an intermediate fact. Rewrite `this` using `[blockVector_sub, sub_self, sub_zero]`. Then use the resulting hypothesis. Use `R.sub_mem (c2 iB i) (c1 (hgC.mul hU) i)` as an intermediate fact. Rewrite `this` using `[eB, blockVector_sub, sub_self, sub_zero]`. Then use the resulting hypothesis.
-/
theorem mid_le {R : Submodule (intL L) (Fin (N + 2) → L)} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
    (hf : IsFrac g₀ U V C) (h1 : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 ∈ R)
    (h2 : ∀ k, vec3 (0 : L) (g₀ k) ((g₀ *ᵥ b) k) ∈ R) :
    (∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R) ∧
      (∀ i, vec3 (0 : L) 0 (((C * V * g₀) *ᵥ b) i) ∈ R) ∧
      ∀ i, vec3 (0 : L) 0 (((g₀ * C * U) *ᵥ b) i) ∈ R := by
  obtain ⟨hU, hV, hC, hgC, e⟩ := hf
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 e
  have h1' : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) ((0 : Fin N → L) k) ∈ R := h1
  have c1 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i, vec3 (0 : L) (X i) 0 ∈ R := fun {X} hX i => by
    simpa using comb R hX 1 0 h1' i
  have c2 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i,
      vec3 (0 : L) ((X * g₀) i) (((X * g₀) *ᵥ b) i) ∈ R := fun {X} hX i => by
    simpa [Matrix.mulVec_mulVec] using comb R hX g₀ (g₀ *ᵥ b) h2 i
  have eA : C * V * g₀ = 1 - C * U := by
    rw [← e', Matrix.mul_add, Matrix.mul_assoc C V g₀]
    abel
  have iA : IsInt (C * V * g₀) := fun i j => by
    rw [eA]
    exact sub_mem (isInt_one i j) ((hC.mul hU) i j)
  have eB : (1 - g₀ * C * V) * g₀ = g₀ * C * U := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc g₀ C V, Matrix.mul_assoc g₀ (C * V) g₀, eA, Matrix.mul_sub,
      Matrix.mul_one, Matrix.mul_assoc g₀ C U]
    abel
  have iB : IsInt (1 - g₀ * C * V) := fun i j => sub_mem (isInt_one i j) ((hgC.mul hV) i j)
  refine ⟨fun k => ?_, fun i => ?_, fun i => ?_⟩
  · have := R.add_mem (c1 hU k) (c2 hV k)
    rwa [vec3_add, zero_add] at this
  · have := R.sub_mem (c2 (hC.mul hV) i) (c1 iA i)
    rwa [blockVector_sub, sub_self, sub_zero] at this
  · have := R.sub_mem (c2 iB i) (c1 (hgC.mul hU) i)
    rwa [eB, blockVector_sub, sub_self, sub_zero] at this

/- English proof (translation)
Take `⟨hU, hV, hC, hgC, e⟩` from `hf`. Establish `e' : C * (U + V * g₀) = 1` using `mul_eq_one_comm.1 e`. Use `⟨fun k => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `R.sub_mem (comb R hC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h1 k)` as an intermediate fact. Rewrite `this` using `[e', blockVector_sub, sub_zero, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]`.

Simplify using `using this`. Use `R.add_mem (comb R hgC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h2 k)` as an intermediate fact. Establish `e2 : g₀ * C * (U + V * g₀) = g₀` using `by rw [Matrix.mul_assoc, e', Matrix.mul_one]`. Establish `e3 : ((g₀ * C) *ᵥ ((V * g₀) *ᵥ b)) k + ((g₀ * C * U) *ᵥ b) k = (g₀ *ᵥ b) k`. Rewrite using `[Matrix.mulVec_mulVec, ← Pi.add_apply, ← Matrix.add_mulVec, ← Matrix.mul_add, add_comm, e2]`.

Rewrite `this` using `[vec3_add, e2, add_zero, e3]`. Then use the resulting hypothesis.
-/
theorem mid_ge {R : Submodule (intL L) (Fin (N + 2) → L)} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
    (hf : IsFrac g₀ U V C) (hm : ∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R)
    (h1 : ∀ i, vec3 (0 : L) 0 (((C * V * g₀) *ᵥ b) i) ∈ R)
    (h2 : ∀ i, vec3 (0 : L) 0 (((g₀ * C * U) *ᵥ b) i) ∈ R) :
    (∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 ∈ R) ∧
      ∀ k, vec3 (0 : L) (g₀ k) ((g₀ *ᵥ b) k) ∈ R := by
  obtain ⟨hU, hV, hC, hgC, e⟩ := hf
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 e
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have := R.sub_mem (comb R hC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h1 k)
    rw [e', blockVector_sub, sub_zero, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at this
    simpa using this
  · have := R.add_mem (comb R hgC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h2 k)
    have e2 : g₀ * C * (U + V * g₀) = g₀ := by rw [Matrix.mul_assoc, e', Matrix.mul_one]
    have e3 : ((g₀ * C) *ᵥ ((V * g₀) *ᵥ b)) k + ((g₀ * C * U) *ᵥ b) k = (g₀ *ᵥ b) k := by
      rw [Matrix.mulVec_mulVec, ← Pi.add_apply, ← Matrix.add_mulVec, ← Matrix.mul_add, add_comm, e2]
    rwa [vec3_add, e2, add_zero, e3] at this

/- English proof (translation)
Establish `hϖ0 : ϖ ≠ 0` using `fun h => by`. Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Establish `hint : ∀ n : ℕ, ϖ ^ n ∈ intL L` using `fun n => pow_mem (by`. Rewrite using `[GlobalTheory.UnitarySwap.mem_int, hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use the proof step `omega) n`. Break down `le_or_gt 0 a with h | h` into its components or cases. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le h`. Establish `t1 : (n : ℤ).toNat = n` using `Int.toNat_natCast n`. Establish `t2 : (-(n : ℤ)).toNat = 0` using `by omega`.

Establish `ew : vec3 ((ϖ ^ (n : ℤ))) (ϖ ^ (n : ℤ) • r) (ϖ ^ (n : ℤ) * c) = ϖ ^ n • vec3 (1 : L) 0 0 + vec3 (0 : L) (ϖ ^ n • r) (ϖ ^ n * c)` using `vec_ext (by simp) (fun j => by simp) (by simp)`. Rewrite using `[t1, t2]`. Use `⟨vec3 1 0 0, by simp, he, ?_, ⟨ϖ ^ (-(n : ℤ)), ?_, hD⟩, fun R' h1 h2 => ⟨h1, ?_⟩⟩` and prove the remaining obligations. Use `R.sub_mem hA (R.smul_mem ⟨ϖ ^ n, hint n⟩ he)` as an intermediate fact. Rewrite `this` using `[ew]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `show _ = ϖ ^ n • vec3 (1 : L) 0 0 + _ - ϖ ^ n • vec3 (1 : L) 0 0`. Normalize the expressions using the abelian group laws. Rewrite using `[v_zpow hϖ]`. Simplify using the standard rewrite rules.

Rewrite using `[ew]`. Conclude with `R'.add_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ -a by omega)`. Take `rfl : a = -(n : ℤ)` from `by omega`. Establish `t1 : (-(n : ℤ)).toNat = 0` using `by omega`.

Establish `t2 : (-(-(n : ℤ))).toNat = n` using `by simp`. Establish `en : ϖ ^ n * (ϖ ^ n)⁻¹ = 1` using `mul_inv_cancel₀ (pow_ne_zero _ hϖ0)`. Establish `ew : vec3 (1 : L) 0 0 = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) - vec3 (0 : L) r c` using `vec_ext (by simp [en]) (fun j => by simp [← mul_assoc, en]) (by simp [← mul_assoc, en])`. Establish `ew2 : ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) = vec3 (1 : L) 0 0 + vec3 (0 : L) r c` using `by rw [ew]; abel`. Rewrite using `[t1, t2]`.

Simplify using `only [pow_zero, one_smul, one_mul]`. Use `⟨_, ?_, hA, ?_, ⟨1, by simp, hl⟩, fun R' h1 h2 => ⟨?_, h1⟩⟩` and prove the remaining obligations. Rewrite using `[blockVector_first, v_zpow hϖ]`. Simplify using the standard rewrite rules. Use `R.sub_mem (R.smul_mem ⟨ϖ ^ n, hint n⟩ hA) he` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `show _ = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) - _`. Rewrite using `[ew2]`. Normalize the expressions using the abelian group laws. Rewrite using `[ew]`.

Conclude with `R'.sub_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2`.
-/
theorem first_row {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a : ℤ) (r : Fin N → L) (c : L)
    (R : Submodule (intL L) (Fin (N + 2) → L)) (he : vec3 (1 : L) 0 0 ∈ R)
    (hA : vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R) (hl : vec3 (0 : L) 0 1 ∈ R)
    (hD : vec3 (0 : L) 0 (ϖ ^ (-a)) ∈ R) :
    ∃ q : Fin (N + 2) → L, Valued.v (q 0) = WithZero.exp ((-a).toNat : ℤ) ∧ q ∈ R ∧
      vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R ∧
      (∃ w, Valued.v w = WithZero.exp (a.toNat : ℤ) ∧ vec3 (0 : L) 0 w ∈ R) ∧
      ∀ R' : Submodule (intL L) (Fin (N + 2) → L), q ∈ R' →
        vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R' →
        vec3 (1 : L) 0 0 ∈ R' ∧ vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R' := by
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hint : ∀ n : ℕ, ϖ ^ n ∈ intL L := fun n => pow_mem (by
    rw [GlobalTheory.UnitarySwap.mem_int, hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega) n
  rcases le_or_gt 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have t1 : (n : ℤ).toNat = n := Int.toNat_natCast n
    have t2 : (-(n : ℤ)).toNat = 0 := by omega
    have ew : vec3 ((ϖ ^ (n : ℤ))) (ϖ ^ (n : ℤ) • r) (ϖ ^ (n : ℤ) * c) =
        ϖ ^ n • vec3 (1 : L) 0 0 + vec3 (0 : L) (ϖ ^ n • r) (ϖ ^ n * c) :=
      vec_ext (by simp) (fun j => by simp) (by simp)
    rw [t1, t2]
    refine ⟨vec3 1 0 0, by simp, he, ?_, ⟨ϖ ^ (-(n : ℤ)), ?_, hD⟩, fun R' h1 h2 => ⟨h1, ?_⟩⟩
    · have := R.sub_mem hA (R.smul_mem ⟨ϖ ^ n, hint n⟩ he)
      rw [ew] at this
      convert this using 1
      show _ = ϖ ^ n • vec3 (1 : L) 0 0 + _ - ϖ ^ n • vec3 (1 : L) 0 0
      abel
    · rw [v_zpow hϖ]
      simp
    · rw [ew]
      exact R'.add_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -a by omega)
    obtain rfl : a = -(n : ℤ) := by omega
    have t1 : (-(n : ℤ)).toNat = 0 := by omega
    have t2 : (-(-(n : ℤ))).toNat = n := by simp
    have en : ϖ ^ n * (ϖ ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hϖ0)
    have ew : vec3 (1 : L) 0 0 = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) -
        vec3 (0 : L) r c :=
      vec_ext (by simp [en]) (fun j => by simp [← mul_assoc, en]) (by simp [← mul_assoc, en])
    have ew2 : ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) =
        vec3 (1 : L) 0 0 + vec3 (0 : L) r c :=
      by rw [ew]; abel
    rw [t1, t2]
    simp only [pow_zero, one_smul, one_mul]
    refine ⟨_, ?_, hA, ?_, ⟨1, by simp, hl⟩, fun R' h1 h2 => ⟨?_, h1⟩⟩
    · rw [blockVector_first, v_zpow hϖ]
      simp
    · have := R.sub_mem (R.smul_mem ⟨ϖ ^ n, hint n⟩ hA) he
      convert this using 1
      show _ = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) - _
      rw [ew2]
      abel
    · rw [ew]
      exact R'.sub_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2

end Lat

section Main

variable {L : Type} [Field L] {N : ℕ}

/- English proof (translation)
Rewrite using `[vecMul_blockMatrix]`. Simplify using `only [blockVector_first, blockVector_middle, blockVector_last, zero_smul, zero_add]`. Rewrite using `[sum_smul_blockVector (z • (r ᵥ* C)) (U + V * g₀) ((V * g₀) *ᵥ b)]`. Establish `e1 : (z • (r ᵥ* C)) ᵥ* (U + V * g₀) = z • r`. Rewrite using `[Matrix.smul_vecMul, Matrix.vecMul_vecMul, e, Matrix.vecMul_one]`.

Establish `e2 : (z • (r ᵥ* C)) ⬝ᵥ ((V * g₀) *ᵥ b) = z * (r ⬝ᵥ ((C * V * g₀) *ᵥ b))`. Rewrite using `[smul_dotProduct, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, Matrix.mul_assoc C V g₀]`. Rewrite using `[e1, e2]`. Conclude with `vec_ext (by simp) (fun j => by simp) (by simp; field_simp; ring)`.
-/
theorem vecMul_basis (q : Fin (N + 2) → L) (g₀ U V C : Matrix (Fin N) (Fin N) L) (r b : Fin N → L) (c y z : L)
    (hy : y ≠ 0) (e : C * (U + V * g₀) = 1) :
    vec3 (0 : L) (z • (r ᵥ* C)) (z * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) ᵥ*
      mat3 q (fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k)) (vec3 (0 : L) 0 y) =
      vec3 (0 : L) (z • r) (z * c) := by
  rw [vecMul_blockMatrix]
  simp only [blockVector_first, blockVector_middle, blockVector_last, zero_smul, zero_add]
  rw [sum_smul_blockVector (z • (r ᵥ* C)) (U + V * g₀) ((V * g₀) *ᵥ b)]
  have e1 : (z • (r ᵥ* C)) ᵥ* (U + V * g₀) = z • r := by
    rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, e, Matrix.vecMul_one]
  have e2 : (z • (r ᵥ* C)) ⬝ᵥ ((V * g₀) *ᵥ b) = z * (r ⬝ᵥ ((C * V * g₀) *ᵥ b)) := by
    rw [smul_dotProduct, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, Matrix.mul_assoc C V g₀]
  rw [e1, e2]
  exact vec_ext (by simp) (fun j => by simp) (by simp; field_simp; ring)

/- English proof (translation)
Use `det_tri (mat3 q (fun k => vec3 (0 : L) (B k) (s k)) (vec3 (0 : L) 0 y)) B ?_ ?_ ?_` as an intermediate fact. Simplify using `using this`. Introduce `i hi`. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Conclude with `absurd rfl hi`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `j hj`. Break down `idx_cases j with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Conclude with `absurd rfl hj`. Introduce `i j`. Simplify using the standard rewrite rules.
-/
theorem det_basis (q : Fin (N + 2) → L) (B : Matrix (Fin N) (Fin N) L) (s : Fin N → L) (y : L) :
    (mat3 q (fun k => vec3 (0 : L) (B k) (s k)) (vec3 (0 : L) 0 y)).det = q 0 * y * B.det := by
  have := det_tri (mat3 q (fun k => vec3 (0 : L) (B k) (s k)) (vec3 (0 : L) 0 y)) B ?_ ?_ ?_
  · simpa using this
  · intro i hi
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · exact absurd rfl hi
    · simp
    · simp
  · intro j hj
    rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
    · simp
    · simp
    · exact absurd rfl hj
  · intro i j
    simp

end Main

/- English proof (translation)
Introduce `L _ _ ϖ N a g g₀ U V C r b c y hϖ hf h00 h0m h0l hm0 hmm hml hl0 hlm hll hya hy1 hy2 hyc`. Establish `eg0 : g 0 = vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c)` using `vec_ext (by simp [h00]) (fun j => by simp [h0m]) (by simp [h0l])`. Establish `egm : ∀ i, g (mid i) = vec3 (0 : L) (g₀ i) ((g₀ *ᵥ b) i)` using `fun i => vec_ext (by simp [hm0]) (fun j => by simp [hmm]) (by simp [hml])`. Establish `egl : g (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) (ϖ ^ (-a))` using `vec_ext (by simp [hl0]) (fun j => by simp [hlm]) (by simp [hll])`. Establish `e10 : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 = vec3 (1 : L) (0 : Fin N → L) 0` using `vec_ext (by simp) (fun j => by simp [Matrix.one_apply, (mid_ne_zero j).symm]) (by simp [Matrix.one_apply])`.

Establish `e1m : ∀ k, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid k) = vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0` using `fun k => vec_ext (by simp [Matrix.one_apply, mid_ne_zero]) (fun j => by simp [Matrix.one_apply, mid_injective.eq_iff]) (by simp [Matrix.one_apply, mid_ne_last])`. Establish `e1l : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) 1` using `vec_ext (by simp [Matrix.one_apply]) (fun j => by simp [Matrix.one_apply, (mid_ne_last j).symm]) (by simp)`. Take `⟨R, hR⟩ : ∃ R, R = rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g` from `⟨_, rfl⟩`. Establish `r1 : ∀ i, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i ∈ R` using `fun i => hR ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)`. Establish `r2 : ∀ i, g i ∈ R` using `fun i => hR ▸ Submodule.mem_sup_right (row_mem_rowLat _ i)`.

Take `⟨q, hq0, hqR, hwR, ⟨w, hw, hwl⟩, hback⟩` from `first_row hϖ a r c R (by rw [← e10]; exact r1 0) (by rw [← eg0]; exact r2 0) (by rw [← e1l]; exact r1 _) (by rw [← egl]; exact r2 _)`. Take `⟨m1, m2, m3⟩` from `mid_le (b := b) hf (R := R) (fun k => by rw [← e1m]; exact r1 _) (fun k => by rw [← egm]; exact r2 _)`. Establish `hval : WithZero.exp (a.toNat : ℤ) ≠ 0` using `WithZero.exp_ne_zero`. Establish `hvy : Valued.v y ≠ 0` using `fun h => by`. Rewrite `hya` using `[h]`.

Conclude with `hval (le_antisymm hya zero_le')`. Establish `hy0 : y ≠ 0` using `fun h => hvy (by rw [h, map_zero])`. Establish `hnz : ∀ t : L, Valued.v y = Valued.v t → t ≠ 0` using `fun t h h0 => hvy (by rw [h, h0, map_zero])`. Establish `hyR : vec3 (0 : L) (0 : Fin N → L) y ∈ R`. Break down `hyc with h | ⟨i, h⟩ | ⟨i, h⟩` into its components or cases.

Conclude with `scale R (hnz w (h.trans hw.symm)) (h.trans hw.symm).le hwl`. Conclude with `scale R (hnz _ h) h.le (m2 i)`. Conclude with `scale R (hnz _ h) h.le (m3 i)`. Establish `e' : C * (U + V * g₀) = 1` using `mul_eq_one_comm.1 hf.2.2.2.2`. Take `⟨M, hM⟩ : ∃ M : Fin N → Fin (N + 2) → L, M = fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k)` from `⟨_, rfl⟩`.

Take `⟨P, hP⟩ : ∃ P, P = mat3 q M (vec3 (0 : L) 0 y)` from `⟨_, rfl⟩`. Take `⟨ρ, hρ⟩ : ∃ ρ, ρ = vec3 (0 : L) (ϖ ^ a.toNat • (r ᵥ* C)) (ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y)` from `⟨_, rfl⟩`. Establish `eρ : ρ ᵥ* P = vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c)`. Rewrite using `[hρ, hP, hM]`. Conclude with `vecMul_basis q g₀ U V C r b c y _ hy0 e'`.

Establish `hdet : Valued.v (U + V * g₀).det = (Valued.v C.det)⁻¹`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← Matrix.det_mul, hf.2.2.2.2, Matrix.det_one, map_one]`. Use `⟨P, ρ, ?_, by rw [hρ]; simp, fun j => by rw [hρ]; simp, by rw [hρ]; simp, ?_⟩` and prove the remaining obligations. Rewrite using `[hP, hM, det_basis q (U + V * g₀) ((V * g₀) *ᵥ b) y, map_mul, map_mul, hq0, hdet]`.

Conclude with `mul_right_comm _ _ _`. Rewrite using `[← hR]`. Take `⟨R', hR'⟩ : ∃ R', R' = rowLat P ⊔ Submodule.span (intL L) {ρ ᵥ* P}` from `⟨_, rfl⟩`. Rewrite using `[← hR']`. Establish `p1 : ∀ i, P i ∈ R'` using `fun i => hR' ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)`.

Establish `hq' : q ∈ R'` using `by simpa [hP] using p1 0`. Establish `hm' : ∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R'` using `fun k => by`. Use `p1 (mid k)` as an intermediate fact. Simplify `this` using `[hP, hM]`. Establish `hy' : vec3 (0 : L) (0 : Fin N → L) y ∈ R'` using `by simpa [hP] using p1 (Fin.last (N + 1))`.

Establish `hw' : vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R'`. Rewrite using `[← eρ, hR']`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span rfl)`. Establish `sc : ∀ t, Valued.v t ≤ Valued.v y → vec3 (0 : L) (0 : Fin N → L) t ∈ R'` using `fun t ht => scale R' hy0 ht hy'`. Take `⟨n1, n2⟩` from `mid_ge (b := b) hf hm' (fun i => sc _ (hy1 i)) (fun i => sc _ (hy2 i))`.

Take `⟨f1, f2⟩` from `hback R' hq' hw'`. Establish `hone : Valued.v (1 : L) ≤ Valued.v y`. Use `le_trans ?_ hya` and prove the remaining obligations. Rewrite using `[map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.

Establish `hD : Valued.v (ϖ ^ (-a)) ≤ Valued.v y`. Use `le_trans ?_ hya` and prove the remaining obligations. Rewrite using `[v_zpow hϖ, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[hR]`. Use `sup_le (rowLat_le.2 fun i => ?_) (rowLat_le.2 fun i => ?_)` and prove the remaining obligations. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Rewrite using `[e10]`. Conclude with `f1`.

Rewrite using `[e1m]`. Conclude with `n1 j`. Rewrite using `[e1l]`. Conclude with `sc 1 hone`. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases.

Rewrite using `[eg0]`. Conclude with `f2`. Rewrite using `[egm]`. Conclude with `n2 j`. Rewrite using `[egl]`.

Conclude with `sc _ hD`. Rewrite using `[hR']`. Use `sup_le (rowLat_le.2 fun i => ?_) ?_` and prove the remaining obligations. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Simplify `hqR` using `[hP]`.

Simplify `m1 j` using `[hP, hM]`. Simplify `hyR` using `[hP]`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, eρ]`. Conclude with `hwR`.
-/
theorem spanEq : SpanEq := by
  intro L _ _ ϖ N a g g₀ U V C r b c y hϖ hf h00 h0m h0l hm0 hmm hml hl0 hlm hll hya hy1 hy2 hyc
  have eg0 : g 0 = vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) :=
    vec_ext (by simp [h00]) (fun j => by simp [h0m]) (by simp [h0l])
  have egm : ∀ i, g (mid i) = vec3 (0 : L) (g₀ i) ((g₀ *ᵥ b) i) :=
    fun i => vec_ext (by simp [hm0]) (fun j => by simp [hmm]) (by simp [hml])
  have egl : g (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) (ϖ ^ (-a)) :=
    vec_ext (by simp [hl0]) (fun j => by simp [hlm]) (by simp [hll])
  have e10 : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 = vec3 (1 : L) (0 : Fin N → L) 0 :=
    vec_ext (by simp) (fun j => by simp [Matrix.one_apply, (mid_ne_zero j).symm])
      (by simp [Matrix.one_apply])
  have e1m : ∀ k, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid k) =
      vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 :=
    fun k => vec_ext (by simp [Matrix.one_apply, mid_ne_zero])
      (fun j => by simp [Matrix.one_apply, mid_injective.eq_iff])
      (by simp [Matrix.one_apply, mid_ne_last])
  have e1l : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) 1 :=
    vec_ext (by simp [Matrix.one_apply]) (fun j => by simp [Matrix.one_apply, (mid_ne_last j).symm]) (by simp)
  obtain ⟨R, hR⟩ : ∃ R, R = rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g := ⟨_, rfl⟩
  have r1 : ∀ i, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i ∈ R :=
    fun i => hR ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)
  have r2 : ∀ i, g i ∈ R := fun i => hR ▸ Submodule.mem_sup_right (row_mem_rowLat _ i)
  obtain ⟨q, hq0, hqR, hwR, ⟨w, hw, hwl⟩, hback⟩ := first_row hϖ a r c R (by rw [← e10]; exact r1 0)
    (by rw [← eg0]; exact r2 0) (by rw [← e1l]; exact r1 _) (by rw [← egl]; exact r2 _)
  obtain ⟨m1, m2, m3⟩ := mid_le (b := b) hf (R := R) (fun k => by rw [← e1m]; exact r1 _)
    (fun k => by rw [← egm]; exact r2 _)
  have hval : WithZero.exp (a.toNat : ℤ) ≠ 0 := WithZero.exp_ne_zero
  have hvy : Valued.v y ≠ 0 := fun h => by
    rw [h] at hya
    exact hval (le_antisymm hya zero_le')
  have hy0 : y ≠ 0 := fun h => hvy (by rw [h, map_zero])
  have hnz : ∀ t : L, Valued.v y = Valued.v t → t ≠ 0 := fun t h h0 => hvy (by rw [h, h0, map_zero])
  have hyR : vec3 (0 : L) (0 : Fin N → L) y ∈ R := by
    rcases hyc with h | ⟨i, h⟩ | ⟨i, h⟩
    · exact scale R (hnz w (h.trans hw.symm)) (h.trans hw.symm).le hwl
    · exact scale R (hnz _ h) h.le (m2 i)
    · exact scale R (hnz _ h) h.le (m3 i)
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 hf.2.2.2.2
  obtain ⟨M, hM⟩ : ∃ M : Fin N → Fin (N + 2) → L,
      M = fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = mat3 q M (vec3 (0 : L) 0 y) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = vec3 (0 : L) (ϖ ^ a.toNat • (r ᵥ* C))
      (ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) := ⟨_, rfl⟩
  have eρ : ρ ᵥ* P = vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) := by
    rw [hρ, hP, hM]
    exact vecMul_basis q g₀ U V C r b c y _ hy0 e'
  have hdet : Valued.v (U + V * g₀).det = (Valued.v C.det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← Matrix.det_mul, hf.2.2.2.2, Matrix.det_one, map_one]
  refine ⟨P, ρ, ?_, by rw [hρ]; simp, fun j => by rw [hρ]; simp, by rw [hρ]; simp, ?_⟩
  · rw [hP, hM, det_basis q (U + V * g₀) ((V * g₀) *ᵥ b) y, map_mul, map_mul, hq0, hdet]
    exact mul_right_comm _ _ _
  rw [← hR]
  obtain ⟨R', hR'⟩ : ∃ R', R' = rowLat P ⊔ Submodule.span (intL L) {ρ ᵥ* P} := ⟨_, rfl⟩
  rw [← hR']
  have p1 : ∀ i, P i ∈ R' := fun i => hR' ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)
  have hq' : q ∈ R' := by simpa [hP] using p1 0
  have hm' : ∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R' := fun k => by
    have := p1 (mid k)
    simpa [hP, hM] using this
  have hy' : vec3 (0 : L) (0 : Fin N → L) y ∈ R' := by simpa [hP] using p1 (Fin.last (N + 1))
  have hw' : vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R' := by
    rw [← eρ, hR']
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  have sc : ∀ t, Valued.v t ≤ Valued.v y → vec3 (0 : L) (0 : Fin N → L) t ∈ R' :=
    fun t ht => scale R' hy0 ht hy'
  obtain ⟨n1, n2⟩ := mid_ge (b := b) hf hm' (fun i => sc _ (hy1 i)) (fun i => sc _ (hy2 i))
  obtain ⟨f1, f2⟩ := hback R' hq' hw'
  have hone : Valued.v (1 : L) ≤ Valued.v y := by
    refine le_trans ?_ hya
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hD : Valued.v (ϖ ^ (-a)) ≤ Valued.v y := by
    refine le_trans ?_ hya
    rw [v_zpow hϖ, WithZero.exp_le_exp]
    omega
  apply le_antisymm
  · rw [hR]
    refine sup_le (rowLat_le.2 fun i => ?_) (rowLat_le.2 fun i => ?_)
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [e10]; exact f1
      · rw [e1m]; exact n1 j
      · rw [e1l]; exact sc 1 hone
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [eg0]; exact f2
      · rw [egm]; exact n2 j
      · rw [egl]; exact sc _ hD
  · rw [hR']
    refine sup_le (rowLat_le.2 fun i => ?_) ?_
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · simpa [hP] using hqR
      · simpa [hP, hM] using m1 j
      · simpa [hP] using hyR
    · rw [Submodule.span_le, Set.singleton_subset_iff, eρ]
      exact hwR

end GlobalTheory.CompanionTheory.InertSpan

end
