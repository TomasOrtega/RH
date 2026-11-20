import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LuLowerLowerTriangular

set_option autoImplicit false
noncomputable section

open Module TopologicalSpace GlobalTheory.FlagPts

namespace GlobalTheory.FlagPts

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use `R.algebraMap_mem a using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Consider the case `add p q hp hq`. Take `⟨N₁, h₁⟩` from `hp`. Take `⟨N₂, h₂⟩` from `hq`. Use `⟨N₁ + N₂, ?_⟩` and prove the remaining obligations.

Establish `: (D ^ (N₁ + N₂) * fun x => MvPolynomial.eval (fun j => g j x) (p + q)) = D ^ N₂ * (D ^ N₁ * fun x => MvPolynomial.eval (fun j => g j x) p) + D ^ N₁ * (D ^ N₂ * fun x => MvPolynomial.eval (fun j => g j x) q)`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `add_mem (mul_mem (pow_mem hD _) h₁) (mul_mem (pow_mem hD _) h₂)`. Consider the case `mul_X p j hp`. Take `⟨N, h⟩` from `hp`. Use `⟨N + 1, ?_⟩` and prove the remaining obligations. Establish `: (D ^ (N + 1) * fun x => MvPolynomial.eval (fun j => g j x) (p * MvPolynomial.X j)) = (D ^ N * fun x => MvPolynomial.eval (fun j => g j x) p) * (D * g j)`.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.mul_apply, Pi.pow_apply, map_mul, MvPolynomial.eval_X]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem h (hg j)`.
-/
theorem exists_pow_mul_eval_mem {k : Type} [Field k] {X J : Type} (R : Subalgebra k (X → k)) (D : X → k) (g : J → X → k) (hD : D ∈ R)
    (hg : ∀ j, D * g j ∈ R) (q : MvPolynomial J k) :
    ∃ N : ℕ, (D ^ N * fun x => MvPolynomial.eval (fun j => g j x) q) ∈ R := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    convert R.algebraMap_mem a using 1
    funext x
    simp
  | add p q hp hq =>
    obtain ⟨N₁, h₁⟩ := hp
    obtain ⟨N₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, ?_⟩
    have : (D ^ (N₁ + N₂) * fun x => MvPolynomial.eval (fun j => g j x) (p + q)) =
        D ^ N₂ * (D ^ N₁ * fun x => MvPolynomial.eval (fun j => g j x) p) +
          D ^ N₁ * (D ^ N₂ * fun x => MvPolynomial.eval (fun j => g j x) q) := by
      funext x
      simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, map_add]
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hD _) h₁) (mul_mem (pow_mem hD _) h₂)
  | mul_X p j hp =>
    obtain ⟨N, h⟩ := hp
    refine ⟨N + 1, ?_⟩
    have : (D ^ (N + 1) * fun x => MvPolynomial.eval (fun j => g j x) (p * MvPolynomial.X j)) =
        (D ^ N * fun x => MvPolynomial.eval (fun j => g j x) p) * (D * g j) := by
      funext x
      simp only [Pi.mul_apply, Pi.pow_apply, map_mul, MvPolynomial.eval_X]
      ring
    rw [this]
    exact mul_mem h (hg j)

/- English proof (translation)
Establish `hcell : (b i).toMatrix (cellFrame b u i) = uniMat u i`. Use extensionality with `a m`. Rewrite using `[Basis.toMatrix_apply, cellFrame_apply]`. Simplify using `[Finsupp.single_apply]`. Establish `h1 : IsUnit ((b i).toMatrix (cellFrame b u i)).det` using `by rw [hcell, det_uniMat]; exact isUnit_one`.

Establish `hchg : (cellFrame b u i).toMatrix (c i) = (uniMat u i)⁻¹ * (b i).toMatrix (c i)`. Rewrite using `[← hcell, ← Basis.toMatrix_mul_toMatrix (b i) (cellFrame b u i) (c i), ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h1, Matrix.one_mul]`. Use `show FullFlag.ofBasis (c i) = FullFlag.ofBasis (cellFrame b u i) ↔ _`. Rewrite using `[FullFlag.ofBasis_eq_ofBasis_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg, hgc⟩`. Rewrite using `[← hchg, ← hgc, toMatrix_basisMulGL]`. Conclude with `hg`. Introduce `h`. Use `⟨basisChange (cellFrame b u i) (c i), ?_, basisMulGL_basisChange _ _⟩` and prove the remaining obligations.

Rewrite using `[mem_upperTriangularGL]`. Introduce `a m hm`. Rewrite using `[coe_basisChange, hchg]`. Conclude with `h hm`.
-/
theorem flags_apply_eq_cellMap_iff (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b c : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) :
    c.flags i = cellMap b u i ↔ ((uniMat u i)⁻¹ * (b i).toMatrix (c i)).BlockTriangular id := by
  have hcell : (b i).toMatrix (cellFrame b u i) = uniMat u i := by
    ext a m
    rw [Basis.toMatrix_apply, cellFrame_apply]
    simp [Finsupp.single_apply]
  have h1 : IsUnit ((b i).toMatrix (cellFrame b u i)).det := by rw [hcell, det_uniMat]; exact isUnit_one
  have hchg : (cellFrame b u i).toMatrix (c i) = (uniMat u i)⁻¹ * (b i).toMatrix (c i) := by
    rw [← hcell, ← Basis.toMatrix_mul_toMatrix (b i) (cellFrame b u i) (c i), ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ h1, Matrix.one_mul]
  show FullFlag.ofBasis (c i) = FullFlag.ofBasis (cellFrame b u i) ↔ _
  rw [FullFlag.ofBasis_eq_ofBasis_iff]
  constructor
  · rintro ⟨g, hg, hgc⟩
    rw [← hchg, ← hgc, toMatrix_basisMulGL]
    exact hg
  · intro h
    refine ⟨basisChange (cellFrame b u i) (c i), ?_, basisMulGL_basisChange _ _⟩
    rw [mem_upperTriangularGL]
    intro a m hm
    rw [coe_basisChange, hchg]
    exact h hm

section Reg
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/- English proof (translation)
Use `(regFns k V).algebraMap_mem x` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.
-/
theorem const_mem_regFns (x : k) : (fun _ : Frames k V => x) ∈ regFns k V := by
  convert (regFns k V).algebraMap_mem x
  rfl

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin (Or.inl ⟨i, (b i).coord a, l, by funext c; simp [Basis.toMatrix_apply]⟩)`.
-/
theorem toMatrix_entry_mem_regFns (b : Frames k V) (i : ι) (a l : Fin (finrank k (V i))) :
    (fun c : Frames k V => (b i).toMatrix (c i) a l) ∈ regFns k V :=
  Algebra.subset_adjoin (Or.inl ⟨i, (b i).coord a, l, by funext c; simp [Basis.toMatrix_apply]⟩)

/- English proof (translation)
Establish `: (fun x => (M x).det) = ∑ σ : Equiv.Perm (Fin m), (fun _ : Frames k V => ((Equiv.Perm.sign σ : ℤ) : k)) * ∏ a, fun x => M x (σ a) a`. Use function extensionality and compare the values at `x`. Simplify using `[Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]`. Rewrite using `[this]`. Conclude with `Subalgebra.sum_mem _ fun σ _ => mul_mem (const_mem_regFns _) (Subalgebra.prod_mem _ fun a _ => hM _ _)`.
-/
theorem det_mem_regFns {m : ℕ} (M : Frames k V → Matrix (Fin m) (Fin m) k)
    (hM : ∀ a c, (fun x => M x a c) ∈ regFns k V) : (fun x => (M x).det) ∈ regFns k V := by
  have : (fun x => (M x).det) = ∑ σ : Equiv.Perm (Fin m),
      (fun _ : Frames k V => ((Equiv.Perm.sign σ : ℤ) : k)) * ∏ a, fun x => M x (σ a) a := by
    funext x
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun σ _ => mul_mem (const_mem_regFns _) (Subalgebra.prod_mem _ fun a _ => hM _ _)
end Reg

/- English proof (translation)
The claim follows from `det_mem_regFns (fun c => leadBlock ((b i).toMatrix (c i)) m) fun _ _ => toMatrix_entry_mem_regFns b i _ _`.
-/
theorem leadMinor_toMatrix_mem_regFns (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b : Frames k V) (i : ι) (m : Fin (finrank k (V i))) :
    (fun c : Frames k V => leadMinor ((b i).toMatrix (c i)) m) ∈ regFns k V :=
  det_mem_regFns (fun c => leadBlock ((b i).toMatrix (c i)) m) fun _ _ => toMatrix_entry_mem_regFns b i _ _

/- English proof (translation)
Establish `: (fun c : Frames k V => luNum ((b i).toMatrix (c i)) a m) = ∑ l : Fin (m + 1), (fun c : Frames k V => (b i).toMatrix (c i) a (Fin.castLE m.isLt l)) * fun c => ((leadBlock ((b i).toMatrix (c i)) m).updateCol l (Pi.single (Fin.last m) 1)).det`. Use function extensionality and compare the values at `c`. Simplify using `[luNum, Finset.sum_apply, Matrix.cramer_apply]`. Rewrite using `[this]`. Use `Subalgebra.sum_mem _ fun l _ => mul_mem (toMatrix_entry_mem_regFns b i _ _) (det_mem_regFns _ fun a' c' => ?_)` and prove the remaining obligations.

Distinguish the cases in `h : c' = l`. Simplify using `only [Matrix.updateCol_apply, h, if_true]`. Conclude with `const_mem_regFns _`. Simplify using `only [Matrix.updateCol_apply, h, if_false]`. Conclude with `toMatrix_entry_mem_regFns b i _ _`.
-/
theorem luNum_toMatrix_mem_regFns (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b : Frames k V) (i : ι) (a m : Fin (finrank k (V i))) :
    (fun c : Frames k V => luNum ((b i).toMatrix (c i)) a m) ∈ regFns k V := by
  have : (fun c : Frames k V => luNum ((b i).toMatrix (c i)) a m) = ∑ l : Fin (m + 1),
      (fun c : Frames k V => (b i).toMatrix (c i) a (Fin.castLE m.isLt l)) *
        fun c => ((leadBlock ((b i).toMatrix (c i)) m).updateCol l (Pi.single (Fin.last m) 1)).det := by
    funext c
    simp [luNum, Finset.sum_apply, Matrix.cramer_apply]
  rw [this]
  refine Subalgebra.sum_mem _ fun l _ => mul_mem (toMatrix_entry_mem_regFns b i _ _) (det_mem_regFns _ fun a' c' => ?_)
  by_cases h : c' = l
  · simp only [Matrix.updateCol_apply, h, if_true]
    exact const_mem_regFns _
  · simp only [Matrix.updateCol_apply, h, if_false]
    exact toMatrix_entry_mem_regFns b i _ _

/- English proof (translation)
Introduce `m`. Establish `hLd : L.det = 1` using `by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]`. Establish `hUd : ∀ l, U l l ≠ 0`. Establish `: U.det ≠ 0`. Rewrite `hdet` using `[Matrix.det_mul, hLd, one_mul]`.

Conclude with `hdet.ne_zero`. Rewrite `this` using `[Matrix.det_of_upperTriangular hU]`. Conclude with `fun l => Finset.prod_ne_zero_iff.1 this l (Finset.mem_univ _)`. Establish `hblock : leadBlock (L * U) m = leadBlock L m * leadBlock U m`. Use extensionality with `a c`.

Simplify using `only [leadBlock, Matrix.submatrix_apply, Matrix.mul_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun _ => rfl)` and prove the remaining obligations. Establish `ha` using `a.isLt`. Establish `: Fin.castLE m.isLt a < l`.

Rewrite using `[Fin.lt_def, Fin.coe_castLE]`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩`. Rewrite using `[hL (by simpa using this), zero_mul]`.

Rewrite using `[leadMinor, hblock, Matrix.det_mul, Matrix.det_of_lowerTriangular (leadBlock L m) (fun a c h => hL (show OrderDual.toDual (Fin.castLE m.isLt c) < OrderDual.toDual (Fin.castLE m.isLt a) by`. Rewrite using `[OrderDual.toDual_lt_toDual, Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]`. Conclude with `Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h))),`. Use the proof step `Matrix.det_of_upperTriangular (M := leadBlock U m) (fun a c h => hU (show Fin.castLE m.isLt c < Fin.castLE m.isLt a by`. Rewrite using `[Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]`.

Conclude with `Fin.lt_def.1 h))]`. Simplify using `only [leadBlock, Matrix.submatrix_apply, hL1, Finset.prod_const_one, one_mul]`. Conclude with `Finset.prod_ne_zero_iff.2 fun l _ => hUd _`.
-/
theorem leadMinor_mul_ne_zero {k : Type} [Field k] {n : ℕ} (L U : Matrix (Fin n) (Fin n) k) (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) (hU : U.BlockTriangular id) (hdet : IsUnit (L * U).det) : ∀ m, leadMinor (L * U) m ≠ 0 := by
  intro m
  have hLd : L.det = 1 := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  have hUd : ∀ l, U l l ≠ 0 := by
    have : U.det ≠ 0 := by
      rw [Matrix.det_mul, hLd, one_mul] at hdet
      exact hdet.ne_zero
    rw [Matrix.det_of_upperTriangular hU] at this
    exact fun l => Finset.prod_ne_zero_iff.1 this l (Finset.mem_univ _)
  have hblock : leadBlock (L * U) m = leadBlock L m * leadBlock U m := by
    ext a c
    simp only [leadBlock, Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun _ => rfl)
    have ha := a.isLt
    have : Fin.castLE m.isLt a < l := by
      rw [Fin.lt_def, Fin.coe_castLE]
      by_contra h
      push_neg at h
      exact hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩
    rw [hL (by simpa using this), zero_mul]
  rw [leadMinor, hblock, Matrix.det_mul,
    Matrix.det_of_lowerTriangular (leadBlock L m) (fun a c h => hL (show OrderDual.toDual (Fin.castLE m.isLt c) < OrderDual.toDual (Fin.castLE m.isLt a) by
      rw [OrderDual.toDual_lt_toDual, Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h))),
    Matrix.det_of_upperTriangular (M := leadBlock U m) (fun a c h => hU (show Fin.castLE m.isLt c < Fin.castLE m.isLt a by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact Fin.lt_def.1 h))]
  simp only [leadBlock, Matrix.submatrix_apply, hL1, Finset.prod_const_one, one_mul]
  exact Finset.prod_ne_zero_iff.2 fun l _ => hUd _

/- English proof (translation)
Set `X : Matrix (Fin n) (Fin n) k` to `fun l m => if h : (l : ℕ) ≤ m then (leadBlock P m).cramer (Pi.single (Fin.last m) 1) ⟨l, Nat.lt_succ_of_le h⟩ / leadMinor P m else 0`. Use `⟨X, fun a c hac => ?_, ?_⟩` and prove the remaining obligations. Establish `: ¬ (a : ℕ) ≤ c` using `not_le.2 (Fin.lt_def.1 hac)`. Simplify using `only [X, dif_neg this]`. Use extensionality with `a m`.

Establish `key : (P * X) a m = luNum P a m / leadMinor P m`. Rewrite using `[Matrix.mul_apply, luNum, Finset.sum_div]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun l => ?_)` and prove the remaining obligations. Establish `hm` using `m.isLt`.

Establish `hn : ¬ (l : ℕ) ≤ m` using `fun h => hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩`. Simplify using `only [X, dif_neg hn, mul_zero]`. Establish `hl : ((Fin.castLE m.isLt l : Fin n) : ℕ) ≤ m` using `by simpa using Nat.lt_succ_iff.1 l.isLt`. Simplify using `only [X, dif_pos hl, mul_div_assoc]`. Both sides reduce to the same expression.

Rewrite using `[key]`. Break down `lt_or_ge m a with h | h` into its components or cases. Rewrite using `[luLower_apply_of_lt _ h]`. Establish `hmul` using `congrFun (Matrix.mulVec_cramer (leadBlock P m) (Pi.single (Fin.last m) 1)) ⟨a, Nat.lt_succ_of_le h⟩`. Establish `e : luNum P a m = (Matrix.mulVec (leadBlock P m) ((leadBlock P m).cramer (Pi.single (Fin.last m) 1))) ⟨a, Nat.lt_succ_of_le h⟩` using `rfl`.

Rewrite using `[e, hmul, Pi.smul_apply, smul_eq_mul]`. Break down `(show a ≤ m from h).eq_or_lt with rfl | h'` into its components or cases. Establish `: (⟨a, Nat.lt_succ_of_le h⟩ : Fin (a + 1)) = Fin.last a` using `Fin.ext rfl`. Rewrite using `[this, Pi.single_eq_same, mul_one, luLower_apply_self]`. Conclude with `div_self (hΔ a)`.

Establish `: (⟨a, Nat.lt_succ_of_le h⟩ : Fin (m + 1)) ≠ Fin.last m` using `fun h2 => h'.ne (Fin.ext (by simpa [Fin.ext_iff] using h2))`. Rewrite using `[Pi.single_eq_of_ne this, mul_zero, zero_div, luLower_lowerTriangular _ (by simpa using h')]`.
-/
theorem exists_upperTriangular_mul_eq_luLower {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (hΔ : ∀ m, leadMinor P m ≠ 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, X.BlockTriangular id ∧ P * X = luLower P := by
  classical
  let X : Matrix (Fin n) (Fin n) k := fun l m => if h : (l : ℕ) ≤ m then
    (leadBlock P m).cramer (Pi.single (Fin.last m) 1) ⟨l, Nat.lt_succ_of_le h⟩ / leadMinor P m else 0
  refine ⟨X, fun a c hac => ?_, ?_⟩
  · have : ¬ (a : ℕ) ≤ c := not_le.2 (Fin.lt_def.1 hac)
    simp only [X, dif_neg this]
  · ext a m
    have key : (P * X) a m = luNum P a m / leadMinor P m := by
      rw [Matrix.mul_apply, luNum, Finset.sum_div]
      symm
      refine Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun l => ?_)
      · have hm := m.isLt
        have hn : ¬ (l : ℕ) ≤ m := fun h => hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩
        simp only [X, dif_neg hn, mul_zero]
      · have hl : ((Fin.castLE m.isLt l : Fin n) : ℕ) ≤ m := by simpa using Nat.lt_succ_iff.1 l.isLt
        simp only [X, dif_pos hl, mul_div_assoc]
        rfl
    rw [key]
    rcases lt_or_ge m a with h | h
    · rw [luLower_apply_of_lt _ h]
    · have hmul := congrFun (Matrix.mulVec_cramer (leadBlock P m) (Pi.single (Fin.last m) 1))
        ⟨a, Nat.lt_succ_of_le h⟩
      have e : luNum P a m = (Matrix.mulVec (leadBlock P m) ((leadBlock P m).cramer (Pi.single (Fin.last m) 1)))
          ⟨a, Nat.lt_succ_of_le h⟩ := rfl
      rw [e, hmul, Pi.smul_apply, smul_eq_mul]
      rcases (show a ≤ m from h).eq_or_lt with rfl | h'
      · have : (⟨a, Nat.lt_succ_of_le h⟩ : Fin (a + 1)) = Fin.last a := Fin.ext rfl
        rw [this, Pi.single_eq_same, mul_one, luLower_apply_self]
        exact div_self (hΔ a)
      · have : (⟨a, Nat.lt_succ_of_le h⟩ : Fin (m + 1)) ≠ Fin.last m := fun h2 =>
          h'.ne (Fin.ext (by simpa [Fin.ext_iff] using h2))
        rw [Pi.single_eq_of_ne this, mul_zero, zero_div, luLower_lowerTriangular _ (by simpa using h')]

section
variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Establish `hdet : IsUnit L.det` using `by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]`. Use `letI := L.invertibleOfIsUnitDet hdet`. Establish `hT' : T = L⁻¹ * L'`. Rewrite using `[← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]`. Establish `hlow : T.BlockTriangular OrderDual.toDual` using `hT' ▸ (Matrix.blockTriangular_inv_of_blockTriangular hL).mul hL'`.

Establish `hT1 : T = 1`. Use extensionality with `a c`. Break down `lt_trichotomy a c with h1 | rfl | h1` into its components or cases. Rewrite using `[hlow (by simpa using h1), Matrix.one_apply_ne h1.ne]`. Use `congrFun (congrFun h a) a` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single a (fun l _ hl => ?_) (by simp), hL1, hL'1, one_mul]`. Rewrite using `[this, Matrix.one_apply_eq]`. Break down `lt_or_gt_of_ne hl with h2 | h2` into its components or cases. Rewrite using `[hlow (by simpa using h2), mul_zero]`. Rewrite using `[hL (by simpa using h2), zero_mul]`.

Rewrite using `[hT h1, Matrix.one_apply_ne h1.ne']`. Rewrite using `[← h, hT1, Matrix.mul_one]`.
-/
theorem eq_of_mul_upperTriangular {L L' T : Matrix (Fin n) (Fin n) k} (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) (hL' : L'.BlockTriangular OrderDual.toDual) (hL'1 : ∀ a, L' a a = 1)
    (hT : T.BlockTriangular id) (h : L * T = L') : L = L' := by
  have hdet : IsUnit L.det := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  letI := L.invertibleOfIsUnitDet hdet
  have hT' : T = L⁻¹ * L' := by
    rw [← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hlow : T.BlockTriangular OrderDual.toDual := hT' ▸ (Matrix.blockTriangular_inv_of_blockTriangular hL).mul hL'
  have hT1 : T = 1 := by
    ext a c
    rcases lt_trichotomy a c with h1 | rfl | h1
    · rw [hlow (by simpa using h1), Matrix.one_apply_ne h1.ne]
    · have := congrFun (congrFun h a) a
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun l _ hl => ?_) (by simp), hL1, hL'1, one_mul] at this
      · rw [this, Matrix.one_apply_eq]
      · rcases lt_or_gt_of_ne hl with h2 | h2
        · rw [hlow (by simpa using h2), mul_zero]
        · rw [hL (by simpa using h2), zero_mul]
    · rw [hT h1, Matrix.one_apply_ne h1.ne']
  rw [← h, hT1, Matrix.mul_one]

/- English proof (translation)
Establish `hLdet : IsUnit L.det` using `by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]`. Establish `hPLU : L * (L⁻¹ * P) = P` using `by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLdet, Matrix.one_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hU`. Establish `hΔ : ∀ m, leadMinor P m ≠ 0`.

Use `leadMinor_mul_ne_zero L _ hL hL1 hU (by rw [hPLU]; exact hP)` as an intermediate fact. Rewrite `this` using `[hPLU]`. Then use the resulting hypothesis. Use `⟨hΔ, ?_⟩` and prove the remaining obligations. Take `⟨X, hX, hPX⟩` from `exists_upperTriangular_mul_eq_luLower P hΔ`. Use `eq_of_mul_upperTriangular hL hL1 (luLower_lowerTriangular P) (luLower_apply_self P) (hU.mul hX) ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.mul_assoc, hPLU, hPX]`. Introduce and unpack `⟨hΔ, rfl⟩`. Take `⟨X, hX, hPX⟩` from `exists_upperTriangular_mul_eq_luLower P hΔ`. Establish `hXdet : IsUnit X.det`. Use `congrArg Matrix.det hPX` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right (this ▸ hLdet)`. Use `letI := X.invertibleOfIsUnitDet hXdet`. Establish `: (luLower P)⁻¹ * P = X⁻¹`. Rewrite using `[← hPX, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]`.

Rewrite using `[this]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hX`.
-/
theorem lu_criterion (P L : Matrix (Fin n) (Fin n) k) (hP : IsUnit P.det) (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) : (L⁻¹ * P).BlockTriangular id ↔ (∀ m, leadMinor P m ≠ 0) ∧ L = luLower P := by
  have hLdet : IsUnit L.det := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  have hPLU : L * (L⁻¹ * P) = P := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLdet, Matrix.one_mul]
  constructor
  · intro hU
    have hΔ : ∀ m, leadMinor P m ≠ 0 := by
      have := leadMinor_mul_ne_zero L _ hL hL1 hU (by rw [hPLU]; exact hP)
      rwa [hPLU] at this
    refine ⟨hΔ, ?_⟩
    obtain ⟨X, hX, hPX⟩ := exists_upperTriangular_mul_eq_luLower P hΔ
    refine eq_of_mul_upperTriangular hL hL1 (luLower_lowerTriangular P) (luLower_apply_self P) (hU.mul hX) ?_
    rw [← Matrix.mul_assoc, hPLU, hPX]
  · rintro ⟨hΔ, rfl⟩
    obtain ⟨X, hX, hPX⟩ := exists_upperTriangular_mul_eq_luLower P hΔ
    have hXdet : IsUnit X.det := by
      have := congrArg Matrix.det hPX
      rw [Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_right (this ▸ hLdet)
    letI := X.invertibleOfIsUnitDet hXdet
    have : (luLower P)⁻¹ * P = X⁻¹ := by
      rw [← hPX, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [this]
    exact Matrix.blockTriangular_inv_of_blockTriangular hX
end

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def cellCoord (b c : Frames k V) : AffPts k (CellIdx k V) := fun j =>
  luNum ((b j.1).toMatrix (c j.1)) j.2.1.1 j.2.1.2 / leadMinor ((b j.1).toMatrix (c j.1)) j.2.1.2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H`. Use function extensionality and compare the values at `j`. Take `⟨i, ⟨⟨a, m⟩, h⟩⟩` from `j`. Use `congrFun (congrFun (H i) a) m` as an intermediate fact.

Rewrite `this` using `[uniMat_apply_of_lt u i h, luLower_apply_of_lt _ h]`. Then use the resulting hypothesis. Introduce and unpack `rfl i`. Use extensionality with `a m`. Break down `lt_trichotomy a m with h | rfl | h` into its components or cases. Rewrite using `[uniMat_apply_of_gt _ i h, luLower_lowerTriangular _ (by simpa using h)]`.

Rewrite using `[uniMat_apply_self, luLower_apply_self]`. Rewrite using `[uniMat_apply_of_lt _ i h, luLower_apply_of_lt _ h]`. Both sides reduce to the same expression.
-/
theorem uniMat_eq_luLower_iff (b c : Frames k V) (u : AffPts k (CellIdx k V)) :
    (∀ i, uniMat u i = luLower ((b i).toMatrix (c i))) ↔ u = cellCoord b c := by
  constructor
  · intro H
    funext j
    obtain ⟨i, ⟨⟨a, m⟩, h⟩⟩ := j
    have := congrFun (congrFun (H i) a) m
    rwa [uniMat_apply_of_lt u i h, luLower_apply_of_lt _ h] at this
  · rintro rfl i
    ext a m
    rcases lt_trichotomy a m with h | rfl | h
    · rw [uniMat_apply_of_gt _ i h, luLower_lowerTriangular _ (by simpa using h)]
    · rw [uniMat_apply_self, luLower_apply_self]
    · rw [uniMat_apply_of_lt _ i h, luLower_apply_of_lt _ h]
      rfl

/- English proof (translation)
Establish `e : c.flags = cellMap b u ↔ ∀ i, c.flags i = cellMap b u i` using `⟨fun h _ => h ▸ rfl, fun h => funext h⟩`. Rewrite using `[← uniMat_eq_luLower_iff, e, ← forall_and]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[flags_apply_eq_cellMap_iff, lu_criterion _ _ (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _)) (uniMat_blockTriangular u i) (uniMat_apply_self u i), eq_comm (a := uniMat u i)]`.
-/
theorem flags_eq_cellMap_iff (b c : Frames k V) (u : AffPts k (CellIdx k V)) :
    c.flags = cellMap b u ↔ (∀ i m, leadMinor ((b i).toMatrix (c i)) m ≠ 0) ∧ u = cellCoord b c := by
  have e : c.flags = cellMap b u ↔ ∀ i, c.flags i = cellMap b u i := ⟨fun h _ => h ▸ rfl, fun h => funext h⟩
  rw [← uniMat_eq_luLower_iff, e, ← forall_and]
  refine forall_congr' fun i => ?_
  rw [flags_apply_eq_cellMap_iff, lu_criterion _ _ (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _))
    (uniMat_blockTriangular u i) (uniMat_apply_self u i), eq_comm (a := uniMat u i)]

section Assembly
variable {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def cellDet (b c : Frames k V) : k :=
  ∏ p : (Σ i, Fin (finrank k (V i))), leadMinor ((b p.1).toMatrix (c p.1)) p.2

/- English proof (translation)
Simplify using `[cellDet, Finset.prod_ne_zero_iff, Sigma.forall]`.
-/
theorem cellDet_ne_zero_iff (b c : Frames k V) :
    cellDet b c ≠ 0 ↔ ∀ i m, leadMinor ((b i).toMatrix (c i)) m ≠ 0 := by
  simp [cellDet, Finset.prod_ne_zero_iff, Sigma.forall]

/- English proof (translation)
Establish `: (fun c => cellDet b c) = ∏ p : (Σ i, Fin (finrank k (V i))), fun c : Frames k V => leadMinor ((b p.1).toMatrix (c p.1)) p.2`. Use function extensionality and compare the values at `c`. Simplify using `[cellDet, Finset.prod_apply]`. Rewrite using `[this]`. Conclude with `Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2`.
-/
theorem cellDet_mem (b : Frames k V) : (fun c => cellDet b c) ∈ regFns k V := by
  have : (fun c => cellDet b c) = ∏ p : (Σ i, Fin (finrank k (V i))),
      fun c : Frames k V => leadMinor ((b p.1).toMatrix (c p.1)) p.2 := by
    funext c
    simp [cellDet, Finset.prod_apply]
  rw [this]
  exact Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2

/- English proof (translation)
Take `⟨i, ⟨⟨a, m⟩, h⟩⟩` from `j`. Set `E : Frames k V → k` to `∏ p ∈ Finset.univ.erase (⟨i, m⟩ : Σ i, Fin (finrank k (V i))), fun c => leadMinor ((b p.1).toMatrix (c p.1)) p.2`. Establish `hE : E ∈ regFns k V` using `Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2`. Establish `: ((fun c => cellDet b c) ^ 2 * fun c => cellCoord b c ⟨i, ⟨⟨a, m⟩, h⟩⟩) = (fun c => cellDet b c) * (fun c => luNum ((b i).toMatrix (c i)) a m) * E`. Use function extensionality and compare the values at `c`.

Establish `hprod : cellDet b c = leadMinor ((b i).toMatrix (c i)) m * E c`. Simplify using `only [cellDet, E, Finset.prod_apply]`. Conclude with `(Finset.mul_prod_erase _ (fun p : (Σ i, Fin (finrank k (V i))) => leadMinor ((b p.1).toMatrix (c p.1)) p.2) (Finset.mem_univ (⟨i, m⟩ : Σ i, Fin (finrank k (V i))))).symm`. Simplify using `only [Pi.mul_apply, Pi.pow_apply, cellCoord]`. Distinguish the cases in `h0 : leadMinor ((b i).toMatrix (c i)) m = 0`.

Simplify using `[hprod, h0]`. Rewrite using `[hprod]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `mul_mem (mul_mem (cellDet_mem b) (luNum_toMatrix_mem_regFns k ι V b i a m)) hE`.
-/
theorem cellDet_sq_mul_mem (b : Frames k V) (j : CellIdx k V) :
    ((fun c => cellDet b c) ^ 2 * fun c => cellCoord b c j) ∈ regFns k V := by
  classical
  obtain ⟨i, ⟨⟨a, m⟩, h⟩⟩ := j
  let E : Frames k V → k := ∏ p ∈ Finset.univ.erase (⟨i, m⟩ : Σ i, Fin (finrank k (V i))),
    fun c => leadMinor ((b p.1).toMatrix (c p.1)) p.2
  have hE : E ∈ regFns k V := Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2
  have : ((fun c => cellDet b c) ^ 2 * fun c => cellCoord b c ⟨i, ⟨⟨a, m⟩, h⟩⟩) =
      (fun c => cellDet b c) * (fun c => luNum ((b i).toMatrix (c i)) a m) * E := by
    funext c
    have hprod : cellDet b c = leadMinor ((b i).toMatrix (c i)) m * E c := by
      simp only [cellDet, E, Finset.prod_apply]
      exact (Finset.mul_prod_erase _ (fun p : (Σ i, Fin (finrank k (V i))) =>
        leadMinor ((b p.1).toMatrix (c p.1)) p.2) (Finset.mem_univ (⟨i, m⟩ : Σ i, Fin (finrank k (V i))))).symm
    simp only [Pi.mul_apply, Pi.pow_apply, cellCoord]
    by_cases h0 : leadMinor ((b i).toMatrix (c i)) m = 0
    · simp [hprod, h0]
    · rw [hprod]; field_simp
  rw [this]
  exact mul_mem (mul_mem (cellDet_mem b) (luNum_toMatrix_mem_regFns k ι V b i a m)) hE

/- English proof (translation)
Use extensionality with `c`. Simplify using `only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq, cellDet_ne_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, h⟩`. Take `⟨h1, rfl⟩` from `(flags_eq_cellMap_iff b c u).1 h.symm`.

Conclude with `⟨h1, hu⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨_, h2, ((flags_eq_cellMap_iff b c _).2 ⟨h1, rfl⟩).symm⟩`.
-/
theorem preimage_image_cellMap (b : Frames k V) (O : Set (AffPts k (CellIdx k V))) :
    Frames.flags ⁻¹' (cellMap b '' O) = {c | cellDet b c ≠ 0 ∧ cellCoord b c ∈ O} := by
  ext c
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq, cellDet_ne_zero_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨h1, rfl⟩ := (flags_eq_cellMap_iff b c u).1 h.symm
    exact ⟨h1, hu⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, ((flags_eq_cellMap_iff b c _).2 ⟨h1, rfl⟩).symm⟩

/- English proof (translation)
Establish `hO' : GenerateOpen {s | ∃ p : MvPolynomial (CellIdx k V) k, s = {x : AffPts k (CellIdx k V) | MvPolynomial.eval x p ≠ 0}} O` using `hO`. Use `clear hO`. Proceed by induction on `hO' with`. Consider the case `basic s hs`. Take `⟨q, rfl⟩` from `hs`.

Take `⟨N, hN⟩` from `exists_pow_mul_eval_mem (regFns k V) _ (fun j c => cellCoord b c j) (pow_mem (cellDet_mem b) 2) (cellDet_sq_mul_mem b) q`. Establish `: {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ {x : AffPts k (CellIdx k V) | MvPolynomial.eval x q ≠ 0}} = {c | ((fun c => cellDet b c) * (((fun c => cellDet b c) ^ 2) ^ N * fun c => MvPolynomial.eval (fun j => cellCoord b c j) q)) c ≠ 0}`. Use extensionality with `c`. Simplify using `only [Set.mem_setOf_eq, Pi.mul_apply, Pi.pow_apply, mul_ne_zero_iff, ne_eq, pow_eq_zero_iff', not_and, not_not]`. The claim follows by propositional logic.

Rewrite using `[this]`. Conclude with `isOpen_generateFrom_of_mem ⟨_, mul_mem (cellDet_mem b) hN, rfl⟩`. Consider the case `univ`. Use `(isClosed_zero (cellDet_mem b)).isOpen_compl using 1` and compare the differences between its conclusion and the goal. Use extensionality with `c`.

Simplify using the standard rewrite rules. Consider the case `inter s t _ _ hs ht`. Use `hs.inter ht using 1` and compare the differences between its conclusion and the goal. Use extensionality with `c`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq]`.

The claim follows by propositional logic. Consider the case `sUnion S _ hS`. Establish `: {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ ⋃₀ S} = ⋃ s ∈ S, {c | cellDet b c ≠ 0 ∧ cellCoord b c ∈ s}`. Use extensionality with `c`. Simplify using `only [Set.mem_setOf_eq, Set.mem_sUnion, Set.mem_iUnion, exists_prop]`.

The claim follows by propositional logic. Rewrite using `[this]`. Conclude with `isOpen_biUnion hS`.
-/
theorem isOpen_cellCoord_mem (b : Frames k V) {O : Set (AffPts k (CellIdx k V))} (hO : IsOpen O) :
    IsOpen {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ O} := by
  have hO' : GenerateOpen {s | ∃ p : MvPolynomial (CellIdx k V) k, s = {x : AffPts k (CellIdx k V) | MvPolynomial.eval x p ≠ 0}} O := hO
  clear hO
  induction hO' with
  | basic s hs =>
    obtain ⟨q, rfl⟩ := hs
    obtain ⟨N, hN⟩ := exists_pow_mul_eval_mem (regFns k V) _ (fun j c => cellCoord b c j) (pow_mem (cellDet_mem b) 2)
      (cellDet_sq_mul_mem b) q
    have : {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ {x : AffPts k (CellIdx k V) | MvPolynomial.eval x q ≠ 0}} =
        {c | ((fun c => cellDet b c) * (((fun c => cellDet b c) ^ 2) ^ N *
          fun c => MvPolynomial.eval (fun j => cellCoord b c j) q)) c ≠ 0} := by
      ext c
      simp only [Set.mem_setOf_eq, Pi.mul_apply, Pi.pow_apply, mul_ne_zero_iff, ne_eq, pow_eq_zero_iff', not_and,
        not_not]
      tauto
    rw [this]
    exact isOpen_generateFrom_of_mem ⟨_, mul_mem (cellDet_mem b) hN, rfl⟩
  | univ =>
    convert (isClosed_zero (cellDet_mem b)).isOpen_compl using 1
    ext c
    simp
  | inter s t _ _ hs ht =>
    convert hs.inter ht using 1
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  | sUnion S _ hS =>
    have : {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ ⋃₀ S} =
        ⋃ s ∈ S, {c | cellDet b c ≠ 0 ∧ cellCoord b c ∈ s} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_sUnion, Set.mem_iUnion, exists_prop]
      tauto
    rw [this]
    exact isOpen_biUnion hS
end Assembly

/- English proof (translation)
Introduce `O hO`. Rewrite using `[isOpen_coinduced, preimage_image_cellMap]`. Conclude with `isOpen_cellCoord_mem b hO`.
-/
theorem isOpenMap_cellMap (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) : IsOpenMap (cellMap b) := by
  intro O hO
  rw [isOpen_coinduced, preimage_image_cellMap]
  exact isOpen_cellCoord_mem b hO

end GlobalTheory.FlagPts

/- English proof (translation)
The claim follows from `GlobalTheory.FlagPts.isOpenMap_cellMap`.
-/
example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpenMap (cellMap b) := GlobalTheory.FlagPts.isOpenMap_cellMap
