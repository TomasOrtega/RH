import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

section Mat

variable {F : Type} [Field F] {r : ℕ} {k : Fin r} {H U : Matrix (Fin r) (Fin r) F}

/- English proof (translation)
Establish `: (H * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `: H i m = (1 : Matrix (Fin r) (Fin r) F) i m`. Assume the negation of the conclusion as `hne`.

Conclude with `hi (hH i m hne).1`. Rewrite using `[this]`. Rewrite using `[this, one_mul]`.
-/
theorem corner_row (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (N : Matrix (Fin r) (Fin r) F) {i : Fin r} (hi : ¬ i < k) (j : Fin r) : (H * N) i j = N i j := by
  have : (H * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : H i m = (1 : Matrix (Fin r) (Fin r) F) i m := by
      by_contra hne
      exact hi (hH i m hne).1
    rw [this]
  rw [this, one_mul]

/- English proof (translation)
Use `conv_rhs => rw [← mul_one (U - 1)]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : m < k`.

Rewrite using `[Matrix.sub_apply, hU i m hm, sub_self, zero_mul, zero_mul]`. Establish `: H m j = (1 : Matrix (Fin r) (Fin r) F) m j`. Assume the negation of the conclusion as `hne`. Conclude with `hm (hH m j hne).1`. Rewrite using `[this]`.
-/
theorem corner_nil_mul (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → U i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (U - 1) * H = U - 1 := by
  conv_rhs => rw [← mul_one (U - 1)]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m < k
  · rw [Matrix.sub_apply, hU i m hm, sub_self, zero_mul, zero_mul]
  · have : H m j = (1 : Matrix (Fin r) (Fin r) F) m j := by
      by_contra hne
      exact hm (hH m j hne).1
    rw [this]

end Mat

variable {F : Type} [Field F] {r : ℕ}

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.mul_inv_eq_iff_eq_mul, add_mul, mul_assoc, corner_nil_mul hH hU, Units.val_mul, mul_sub, one_mul, mul_one, add_sub_cancel]`.
-/
theorem corner_conj_val {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + (h : Matrix (Fin r) (Fin r) F) * ((u : Matrix (Fin r) (Fin r) F) - 1) := by
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, add_mul, mul_assoc, corner_nil_mul hH hU, Units.val_mul,
    mul_sub, one_mul, mul_one, add_sub_cancel]

/- English proof (translation)
Rewrite using `[corner_conj_val h u hH hU]`. Use `⟨fun i j hi => ?_, fun i j hj => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, corner_row hH _ hi, Matrix.sub_apply, add_sub_cancel]`. Rewrite using `[Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]`. Introduce `m _`.

Rewrite using `[Matrix.sub_apply, hU m j hj, sub_self, mul_zero]`. Establish `: (h : Matrix (Fin r) (Fin r) F) i k = (1 : Matrix (Fin r) (Fin r) F) i k`. Assume the negation of the conclusion as `hne`. Conclude with `lt_irrefl _ (hH i k hne).2`. Rewrite using `[mul_sub, mul_one, Matrix.add_apply, Matrix.sub_apply, this, add_sub_cancel]`.
-/
theorem corner_conj {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (∀ i j : Fin r, ¬ i < k → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (u : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i j : Fin r, j.val < k.val → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (1 : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i : Fin r, ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      ((h : Matrix (Fin r) (Fin r) F) * (u : Matrix (Fin r) (Fin r) F)) i k) := by
  rw [corner_conj_val h u hH hU]
  refine ⟨fun i j hi => ?_, fun i j hj => ?_, fun i => ?_⟩
  · rw [Matrix.add_apply, corner_row hH _ hi, Matrix.sub_apply, add_sub_cancel]
  · rw [Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro m _
    rw [Matrix.sub_apply, hU m j hj, sub_self, mul_zero]
  · have : (h : Matrix (Fin r) (Fin r) F) i k = (1 : Matrix (Fin r) (Fin r) F) i k := by
      by_contra hne
      exact lt_irrefl _ (hH i k hne).2
    rw [mul_sub, mul_one, Matrix.add_apply, Matrix.sub_apply, this, add_sub_cancel]

/- English proof (translation)
Rewrite `hne`, the goal using `[Submodule.ne_bot_iff]`. Take `⟨v, hv, hv0⟩` from `hne`. Rewrite `hv` using `[mem_eig]`. Use `⟨σ h⁻¹ v, ?_, fun h0 => hv0 ?_⟩` and prove the remaining obligations. Rewrite using `[mem_eig]`.

Introduce and unpack `u ⟨hu, hU⟩`. Take `⟨c1, c2, c3⟩` from `corner_conj (h : GL (Fin r) F) (u : GL (Fin r) F) hH hU`. Establish `hc : ((h * u * h⁻¹ : blockTri (κ` using `F) b) : GL (Fin r) F) = (h : GL (Fin r) F) * (u : GL (Fin r) F) * (h : GL (Fin r) F)⁻¹ := rfl`. Establish `hmem : h * u * h⁻¹ ∈ colSet F b k.val`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hij' : j < i` using `hij`. Distinguish the cases in `hj : j < k`. Rewrite using `[c2 i j hj, Matrix.one_apply_ne (ne_of_gt hij')]`.

Rewrite using `[c1 i j (fun hi => hj (hij'.trans hi)), unip_lower hu hij']`. Distinguish the cases in `hi : i < k`. Rewrite using `[c2 i i hi, Matrix.one_apply_eq]`. Rewrite using `[c1 i i hi, unip_diag hu]`. Rewrite using `[hc]`.

Conclude with `c2`. Establish `hχ : colChar ψ b k l (h * u * h⁻¹) = colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) u`. Unfold `colChar`. Rewrite using `[hc]`. Use `congr 2`.

Simplify using `only [c3]`. Use `congrFun (Matrix.vecMul_vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) k` as an intermediate fact. Conclude with `this.symm`. Unfold `edgeSum`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs with hij`. Use `c1 i j fun hi => ?_` and prove the remaining obligations. Establish `h1 : j.val = i.val + 1` using `hij.1.1`. Establish `h2 : k.val < j.val` using `hij.2`. Establish `h3 : i.val < k.val` using `hi`.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Establish `e : σ u (σ h⁻¹ v) = σ h⁻¹ (σ (h * u * h⁻¹) v)`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`.

Use `group`. Rewrite using `[e, hv _ hmem, map_smul, hχ]`. Establish `: σ h (σ h⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[← this, h0, map_zero]`.
-/
theorem eig_colChar_vecMul_ne_bot (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (l : Fin r → F)
    (h : blockTri (κ := F) b)
    (hH : ∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j →
      i < k ∧ j < k)
    (hne : eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥) :
    eig σ (colSet F b k.val)
      (colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨v, hv, hv0⟩ := hne
  rw [mem_eig] at hv
  refine ⟨σ h⁻¹ v, ?_, fun h0 => hv0 ?_⟩
  · rw [mem_eig]
    rintro u ⟨hu, hU⟩
    obtain ⟨c1, c2, c3⟩ := corner_conj (h : GL (Fin r) F) (u : GL (Fin r) F) hH hU
    have hc : ((h * u * h⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) =
        (h : GL (Fin r) F) * (u : GL (Fin r) F) * (h : GL (Fin r) F)⁻¹ := rfl
    have hmem : h * u * h⁻¹ ∈ colSet F b k.val := by
      refine ⟨?_, ?_⟩
      · rw [hc]
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · have hij' : j < i := hij
          by_cases hj : j < k
          · rw [c2 i j hj, Matrix.one_apply_ne (ne_of_gt hij')]
          · rw [c1 i j (fun hi => hj (hij'.trans hi)), unip_lower hu hij']
        · by_cases hi : i < k
          · rw [c2 i i hi, Matrix.one_apply_eq]
          · rw [c1 i i hi, unip_diag hu]
      · rw [hc]; exact c2
    have hχ : colChar ψ b k l (h * u * h⁻¹) =
        colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) u := by
      unfold colChar
      rw [hc]
      congr 2
      · simp only [c3]
        have := congrFun (Matrix.vecMul_vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
          ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) k
        exact this.symm
      · unfold edgeSum
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hij
        · refine c1 i j fun hi => ?_
          have h1 : j.val = i.val + 1 := hij.1.1
          have h2 : k.val < j.val := hij.2
          have h3 : i.val < k.val := hi
          omega
        · rfl
    have e : σ u (σ h⁻¹ v) = σ h⁻¹ (σ (h * u * h⁻¹) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hv _ hmem, map_smul, hχ]
  · have : σ h (σ h⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← this, h0, map_zero]

end GlobalTheory.FinGL.LeviWh
