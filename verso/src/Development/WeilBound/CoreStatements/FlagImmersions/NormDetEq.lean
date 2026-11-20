import Development.WeilBound.CoreStatements.FlagImmersions.Transport

noncomputable section

namespace RootFieldNumerics

open Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace MS

/- English proof (translation)
Establish `h1 : C.submatrix e e * C⁻¹.submatrix e e = 1`. Rewrite using `[submatrix_mul_equiv, mul_nonsing_inv _ hC, submatrix_one_equiv]`. Use `set A := C.submatrix e e with hA`. Use `set B := C⁻¹.submatrix e e with hB`. Establish `h2 : A * fromBlocks 1 B.toBlocks₁₂ 0 B.toBlocks₂₂ = fromBlocks A.toBlocks₁₁ 0 A.toBlocks₂₁ 1`.

Rewrite `h1` using `[← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]`. Use `conv_lhs => rw [← fromBlocks_toBlocks A]`. Rewrite using `[fromBlocks_multiply, h1.2.1, h1.2.2.2]`. Simplify using the standard rewrite rules. Establish `h3` using `congrArg det h2`.

Rewrite `h3` using `[det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, mul_one, hA, det_submatrix_equiv_self]`. Conclude with `h3`.
-/
theorem jac {α β n : Type} [Fintype α] [Fintype β] [Fintype n] [DecidableEq α] [DecidableEq β] [DecidableEq n]
    (C : Matrix n n ℂ) (hC : IsUnit C.det) (e : α ⊕ β ≃ n) :
    C.det * (C⁻¹.submatrix (fun b => e (.inr b)) fun b => e (.inr b)).det =
      (C.submatrix (fun a => e (.inl a)) fun a => e (.inl a)).det := by
  have h1 : C.submatrix e e * C⁻¹.submatrix e e = 1 := by
    rw [submatrix_mul_equiv, mul_nonsing_inv _ hC, submatrix_one_equiv]
  set A := C.submatrix e e with hA
  set B := C⁻¹.submatrix e e with hB
  have h2 : A * fromBlocks 1 B.toBlocks₁₂ 0 B.toBlocks₂₂ = fromBlocks A.toBlocks₁₁ 0 A.toBlocks₂₁ 1 := by
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h1
    conv_lhs => rw [← fromBlocks_toBlocks A]
    rw [fromBlocks_multiply, h1.2.1, h1.2.2.2]
    simp
  have h3 := congrArg det h2
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, mul_one, hA,
    det_submatrix_equiv_self] at h3
  exact h3

def headEquiv {N k : ℕ} (h : k ≤ N) : Fin k ≃ {a : Fin N // (a : ℕ) < k} where
  toFun i := ⟨Fin.castLE h i, i.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Rewrite using `[← det_submatrix_equiv_self e]`. Both sides reduce to the same expression.
-/
theorem det_head {N k : ℕ} {α : Type} [Fintype α] [DecidableEq α] (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ)
    (e : α ≃ {a : Fin N // (a : ℕ) < k}) :
    (gramHead hd k g).det = ((gramOf hd g).submatrix (fun a => (e a).1) fun a => (e a).1).det := by
  rw [← det_submatrix_equiv_self e]
  rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[gramOf, mul_apply, conjTranspose_apply]`.
-/
theorem gram_sub {N : ℕ} {α β : Type} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) (f : α → Fin N) (f' : β → Fin N) :
    (gramOf hd g).submatrix f f' = (g.submatrix id f)ᴴ * diagonal (fun i => (hd i : ℂ)) * g.submatrix id f' := by
  ext a b
  simp [gramOf, mul_apply, conjTranspose_apply]

/- English proof (translation)
Establish `h1` using `(hΓ.submatrix (Fin.castLE_injective h)).det_pos`. Unfold `leadMinor`. Rewrite using `[dif_pos h]`. Conclude with `(Complex.re_eq_norm.2 h1.le).symm`.
-/
theorem norm_det_eq {r s : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.PosDef) (h : s ≤ r) :
    ‖(Γ.submatrix (Fin.castLE h) (Fin.castLE h)).det‖ = leadMinor Γ s := by
  have h1 := (hΓ.submatrix (Fin.castLE_injective h)).det_pos
  unfold leadMinor
  rw [dif_pos h]
  exact (Complex.re_eq_norm.2 h1.le).symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [leadMinor_size_zero]`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, ih (by omega), grLog]`. Distinguish the cases in `h1 : n < p`.

Establish `a1` using `leadMinor_pos_of_posDef h (s := n + 1) h1`. Establish `a2` using `leadMinor_pos_of_posDef h (s := n) h1.le`. Rewrite using `[if_pos h1.le, if_pos h1, if_pos (show n + 1 ≤ p from h1), Real.log_sqrt (div_pos a1 a2).le, Real.log_div a1.ne' a2.ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `a1` using `leadMinor_pos_of_posDef h' (s := p + q - 1 - n + 1) (by omega)`.

Establish `a2` using `leadMinor_pos_of_posDef h' (s := p + q - 1 - n) (by omega)`. Rewrite using `[if_neg h1, if_neg (show ¬ n + 1 ≤ p from h1), Real.log_sqrt (div_pos a1 a2).le, Real.log_div a1.ne' a2.ne', show p + q - 1 - n + 1 = p + q - n by omega, show p + q - 1 - n = p + q - (n + 1) by omega]`. Use `split_ifs with h2`. Take `rfl : n = p` from `by omega`. Rewrite using `[show n + q - n = q by omega]`.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_grLog {p q : ℕ} {Γ : Matrix (Fin p) (Fin p) ℂ} {Γ' : Matrix (Fin q) (Fin q) ℂ} (h : Γ.PosDef) (h' : Γ'.PosDef)
    (n : ℕ) (hn : n ≤ p + q) : ∑ k ∈ Finset.range n, grLog Γ Γ' k =
      if n ≤ p then Real.log (leadMinor Γ n) / 2
      else Real.log (leadMinor Γ p) / 2 + (Real.log (leadMinor Γ' (p + q - n)) - Real.log (leadMinor Γ' q)) / 2 := by
  induction n with
  | zero => simp [leadMinor_size_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega), grLog]
    by_cases h1 : n < p
    · have a1 := leadMinor_pos_of_posDef h (s := n + 1) h1
      have a2 := leadMinor_pos_of_posDef h (s := n) h1.le
      rw [if_pos h1.le, if_pos h1, if_pos (show n + 1 ≤ p from h1), Real.log_sqrt (div_pos a1 a2).le,
        Real.log_div a1.ne' a2.ne']
      ring
    · have a1 := leadMinor_pos_of_posDef h' (s := p + q - 1 - n + 1) (by omega)
      have a2 := leadMinor_pos_of_posDef h' (s := p + q - 1 - n) (by omega)
      rw [if_neg h1, if_neg (show ¬ n + 1 ≤ p from h1), Real.log_sqrt (div_pos a1 a2).le,
        Real.log_div a1.ne' a2.ne', show p + q - 1 - n + 1 = p + q - n by omega,
        show p + q - 1 - n = p + q - (n + 1) by omega]
      split_ifs with h2
      · obtain rfl : n = p := by omega
        rw [show n + q - n = q by omega]
        ring
      · ring

/- English proof (translation)
Use `(Finset.sum_map (Finset.Iic i) Fin.valEmbedding f).symm.trans ?_` and prove the remaining obligations. Rewrite using `[Fin.map_valEmbedding_Iic]`. Use `congr 1`. Use extensionality with `k`. Simplify using `[Nat.lt_succ_iff]`.
-/
theorem sum_Iic {N : ℕ} (i : Fin N) (f : ℕ → ℝ) : ∑ k ∈ Finset.Iic i, f k = ∑ k ∈ Finset.range (i + 1), f k := by
  refine (Finset.sum_map (Finset.Iic i) Fin.valEmbedding f).symm.trans ?_
  rw [Fin.map_valEmbedding_Iic]
  congr 1
  ext k
  simp [Nat.lt_succ_iff]

section

variable {p q : ℕ} {Γ : Matrix (Fin p) (Fin p) ℂ} {C : Matrix (Fin q) (Fin q) ℂ} {M : Matrix (Fin p) (Fin (p + q)) ℂ}
  {P : Matrix (Fin q) (Fin (p + q)) ℂ} {S : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}

/- English proof (translation)
Establish `h1 : (S * fromCols (-(Pᴴ * C)) (Mᴴ * Γ)) * fromRows P M = 1`. Rewrite using `[Matrix.mul_assoc, fromCols_mul_fromRows, ← hS, ← h]`. Use `congr 1`. Simplify using `only [Matrix.neg_mul]`. Normalize the expressions using the abelian group laws.

Establish `h2` using `(mul_eq_one_comm_of_equiv (finSumFinEquiv.symm.trans (Equiv.sumComm _ _))).1 h1`. Rewrite `h2` using `[mul_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj]`. Take `⟨a1, -, a3, -⟩` from `h2`. Use `⟨?_, ?_, fun m v h3 h4 => ?_⟩` and prove the remaining obligations. Establish `: M * S * Pᴴ * C * C⁻¹ = 0`.

Establish `e : M * S * Pᴴ * C = 0`. Rewrite using `[← neg_eq_zero, ← a3]`. Simplify using `[Matrix.mul_assoc]`. Rewrite using `[e, Matrix.zero_mul]`. Rewrite `this` using `[Matrix.mul_nonsing_inv_cancel_right _ _ hC]`. Then use the resulting hypothesis.

Establish `e : P * S * Pᴴ * C = -1`. Rewrite using `[← a1]`. Simplify using `[Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_nonsing_inv_cancel_right C (P * S * Pᴴ) hC, e]`. Simplify using the standard rewrite rules.

Rewrite using `[← Matrix.one_mul v, ← h1, Matrix.mul_assoc, fromRows_mul, h3, h4]`. Simplify using the standard rewrite rules.
-/
theorem blocks (hC : IsUnit C.det) (hS : S * S = 1) (h : Mᴴ * Γ * M - Pᴴ * C * P = S) :
    M * S * Pᴴ = 0 ∧ P * S * Pᴴ = -C⁻¹ ∧ ∀ (m : Type) (v : Matrix (Fin (p + q)) m ℂ), P * v = 0 → M * v = 0 → v = 0 := by
  have h1 : (S * fromCols (-(Pᴴ * C)) (Mᴴ * Γ)) * fromRows P M = 1 := by
    rw [Matrix.mul_assoc, fromCols_mul_fromRows, ← hS, ← h]
    congr 1
    simp only [Matrix.neg_mul]
    abel
  have h2 := (mul_eq_one_comm_of_equiv (finSumFinEquiv.symm.trans (Equiv.sumComm _ _))).1 h1
  rw [mul_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at h2
  obtain ⟨a1, -, a3, -⟩ := h2
  refine ⟨?_, ?_, fun m v h3 h4 => ?_⟩
  · have : M * S * Pᴴ * C * C⁻¹ = 0 := by
      have e : M * S * Pᴴ * C = 0 := by
        rw [← neg_eq_zero, ← a3]
        simp [Matrix.mul_assoc]
      rw [e, Matrix.zero_mul]
    rwa [Matrix.mul_nonsing_inv_cancel_right _ _ hC] at this
  · have e : P * S * Pᴴ * C = -1 := by
      rw [← a1]
      simp [Matrix.mul_assoc]
    rw [← Matrix.mul_nonsing_inv_cancel_right C (P * S * Pᴴ) hC, e]
    simp
  · rw [← Matrix.one_mul v, ← h1, Matrix.mul_assoc, fromRows_mul, h3, h4]
    simp

end

end MS

open MS

/- English proof (translation)
Introduce `p q Γ Γ' M Q L hΓ hΓ' h hL`. Use `set S : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := diagonal fun a => (sigForm (p + q) p a : ℂ) with hSd`. Use `set P := Q.map (starRingEnd ℂ) with hP`. Establish `hPQ : Qᵀ = Pᴴ`. Use extensionality with `a b`.

Simplify using `[hP]`. Establish `hC : Γ'ᵀ.PosDef` using `hΓ'.transpose`. Use `set C := Γ'ᵀ with hCd`. Establish `hCu : IsUnit C.det` using `(isUnit_iff_isUnit_det _).1 hC.isUnit`. Establish `hS : S * S = 1`.

Rewrite using `[hSd, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Unfold `sigForm`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hSH : Sᴴ = S`. Rewrite using `[hSd, diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.

Rewrite `h` using `[hPQ]`. Take `⟨b1, b2, b3⟩` from `blocks hCu hS h`. Establish `hqN : q ≤ p + q` using `by omega`. Set `fl : Fin q → Fin (p + q)` to `Fin.castLE hqN`. Set `fr : Fin p → Fin (p + q)` to `fun a => ⟨q + a, by omega⟩`.

Use `set g := perMat Q L with hg`. Establish `gl : g.submatrix id fl = (S * Pᴴ).submatrix id Fin.rev`. Use extensionality with `a b`. Establish `: (⟨q - 1 - b, by omega⟩ : Fin q) = b.rev` using `Fin.ext (by simp [Fin.val_rev]; omega)`. Simplify using `[hg, perMat, fl, hSd, ← hPQ, this]`.

Establish `gr : g.submatrix id fr = L`. Use extensionality with `a b`. Simplify using `[hg, perMat, fr]`. Use `set B : Matrix (Fin q) (Fin q) ℂ := C⁻¹.submatrix Fin.rev Fin.rev with hB`. Establish `hBp : B.PosDef` using `hC.inv.submatrix Fin.rev_injective`.

Use `set X : Matrix (Fin q) (Fin p) ℂ := (P * L).submatrix Fin.rev id with hX`. Establish `FourierUniquenessMirabolic : (gramOf (sigForm (p + q) p) g).submatrix fl fl = -B`. Rewrite using `[gram_sub, gl, ← hSd]`. Use `show ((S * Pᴴ)ᴴ * S * (S * Pᴴ)).submatrix Fin.rev Fin.rev = _`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, hSH, Matrix.mul_assoc P S S, hS, Matrix.mul_one, ← Matrix.mul_assoc, b2]`.

Both sides reduce to the same expression. Establish `WeakApproximationGL : (gramOf (sigForm (p + q) p) g).submatrix fl fr = X`. Rewrite using `[gram_sub, gl, gr, ← hSd]`. Use `show ((S * Pᴴ)ᴴ * S * L).submatrix Fin.rev id = _`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, hSH, Matrix.mul_assoc P S S, hS, Matrix.mul_one]`.

Establish `G21 : (gramOf (sigForm (p + q) p) g).submatrix fr fl = Xᴴ`. Rewrite using `[← WeakApproximationGL, gram_sub, gram_sub, ← hSd, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hSH, Matrix.mul_assoc]`. Establish `hBi : B⁻¹ = C.submatrix Fin.rev Fin.rev`. Use `inv_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[hB, ← submatrix_mul _ _ _ _ _ Fin.rev_bijective, nonsing_inv_mul _ hCu]`.

Conclude with `submatrix_one _ Fin.rev_injective`. Establish `G22 : (gramOf (sigForm (p + q) p) g).submatrix fr fr = Γ - Xᴴ * B⁻¹ * X`. Rewrite using `[gram_sub, gr, ← hSd, ← h, hBi, hX, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Fin.rev_bijective, ← submatrix_mul _ _ _ _ _ Fin.rev_bijective, submatrix_id_id, Matrix.mul_sub, Matrix.sub_mul]`. Use `congr 1`. Establish `: Lᴴ * (Mᴴ * Γ * M) * L = (M * L)ᴴ * Γ * (M * L)`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[this, hL]`. Simplify using the standard rewrite rules. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Establish `hBu : IsUnit B.det` using `(isUnit_iff_isUnit_det _).1 hBp.isUnit`.

Establish `lmq : ‖C.det‖ = leadMinor Γ' q`. Rewrite using `[← leadMinor_transpose, ← norm_det_eq hC le_rfl]`. Both sides reduce to the same expression. Establish `low : ∀ k (hk : k ≤ q), ‖(B.submatrix (Fin.castLE hk) (Fin.castLE hk)).det‖ = leadMinor Γ' (q - k) / leadMinor Γ' q`. Introduce `k hk`.

Establish `e1 : q - k + k = q` using `by omega`. Establish `j` using `congrArg norm (jac C hCu (finSumFinEquiv.trans (finCongr e1)))`. Establish `e2 : (C⁻¹.submatrix (fun b => (finSumFinEquiv.trans (finCongr e1)) (.inr b)) fun b => (finSumFinEquiv.trans (finCongr e1)) (.inr b)).submatrix Fin.revPerm Fin.revPerm = B.submatrix (Fin.castLE hk) (Fin.castLE hk)`. Use extensionality with `a b`. Simplify using `only [hB, submatrix_apply]`.

Establish `: ∀ a : Fin k, (finSumFinEquiv.trans (finCongr e1)) (Sum.inr (Fin.revPerm a)) = (Fin.castLE hk a).rev` using `fun a => Fin.ext (by have := a.2; simp [Fin.val_rev]; omega)`. Rewrite using `[this, this]`. Establish `e3 : (C.submatrix (fun b => (finSumFinEquiv.trans (finCongr e1)) (.inl b)) fun b => (finSumFinEquiv.trans (finCongr e1)) (.inl b)) = C.submatrix (Fin.castLE (Nat.sub_le q k)) (Fin.castLE (Nat.sub_le q k))`. Use extensionality with `a b`. Simplify using `only [submatrix_apply]`.

Use `congr 1`. Rewrite `j` using `[norm_mul, lmq, e3, norm_det_eq hC, leadMinor_transpose, ← det_submatrix_equiv_self Fin.revPerm, e2]`. Rewrite using `[← j, mul_div_cancel_left₀ _ (leadMinor_pos_of_posDef hΓ' le_rfl).ne']`. Establish `dlow : ∀ k, k ≤ q → ‖(gramHead (sigForm (p + q) p) k g).det‖ = leadMinor Γ' (q - k) / leadMinor Γ' q`. Introduce `k hk`.

Rewrite using `[det_head _ _ (headEquiv (hk.trans hqN)), ← low k hk]`. Establish `: ((gramOf (sigForm (p + q) p) g).submatrix (fun a => (headEquiv (hk.trans hqN) a).1) fun a => (headEquiv (hk.trans hqN) a).1) = -B.submatrix (Fin.castLE hk) (Fin.castLE hk)` using `by show _ = (-B).submatrix (Fin.castLE hk) (Fin.castLE hk)`. Rewrite using `[← FourierUniquenessMirabolic]`. Both sides reduce to the same expression. Rewrite using `[this, det_neg, norm_mul]`.

Simplify using the standard rewrite rules. Establish `dhigh : ∀ m, m ≤ p → ‖(gramHead (sigForm (p + q) p) (q + m) g).det‖ = leadMinor Γ m / leadMinor Γ' q`. Introduce `m hm`. Establish `hle : q + m ≤ p + q` using `by omega`. Rewrite using `[det_head _ _ (finSumFinEquiv.trans (headEquiv hle))]`.

Establish `: ((gramOf (sigForm (p + q) p) g).submatrix (fun a => ((finSumFinEquiv.trans (headEquiv hle)) a).1) fun a => ((finSumFinEquiv.trans (headEquiv hle)) a).1) = fromBlocks (-B) (X.submatrix id (Fin.castLE hm)) (Xᴴ.submatrix (Fin.castLE hm) id) ((Γ - Xᴴ * B⁻¹ * X).submatrix (Fin.castL …`. Rewrite using `[← FourierUniquenessMirabolic, ← G22, ← G21, ← WeakApproximationGL]`. Apply the tactic sequence `ext (a | a) (b | b) <;> rfl`. Establish `hnB : IsUnit (-B).det`. Rewrite using `[det_neg]`.

Conclude with `(isUnit_neg_one.pow _).mul hBu`. Set `_i` to `invertibleOfIsUnitDet _ hnB`. Establish `hi : ⅟(-B) = -B⁻¹`. Rewrite using `[invOf_eq_nonsing_inv]`. Use `inv_eq_right_inv ?_` and prove the remaining obligations.

Rewrite using `[Matrix.neg_mul, Matrix.mul_neg, neg_neg, mul_nonsing_inv _ hBu]`. Establish `e4 : (Γ - Xᴴ * B⁻¹ * X).submatrix (Fin.castLE hm) (Fin.castLE hm) - Xᴴ.submatrix (Fin.castLE hm) id * -B⁻¹ * X.submatrix id (Fin.castLE hm) = Γ.submatrix (Fin.castLE hm) (Fin.castLE hm)`. Use extensionality with `a b`. Simplify using `[mul_apply]`. Establish `e5` using `low q le_rfl`.

Rewrite `e5` using `[Nat.sub_self, leadMinor_size_zero]`. Establish `e6 : ‖B.det‖ = 1 / leadMinor Γ' q` using `e5`. Rewrite using `[this, det_fromBlocks₁₁, hi, e4, norm_mul, norm_det_eq hΓ, det_neg, norm_mul, e6]`. Simplify using `[div_eq_inv_mul]`. Establish `hNp : p + q - p = q` using `by omega`.

Establish `lq` using `leadMinor_pos_of_posDef hΓ' (le_refl q)`. Use `⟨⟨?_, ?_⟩, fun i => ?_, fun a b => ?_⟩` and prove the remaining obligations. Establish `e` using `dhigh p le_rfl`. Establish `hne : (gramHead (sigForm (p + q) p) (q + p) g).det ≠ 0`. Rewrite using `[← norm_ne_zero_iff, e]`.

Conclude with `(div_pos (leadMinor_pos_of_posDef hΓ le_rfl) lq).ne'`. Rewrite `hne` using `[det_head _ _ (Equiv.subtypeUnivEquiv fun a => by have := a.2; omega).symm]`. Establish `e2 : (gramOf (sigForm (p + q) p) g).det ≠ 0` using `hne`. Rewrite `e2` using `[gramOf, det_mul]`. Conclude with `(right_ne_zero_of_mul e2).isUnit`.

Rewrite using `[hNp]`. Establish `: -gramHead (sigForm (p + q) p) q g = B.submatrix (headEquiv hqN).symm (headEquiv hqN).symm`. Rewrite using `[← neg_neg B, ← FourierUniquenessMirabolic]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `hBp.submatrix (headEquiv hqN).symm.injective`. Establish `hi` using `i.2`. Rewrite using `[sum_Iic, sum_grLog hΓ hΓ' _ hi, stepPot, hNp]`. Establish `d0` using `dlow q le_rfl`. Rewrite `d0` using `[Nat.sub_self, leadMinor_size_zero]`.

Use `split_ifs with h1`. Rewrite using `[gramLog, gramLog, dhigh _ h1, d0, Real.log_div (leadMinor_pos_of_posDef hΓ h1).ne' lq.ne', Real.log_div one_ne_zero lq.ne', Real.log_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `d1` using `dhigh p le_rfl`. Rewrite `d1` using `[add_comm q p]`.

Rewrite using `[gramLog, gramLog, gramLog, d1, d0, dlow _ (by omega), Real.log_div (leadMinor_pos_of_posDef hΓ le_rfl).ne' lq.ne', Real.log_div one_ne_zero lq.ne', Real.log_one, Real.log_div (leadMinor_pos_of_posDef hΓ' (Nat.sub_le _ _)).ne' lq.ne', show q - (i + 1 - p) = p + q - (i + 1) by ome …`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hb : (b : ℕ) < q`. Establish `e1 : (M * g) a b = (M * g.submatrix id fl) a ⟨b, hb⟩` using `rfl`. Establish `e2 : M * (S * Pᴴ).submatrix id Fin.rev = (M * (S * Pᴴ)).submatrix id Fin.rev` using `rfl`.

Rewrite using `[e1, gl, e2, ← Matrix.mul_assoc, b1, if_neg (by omega)]`. Both sides reduce to the same expression. Establish `hb2` using `b.2`. Establish `e0 : b = fr ⟨b - q, by omega⟩` using `Fin.ext (by simp [fr]; omega)`. Establish `e1 : (M * g) a b = (M * g.submatrix id fr) a ⟨b - q, by omega⟩` using `by conv_lhs => rw [e0]`.

Both sides reduce to the same expression. Rewrite using `[e1, gr, hL, one_apply]`. Simplify using `only [Fin.ext_iff]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
theorem matStep : MatStep := by
  intro p q Γ Γ' M Q L hΓ hΓ' h hL
  set S : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := diagonal fun a => (sigForm (p + q) p a : ℂ) with hSd
  set P := Q.map (starRingEnd ℂ) with hP
  have hPQ : Qᵀ = Pᴴ := by
    ext a b
    simp [hP]
  have hC : Γ'ᵀ.PosDef := hΓ'.transpose
  set C := Γ'ᵀ with hCd
  have hCu : IsUnit C.det := (isUnit_iff_isUnit_det _).1 hC.isUnit
  have hS : S * S = 1 := by
    rw [hSd, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold sigForm
    split_ifs <;> simp
  have hSH : Sᴴ = S := by
    rw [hSd, diagonal_conjTranspose]
    congr 1
    funext a
    simp
  rw [hPQ] at h
  obtain ⟨b1, b2, b3⟩ := blocks hCu hS h
  have hqN : q ≤ p + q := by omega
  let fl : Fin q → Fin (p + q) := Fin.castLE hqN
  let fr : Fin p → Fin (p + q) := fun a => ⟨q + a, by omega⟩
  set g := perMat Q L with hg
  have gl : g.submatrix id fl = (S * Pᴴ).submatrix id Fin.rev := by
    ext a b
    have : (⟨q - 1 - b, by omega⟩ : Fin q) = b.rev := Fin.ext (by simp [Fin.val_rev]; omega)
    simp [hg, perMat, fl, hSd, ← hPQ, this]
  have gr : g.submatrix id fr = L := by
    ext a b
    simp [hg, perMat, fr]
  set B : Matrix (Fin q) (Fin q) ℂ := C⁻¹.submatrix Fin.rev Fin.rev with hB
  have hBp : B.PosDef := hC.inv.submatrix Fin.rev_injective
  set X : Matrix (Fin q) (Fin p) ℂ := (P * L).submatrix Fin.rev id with hX
  have FourierUniquenessMirabolic : (gramOf (sigForm (p + q) p) g).submatrix fl fl = -B := by
    rw [gram_sub, gl, ← hSd]
    show ((S * Pᴴ)ᴴ * S * (S * Pᴴ)).submatrix Fin.rev Fin.rev = _
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hSH,
      Matrix.mul_assoc P S S, hS, Matrix.mul_one, ← Matrix.mul_assoc, b2]
    rfl
  have WeakApproximationGL : (gramOf (sigForm (p + q) p) g).submatrix fl fr = X := by
    rw [gram_sub, gl, gr, ← hSd]
    show ((S * Pᴴ)ᴴ * S * L).submatrix Fin.rev id = _
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hSH, Matrix.mul_assoc P S S, hS, Matrix.mul_one]
  have G21 : (gramOf (sigForm (p + q) p) g).submatrix fr fl = Xᴴ := by
    rw [← WeakApproximationGL, gram_sub, gram_sub, ← hSd, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hSH,
      Matrix.mul_assoc]
  have hBi : B⁻¹ = C.submatrix Fin.rev Fin.rev := by
    refine inv_eq_right_inv ?_
    rw [hB, ← submatrix_mul _ _ _ _ _ Fin.rev_bijective, nonsing_inv_mul _ hCu]
    exact submatrix_one _ Fin.rev_injective
  have G22 : (gramOf (sigForm (p + q) p) g).submatrix fr fr = Γ - Xᴴ * B⁻¹ * X := by
    rw [gram_sub, gr, ← hSd, ← h, hBi, hX, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Fin.rev_bijective,
      ← submatrix_mul _ _ _ _ _ Fin.rev_bijective, submatrix_id_id, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · have : Lᴴ * (Mᴴ * Γ * M) * L = (M * L)ᴴ * Γ * (M * L) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [this, hL]
      simp
    · simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hBu : IsUnit B.det := (isUnit_iff_isUnit_det _).1 hBp.isUnit
  have lmq : ‖C.det‖ = leadMinor Γ' q := by
    rw [← leadMinor_transpose, ← norm_det_eq hC le_rfl]
    rfl
  have low : ∀ k (hk : k ≤ q), ‖(B.submatrix (Fin.castLE hk) (Fin.castLE hk)).det‖ =
      leadMinor Γ' (q - k) / leadMinor Γ' q := by
    intro k hk
    have e1 : q - k + k = q := by omega
    have j := congrArg norm (jac C hCu (finSumFinEquiv.trans (finCongr e1)))
    have e2 : (C⁻¹.submatrix (fun b => (finSumFinEquiv.trans (finCongr e1)) (.inr b))
        fun b => (finSumFinEquiv.trans (finCongr e1)) (.inr b)).submatrix Fin.revPerm Fin.revPerm =
        B.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      ext a b
      simp only [hB, submatrix_apply]
      have : ∀ a : Fin k, (finSumFinEquiv.trans (finCongr e1)) (Sum.inr (Fin.revPerm a)) = (Fin.castLE hk a).rev :=
        fun a => Fin.ext (by have := a.2; simp [Fin.val_rev]; omega)
      rw [this, this]
    have e3 : (C.submatrix (fun b => (finSumFinEquiv.trans (finCongr e1)) (.inl b))
        fun b => (finSumFinEquiv.trans (finCongr e1)) (.inl b)) =
        C.submatrix (Fin.castLE (Nat.sub_le q k)) (Fin.castLE (Nat.sub_le q k)) := by
      ext a b
      simp only [submatrix_apply]
      congr 1
    rw [norm_mul, lmq, e3, norm_det_eq hC, leadMinor_transpose, ← det_submatrix_equiv_self Fin.revPerm, e2] at j
    rw [← j, mul_div_cancel_left₀ _ (leadMinor_pos_of_posDef hΓ' le_rfl).ne']
  have dlow : ∀ k, k ≤ q → ‖(gramHead (sigForm (p + q) p) k g).det‖ = leadMinor Γ' (q - k) / leadMinor Γ' q := by
    intro k hk
    rw [det_head _ _ (headEquiv (hk.trans hqN)), ← low k hk]
    have : ((gramOf (sigForm (p + q) p) g).submatrix (fun a => (headEquiv (hk.trans hqN) a).1)
        fun a => (headEquiv (hk.trans hqN) a).1) = -B.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      show _ = (-B).submatrix (Fin.castLE hk) (Fin.castLE hk)
      rw [← FourierUniquenessMirabolic]
      rfl
    rw [this, det_neg, norm_mul]
    simp
  have dhigh : ∀ m, m ≤ p → ‖(gramHead (sigForm (p + q) p) (q + m) g).det‖ = leadMinor Γ m / leadMinor Γ' q := by
    intro m hm
    have hle : q + m ≤ p + q := by omega
    rw [det_head _ _ (finSumFinEquiv.trans (headEquiv hle))]
    have : ((gramOf (sigForm (p + q) p) g).submatrix (fun a => ((finSumFinEquiv.trans (headEquiv hle)) a).1)
        fun a => ((finSumFinEquiv.trans (headEquiv hle)) a).1) =
        fromBlocks (-B) (X.submatrix id (Fin.castLE hm)) (Xᴴ.submatrix (Fin.castLE hm) id)
          ((Γ - Xᴴ * B⁻¹ * X).submatrix (Fin.castLE hm) (Fin.castLE hm)) := by
      rw [← FourierUniquenessMirabolic, ← G22, ← G21, ← WeakApproximationGL]
      ext (a | a) (b | b) <;> rfl
    have hnB : IsUnit (-B).det := by
      rw [det_neg]
      exact (isUnit_neg_one.pow _).mul hBu
    let _i := invertibleOfIsUnitDet _ hnB
    have hi : ⅟(-B) = -B⁻¹ := by
      rw [invOf_eq_nonsing_inv]
      refine inv_eq_right_inv ?_
      rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, mul_nonsing_inv _ hBu]
    have e4 : (Γ - Xᴴ * B⁻¹ * X).submatrix (Fin.castLE hm) (Fin.castLE hm) -
        Xᴴ.submatrix (Fin.castLE hm) id * -B⁻¹ * X.submatrix id (Fin.castLE hm) =
        Γ.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
      ext a b
      simp [mul_apply]
    have e5 := low q le_rfl
    rw [Nat.sub_self, leadMinor_size_zero] at e5
    have e6 : ‖B.det‖ = 1 / leadMinor Γ' q := e5
    rw [this, det_fromBlocks₁₁, hi, e4, norm_mul, norm_det_eq hΓ, det_neg, norm_mul, e6]
    simp [div_eq_inv_mul]
  have hNp : p + q - p = q := by omega
  have lq := leadMinor_pos_of_posDef hΓ' (le_refl q)
  refine ⟨⟨?_, ?_⟩, fun i => ?_, fun a b => ?_⟩
  · have e := dhigh p le_rfl
    have hne : (gramHead (sigForm (p + q) p) (q + p) g).det ≠ 0 := by
      rw [← norm_ne_zero_iff, e]
      exact (div_pos (leadMinor_pos_of_posDef hΓ le_rfl) lq).ne'
    rw [det_head _ _ (Equiv.subtypeUnivEquiv fun a => by have := a.2; omega).symm] at hne
    have e2 : (gramOf (sigForm (p + q) p) g).det ≠ 0 := hne
    rw [gramOf, det_mul] at e2
    exact (right_ne_zero_of_mul e2).isUnit
  · rw [hNp]
    have : -gramHead (sigForm (p + q) p) q g = B.submatrix (headEquiv hqN).symm (headEquiv hqN).symm := by
      rw [← neg_neg B, ← FourierUniquenessMirabolic]
      rfl
    rw [this]
    exact hBp.submatrix (headEquiv hqN).symm.injective
  · have hi := i.2
    rw [sum_Iic, sum_grLog hΓ hΓ' _ hi, stepPot, hNp]
    have d0 := dlow q le_rfl
    rw [Nat.sub_self, leadMinor_size_zero] at d0
    split_ifs with h1
    · rw [gramLog, gramLog, dhigh _ h1, d0, Real.log_div (leadMinor_pos_of_posDef hΓ h1).ne' lq.ne',
        Real.log_div one_ne_zero lq.ne', Real.log_one]
      ring
    · have d1 := dhigh p le_rfl
      rw [add_comm q p] at d1
      rw [gramLog, gramLog, gramLog, d1, d0, dlow _ (by omega), Real.log_div (leadMinor_pos_of_posDef hΓ le_rfl).ne' lq.ne',
        Real.log_div one_ne_zero lq.ne', Real.log_one,
        Real.log_div (leadMinor_pos_of_posDef hΓ' (Nat.sub_le _ _)).ne' lq.ne',
        show q - (i + 1 - p) = p + q - (i + 1) by omega]
      ring
  · by_cases hb : (b : ℕ) < q
    · have e1 : (M * g) a b = (M * g.submatrix id fl) a ⟨b, hb⟩ := rfl
      have e2 : M * (S * Pᴴ).submatrix id Fin.rev = (M * (S * Pᴴ)).submatrix id Fin.rev := rfl
      rw [e1, gl, e2, ← Matrix.mul_assoc, b1, if_neg (by omega)]
      rfl
    · have hb2 := b.2
      have e0 : b = fr ⟨b - q, by omega⟩ := Fin.ext (by simp [fr]; omega)
      have e1 : (M * g) a b = (M * g.submatrix id fr) a ⟨b - q, by omega⟩ := by
        conv_lhs => rw [e0]
        rfl
      rw [e1, gr, hL, one_apply]
      simp only [Fin.ext_iff]
      congr 1
      apply propext
      omega

end RootFieldNumerics
