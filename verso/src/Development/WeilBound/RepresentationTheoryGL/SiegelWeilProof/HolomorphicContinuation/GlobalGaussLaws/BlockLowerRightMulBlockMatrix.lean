import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField

noncomputable section

open Matrix GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob.Gen2H

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Unfold `blk4`. Rewrite using `[Matrix.submatrix_submatrix]`. Simplify using the standard rewrite rules.
-/
theorem submatrix_fromBlocks_levi (P Q S T : Matrix (Fin n) (Fin n) R) :
    (blk4 P Q S T).submatrix finSumFinEquiv finSumFinEquiv = fromBlocks P Q S T := by
  unfold blk4
  rw [Matrix.submatrix_submatrix]
  simp

/- English proof (translation)
Unfold `blkDm`. Rewrite using `[← Matrix.submatrix_mul_equiv M (blk4 P Q S T) finSumFinEquiv finSumFinEquiv finSumFinEquiv, submatrix_fromBlocks_levi]`. Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]`. Rewrite using `[Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]`.
-/
theorem block_lower_right_mul_block_matrix (M : Matrix (Fin (n + n)) (Fin (n + n)) R) (P Q S T : Matrix (Fin n) (Fin n) R) :
    blkDm (M * blk4 P Q S T) =
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ * Q +
        (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ * T := by
  unfold blkDm
  rw [← Matrix.submatrix_mul_equiv M (blk4 P Q S T) finSumFinEquiv finSumFinEquiv finSumFinEquiv, submatrix_fromBlocks_levi]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]

/- English proof (translation)
Unfold `blk4`. Rewrite using `[Matrix.submatrix_mul_equiv (fromBlocks a b c d) (fromBlocks a' b' c' d') finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm, Matrix.fromBlocks_multiply]`.
-/
theorem block_matrix_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv (fromBlocks a b c d) (fromBlocks a' b' c' d') finSumFinEquiv.symm finSumFinEquiv.symm
    finSumFinEquiv.symm, Matrix.fromBlocks_multiply]

/- English proof (translation)
Establish `h2 : (1 : Matrix (Fin n) (Fin n) R) - eI I = diagonal (fun i => if i ∈ I then (0 : R) else 1)`. Rewrite using `[eI, ← diagonal_one, diagonal_sub]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp`. Rewrite using `[h2, eI, vecMul_add, Pi.add_apply, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_diagonal, vecMul_diagonal]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem vecMul_mix (C D : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)) (u : Fin n → R) (j : Fin n) :
    vecMul u (C * eI I + D * (1 - eI I)) j = if j ∈ I then vecMul u C j else vecMul u D j := by
  classical
  have h2 : (1 : Matrix (Fin n) (Fin n) R) - eI I = diagonal (fun i => if i ∈ I then (0 : R) else 1) := by
    rw [eI, ← diagonal_one, diagonal_sub]
    congr 1; funext i; split_ifs <;> simp
  rw [h2, eI, vecMul_add, Pi.add_apply, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_diagonal, vecMul_diagonal]
  split_ifs <;> simp

end Ring

section Field

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Simplify using `[Formalism.UG.cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]`.
-/
theorem cT_fromBlocks (σ : k →+* k) (A B C D : Matrix (Fin n) (Fin n) k) :
    Formalism.UG.cT σ (fromBlocks A B C D) =
      fromBlocks (Formalism.UG.cT σ A) (Formalism.UG.cT σ C) (Formalism.UG.cT σ B) (Formalism.UG.cT σ D) := by
  simp [Formalism.UG.cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem cT_submatrix (σ : k →+* k) (M : Matrix (Fin (n + n)) (Fin (n + n)) k) :
    (Formalism.UG.cT σ M).submatrix finSumFinEquiv finSumFinEquiv =
      Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) := by
  ext i j
  rfl

/- English proof (translation)
Introduce `Gs`. Establish `h0 : Formalism.UG.cT σ (g : Matrix (Fin (n + n)) (Fin (n + n)) k) * J2 k n * (g : Matrix (Fin (n + n)) (Fin (n + n)) k) = J2 k n` using `hg`. Use `set J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k := fromBlocks 0 1 (-1) 0 with hJ'`. Establish `hJs : (J2 k n).submatrix finSumFinEquiv finSumFinEquiv = J'` using `by rw [J2, submatrix_fromBlocks_levi]`. Establish `h1 : Formalism.UG.cT σ Gs * J' * Gs = J'`.

Use `congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h0` as an intermediate fact. Rewrite `this` using `[← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, cT_submatrix, hJs]`. Conclude with `this`. Establish `hJJ : J' * J' = -1`. Rewrite using `[hJ', Matrix.fromBlocks_multiply]`.

Simplify using `only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero]`. Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]`. Establish `h2 : (-J' * Formalism.UG.cT σ Gs * J') * Gs = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT σ Gs), h1, Matrix.neg_mul, hJJ, neg_neg]`. Establish `h3 : Gs * (-J' * Formalism.UG.cT σ Gs * J') = 1` using `mul_eq_one_comm.mp h2`.

Establish `h4 : Gs * J' * Formalism.UG.cT σ Gs = J'`. Combine the equalities or inequalities in the displayed calculation. Establish `h5` using `congrArg Matrix.toBlocks₂₂ h4`. Use `conv_lhs at h5 => rw [← Matrix.fromBlocks_toBlocks Gs, cT_fromBlocks, hJ']`. Rewrite `h5` using `[hJ', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₂]`.

Simplify using `only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h5`. Rewrite `h5` using `[neg_add_eq_zero]`. Conclude with `h5.symm`.
-/
theorem lower_rel (σ : k →+* k) (g : GL (Fin (n + n)) k) (hg : g ∈ Formalism.UG.UJ σ (J2 k n)) :
    let Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv
    Gs.toBlocks₂₁ * Formalism.UG.cT σ Gs.toBlocks₂₂ = Gs.toBlocks₂₂ * Formalism.UG.cT σ Gs.toBlocks₂₁ := by
  intro Gs
  have h0 : Formalism.UG.cT σ (g : Matrix (Fin (n + n)) (Fin (n + n)) k) * J2 k n * (g : Matrix (Fin (n + n)) (Fin (n + n)) k) =
      J2 k n := hg
  set J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k := fromBlocks 0 1 (-1) 0 with hJ'
  have hJs : (J2 k n).submatrix finSumFinEquiv finSumFinEquiv = J' := by rw [J2, submatrix_fromBlocks_levi]
  have h1 : Formalism.UG.cT σ Gs * J' * Gs = J' := by
    have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h0
    rw [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _,
      cT_submatrix, hJs] at this
    exact this
  have hJJ : J' * J' = -1 := by
    rw [hJ', Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  have h2 : (-J' * Formalism.UG.cT σ Gs * J') * Gs = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT σ Gs), h1, Matrix.neg_mul, hJJ, neg_neg]
  have h3 : Gs * (-J' * Formalism.UG.cT σ Gs * J') = 1 := mul_eq_one_comm.mp h2
  have h4 : Gs * J' * Formalism.UG.cT σ Gs = J' := by
    calc Gs * J' * Formalism.UG.cT σ Gs = Gs * J' * Formalism.UG.cT σ Gs * (J' * J') * (-1) := by rw [hJJ]; noncomm_ring
      _ = (Gs * (-J' * Formalism.UG.cT σ Gs * J')) * J' := by noncomm_ring
      _ = J' := by rw [h3, Matrix.one_mul]
  have h5 := congrArg Matrix.toBlocks₂₂ h4
  conv_lhs at h5 => rw [← Matrix.fromBlocks_toBlocks Gs, cT_fromBlocks, hJ']
  rw [hJ', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.toBlocks_fromBlocks₂₂] at h5
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h5
  rw [neg_add_eq_zero] at h5
  exact h5.symm

/- English proof (translation)
Use `set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs`. Set `w : Fin n ⊕ Fin n → k` to `Sum.elim 0 u`. Establish `hw : w ᵥ* Gs = 0`. Use function extensionality and compare the values at `x`. Break down `x with i | i` into its components or cases.

Use `congrFun hC i` as an intermediate fact. Simplify `this` using `[w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁]`. Use `congrFun hD i` as an intermediate fact. Simplify `this` using `[w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂]`. Establish `hdet : Gs.det ≠ 0`.

Rewrite using `[hGs, Matrix.det_submatrix_equiv_self]`. Conclude with `(Matrix.GeneralLinearGroup.det g).ne_zero`. Establish `hw0 : w = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨w, hne, hw⟩)`.

Use function extensionality and compare the values at `j`. Use `congrFun hw0 (Sum.inr j)` as an intermediate fact. Simplify `this` using `[w]`.
-/
theorem lower_inj (g : GL (Fin (n + n)) k) (u : Fin n → k)
    (hC : u ᵥ* ((g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (hD : u ᵥ* ((g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = 0) :
    u = 0 := by
  classical
  set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs
  let w : Fin n ⊕ Fin n → k := Sum.elim 0 u
  have hw : w ᵥ* Gs = 0 := by
    funext x
    rcases x with i | i
    · have := congrFun hC i
      simpa [w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using this
    · have := congrFun hD i
      simpa [w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂] using this
  have hdet : Gs.det ≠ 0 := by
    rw [hGs, Matrix.det_submatrix_equiv_self]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hw0 : w = 0 := by
    by_contra hne
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨w, hne, hw⟩)
  funext j
  have := congrFun hw0 (Sum.inr j)
  simpa [w] using this

/- English proof (translation)
Simplify using `[vecMul, mulVec, dotProduct, Formalism.UG.cT, map_sum, map_mul, mul_comm]`.
-/
theorem conj_vecMul (σ : k →+* k) (u' : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) (i : Fin n) :
    σ ((u' ᵥ* Y) i) = (Formalism.UG.cT σ Y *ᵥ (fun l => σ (u' l))) i := by
  simp [vecMul, mulVec, dotProduct, Formalism.UG.cT, map_sum, map_mul, mul_comm]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]`. Simplify using `only [dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[conj_vecMul]`.
-/
theorem iso_eq (σ : k →+* k) (u u' : Fin n → k) (X Y : Matrix (Fin n) (Fin n) k) :
    ∑ i, (u ᵥ* X) i * σ ((u' ᵥ* Y) i) = u ⬝ᵥ ((X * Formalism.UG.cT σ Y) *ᵥ (fun l => σ (u' l))) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conj_vecMul]

end Field

end PositivityTheory.Rg.Sw.Glob.Gen2H

namespace PositivityTheory.Rg.Sw.Glob

open Gen2H

/- English proof (translation)
Introduce `k _ σ hσ n g hg`. Use `set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs`. Use `set C := Gs.toBlocks₂₁ with hC`. Use `set D := Gs.toBlocks₂₂ with hD`. Establish `hrel : C * Formalism.UG.cT σ D = D * Formalism.UG.cT σ C` using `lower_rel σ g hg`.

Establish `hiso : ∀ u u' : Fin n → k, ∑ i, (u ᵥ* C) i * σ ((u' ᵥ* D) i) = ∑ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i)`. Introduce `u u'`. Rewrite using `[iso_eq, iso_eq, hrel]`. Set `Surj : Finset (Fin n) → Prop` to `fun I => ∀ t : Fin n → k, ∃ u : Fin n → k, u ᵥ* D = 0 ∧ ∀ i ∈ I, (u ᵥ* C) i = t i`. Establish `h0 : Surj ∅` using `fun t => ⟨0, by simp, by simp⟩`.

Take `⟨I, hI, hmax⟩` from `Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter Surj) Finset.card ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩`. Establish `hSI : Surj I` using `(Finset.mem_filter.1 hI).2`. Establish `hInj : ∀ u : Fin n → k, u ᵥ* D = 0 → (∀ i ∈ I, (u ᵥ* C) i = 0) → u ᵥ* C = 0`. Introduce `u hu hI0`. Assume the negation of the conclusion as `hne`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, (u ᵥ* C) j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (funext h)`. Establish `hjI : j ∉ I` using `fun h => hj (hI0 j h)`.

Establish `hS : Surj (insert j I)`. Introduce `t`. Take `⟨u', hu', ht⟩` from `hSI t`. Use `⟨u' + ((t j - (u' ᵥ* C) j) / (u ᵥ* C) j) • u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_vecMul, smul_vecMul, hu', hu, smul_zero, add_zero]`.

Introduce `i hi`. Rewrite using `[add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[ht i hi, hI0 i hi, mul_zero, add_zero]`. Use `hmax (insert j I) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩)` as an intermediate fact. Rewrite `this` using `[Finset.card_insert_of_notMem hjI]`. Use linear arithmetic over natural numbers and integers. Use `⟨I, ?_⟩` and prove the remaining obligations.

Rewrite using `[wIm, block_lower_right_mul_block_matrix, ← hGs, ← hC, ← hD, isUnit_iff_ne_zero]`. Introduce `hdet`. Take `⟨u, hu0, hu⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hdet`. Establish `hmix : ∀ j, (j ∈ I → (u ᵥ* C) j = 0) ∧ (j ∉ I → (u ᵥ* D) j = 0)`. Introduce `j`.

Use `congrFun hu j` as an intermediate fact. Rewrite `this` using `[vecMul_mix]`. Distinguish the cases in `h : j ∈ I`. Rewrite `this` using `[if_pos h]`. Conclude with `⟨fun _ => this, fun h' => absurd h h'⟩`.

Rewrite `this` using `[if_neg h]`. Conclude with `⟨fun h' => absurd h' h, fun _ => this⟩`. Establish `hD0 : u ᵥ* D = 0`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j ∈ I`.

Take `⟨u', hu', ht⟩` from `hSI (fun i => if i = j then 1 else 0)`. Establish `h` using `hiso u u'`. Rewrite `h` using `[hu']`. Simplify using `only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero] at h`. Establish `hterm : ∀ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i) = if i = j then (u ᵥ* D) j else 0`.

Introduce `i`. Distinguish the cases in `hi : i ∈ I`. Rewrite using `[ht i hi]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hij]`. Establish `hne : i ≠ j` using `fun e => hi (e ▸ hj)`. Rewrite using `[(hmix i).2 hi]`. Simplify using `[hne]`.

Rewrite `h` using `[Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq']`. Simplify using `using h.symm`. Conclude with `(hmix j).2 hj`. Establish `hC0 : u ᵥ* C = 0` using `hInj u hD0 (fun i hi => (hmix i).1 hi)`. Conclude with `hu0 (lower_inj g u hC0 hD0)`.
-/
theorem locRedField : LocRedField := by
  intro k _ σ hσ n g hg
  classical
  set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs
  set C := Gs.toBlocks₂₁ with hC
  set D := Gs.toBlocks₂₂ with hD
  have hrel : C * Formalism.UG.cT σ D = D * Formalism.UG.cT σ C := lower_rel σ g hg
  have hiso : ∀ u u' : Fin n → k,
      ∑ i, (u ᵥ* C) i * σ ((u' ᵥ* D) i) = ∑ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i) := by
    intro u u'
    rw [iso_eq, iso_eq, hrel]
  let Surj : Finset (Fin n) → Prop := fun I => ∀ t : Fin n → k, ∃ u : Fin n → k, u ᵥ* D = 0 ∧ ∀ i ∈ I, (u ᵥ* C) i = t i
  have h0 : Surj ∅ := fun t => ⟨0, by simp, by simp⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter Surj) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have hSI : Surj I := (Finset.mem_filter.1 hI).2
  have hInj : ∀ u : Fin n → k, u ᵥ* D = 0 → (∀ i ∈ I, (u ᵥ* C) i = 0) → u ᵥ* C = 0 := by
    intro u hu hI0
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, (u ᵥ* C) j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hjI : j ∉ I := fun h => hj (hI0 j h)
    have hS : Surj (insert j I) := by
      intro t
      obtain ⟨u', hu', ht⟩ := hSI t
      refine ⟨u' + ((t j - (u' ᵥ* C) j) / (u ᵥ* C) j) • u, ?_, ?_⟩
      · rw [add_vecMul, smul_vecMul, hu', hu, smul_zero, add_zero]
      · intro i hi
        rw [add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · field_simp
          ring
        · rw [ht i hi, hI0 i hi, mul_zero, add_zero]
    have := hmax (insert j I) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩)
    rw [Finset.card_insert_of_notMem hjI] at this
    omega
  refine ⟨I, ?_⟩
  rw [wIm, block_lower_right_mul_block_matrix, ← hGs, ← hC, ← hD, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hmix : ∀ j, (j ∈ I → (u ᵥ* C) j = 0) ∧ (j ∉ I → (u ᵥ* D) j = 0) := by
    intro j
    have := congrFun hu j
    rw [vecMul_mix] at this
    by_cases h : j ∈ I
    · rw [if_pos h] at this
      exact ⟨fun _ => this, fun h' => absurd h h'⟩
    · rw [if_neg h] at this
      exact ⟨fun h' => absurd h' h, fun _ => this⟩
  have hD0 : u ᵥ* D = 0 := by
    funext j
    by_cases hj : j ∈ I
    · obtain ⟨u', hu', ht⟩ := hSI (fun i => if i = j then 1 else 0)
      have h := hiso u u'
      rw [hu'] at h
      simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero] at h
      have hterm : ∀ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i) = if i = j then (u ᵥ* D) j else 0 := by
        intro i
        by_cases hi : i ∈ I
        · rw [ht i hi]
          by_cases hij : i = j
          · subst hij
            simp
          · simp [hij]
        · have hne : i ≠ j := fun e => hi (e ▸ hj)
          rw [(hmix i).2 hi]
          simp [hne]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq'] at h
      simpa using h.symm
    · exact (hmix j).2 hj
  have hC0 : u ᵥ* C = 0 := hInj u hD0 (fun i hi => (hmix i).1 hi)
  exact hu0 (lower_inj g u hC0 hD0)

end PositivityTheory.Rg.Sw.Glob
