import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAdapt

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

/- English proof (translation)
Introduce `n ε ι _ _ B hG`. Establish `hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1`. Simplify using `only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hJs : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε`. Simplify using `only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a <;> simp [h]`. Use `set J := Formalism.REAL.Jm ε with hJdef`. Use `set G := Bᴴ * J * B with hGdef`. Establish `hdet : IsUnit G.det` using `(Matrix.isUnit_iff_isUnit_det G).mp hG`.

Establish `hGi : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul G hdet`. Establish `hGh : Gᴴ = G`. Rewrite using `[hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJs, Matrix.mul_assoc]`. Establish `hGih : (G⁻¹)ᴴ = G⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hGh]`. Use `set Q := B * G⁻¹ * Bᴴ * J with hQdef`.

Establish `hQB : Q * B = B`. Combine the equalities or inequalities in the displayed calculation. Establish `hQQ : Q * Q = Q`. Combine the equalities or inequalities in the displayed calculation. Establish `hQJ : Qᴴ * J = J * Q`.

Simplify using `only [hQdef, Matrix.conjTranspose_mul, hJs, hGih, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Use `set P := 1 - Q with hPdef`. Establish `hPP : P * P = P`. Simplify using `only [hPdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]`. Normalize the expressions using the abelian group laws.

Establish `hPJ : Pᴴ * J = J * P`. Rewrite using `[hPdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hQJ, Matrix.one_mul, Matrix.mul_one]`. Establish `hQP : Q * P = 0` using `by rw [hPdef, Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]`. Establish `hPQ : P * Q = 0` using `by rw [hPdef, Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]`. Take `⟨W1, l1, hW1J, hQW1, hsp1, hcard1, -⟩` from `inst_qfamily ε Q hQQ hQJ`.

Take `⟨W2, l2, hW2J, hPW2, -, hcard2, -⟩` from `inst_qfamily ε P hPP hPJ`. Establish `hcross : W1ᴴ * J * W2 = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQJ]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc Q P, hQP]`. Simplify using the standard rewrite rules. Establish `hcross' : W2ᴴ * J * W1 = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hPJ]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc P Q, hPQ]`. Simplify using the standard rewrite rules. Establish `hrk : Q.rank + P.rank = n`. Apply `le_antisymm` to reduce the goal to its premises.

Establish `h1 : LinearMap.range P.mulVecLin ≤ LinearMap.ker Q.mulVecLin`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQP, Matrix.zero_mulVec]`. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker Q.mulVecLin`. Establish `h3` using `Submodule.finrank_mono h1`.

Establish `h4 : Module.finrank ℂ (Fin n → ℂ) = n` using `by first`. Consider the case `exact Module.finrank_fin_fun ℂ`. Consider the case `simp`. Unfold `Matrix.rank`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `inst_rank_add_le Q P`. Establish `hsum : Q + P = 1` using `by rw [hPdef]; abel`. Rewrite `h` using `[hsum, Matrix.rank_one, Fintype.card_fin]`. Conclude with `h`. Establish `hcardsum : Fintype.card ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0}) = n`.

Use `Eq.trans ?_ hrk` and prove the remaining obligations. Rewrite using `[Fintype.card_sum]`. Use `congrArg₂ (· + ·) hcard1 hcard2 using 2` and compare the differences between its conclusion and the goal. Take `⟨e⟩ : Nonempty (Fin n ≃ ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0}))` from `⟨(Fintype.equivFinOfCardEq hcardsum).symm⟩`. Take `⟨A, hAe⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, ∀ r k, A r k = Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k)` from `⟨Matrix.of fun r k => Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k), fun _ _ => rfl⟩`.

Take `⟨ε', hε'⟩ : ∃ ε' : Fin n → Bool, ∀ k, ε' k = Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j)) (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k)` from `⟨fun k => Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j)) (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k), fun _ => rfl⟩`. Establish `hcol : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n), M *ᵥ Pi.single k 1 = fun r => M r k`. Introduce `M k`. Use function extensionality and compare the values at `r`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Use `⟨A, ε', Finset.univ.filter (fun k => (e k).isLeft = true), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `k k'`. Rewrite using `[inst_gram_entry]`. Simplify using `only [Formalism.REAL.Jm, Matrix.diagonal_apply, hAe, hε']`. Apply the tactic sequence `rcases hk : e k with j | j <;> rcases hk' : e k' with j' | j' <;>`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Apply the tactic sequence `rw [← inst_gram_entry W1 J W1 (j : Fin n) j', hW1J, Matrix.diagonal_apply]`. Establish `hkk : k = k' ↔ (j : Fin n) = j'`. Rewrite using `[← e.apply_eq_iff_eq, hk, hk', Sum.inl.injEq, Subtype.ext_iff]`. Distinguish the cases in `h : (j : Fin n) = j'`.

Rewrite using `[if_pos h, if_pos (hkk.mpr h), if_neg j.2]`. Apply the tactic sequence `by_cases hp : 0 < l1 j <;> simp [hp]`. Rewrite using `[if_neg h, if_neg (fun h' => h (hkk.mp h'))]`. Apply the tactic sequence `rw [← inst_gram_entry W1 J W2 (j : Fin n) j', hcross, Matrix.zero_apply, if_neg]`. Introduce `h`.

Substitute `h` using the available equality. Rewrite `hk'` using `[hk]`. Conclude with `Sum.inl_ne_inr hk'`. Apply the tactic sequence `rw [← inst_gram_entry W2 J W1 (j : Fin n) j', hcross', Matrix.zero_apply, if_neg]`. Introduce `h`.

Substitute `h` using the available equality. Rewrite `hk'` using `[hk]`. Conclude with `Sum.inr_ne_inl hk'`. Apply the tactic sequence `rw [← inst_gram_entry W2 J W2 (j : Fin n) j', hW2J, Matrix.diagonal_apply]`. Establish `hkk : k = k' ↔ (j : Fin n) = j'`.

Rewrite using `[← e.apply_eq_iff_eq, hk, hk', Sum.inr.injEq, Subtype.ext_iff]`. Distinguish the cases in `h : (j : Fin n) = j'`. Rewrite using `[if_pos h, if_pos (hkk.mpr h), if_neg j.2]`. Apply the tactic sequence `by_cases hp : 0 < l2 j <;> simp [hp]`. Rewrite using `[if_neg h, if_neg (fun h' => h (hkk.mp h'))]`.

Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi`. Break down `hk : e i with j | j` into its components or cases. Use `⟨G⁻¹ *ᵥ (Bᴴ *ᵥ (J *ᵥ (W1 *ᵥ Pi.single (j : Fin n) 1))), ?_⟩` and prove the remaining obligations. Establish `h1 : A *ᵥ Pi.single i 1 = W1 *ᵥ Pi.single (j : Fin n) 1`.

Rewrite using `[hcol, hcol]`. Use function extensionality and compare the values at `r`. Use `show A r i = W1 r (j : Fin n)`. Rewrite using `[hAe, hk, Sum.elim_inl]`. Rewrite using `[h1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hi` using `[hk]`. Simplify using `at hi`. Introduce `j`. Establish `hb : Q *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1` using `by rw [Matrix.mulVec_mulVec, hQB]`.

Take `⟨y, hy0, hy⟩` from `hsp1 _ hb`. Use `⟨fun k => Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) (e k), ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk`. Break down `he : e k with j' | j'` into its components or cases.

Rewrite `hk` using `[he]`. Simplify using `at hk`. Simplify using `only [he, Sum.elim_inr]`. Rewrite using `[hy]`. Use function extensionality and compare the values at `r`.

Simplify using `only [Matrix.mulVec, dotProduct, hAe]`. Use `symm`. Rewrite using `[Fintype.sum_equiv e _ (fun x => Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) x * Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) x) (fun k => rfl)]`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]`.

Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun i => l1 i ≠ 0) (fun i => W1 r i * y i)]`. Establish `h0 : ∑ i : {i // ¬ l1 i ≠ 0}, W1 r i * y i = 0` using `Finset.sum_eq_zero fun i _ => by rw [hy0 i (not_not.mp i.2), mul_zero]`. Rewrite using `[h0, add_zero]`.
-/
theorem adapted_basis_instance : InstAdaptBasis := by
  intro n ε ι _ _ B hG
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJs : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  set J := Formalism.REAL.Jm ε with hJdef
  set G := Bᴴ * J * B with hGdef
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hGi : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hGh : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJs, Matrix.mul_assoc]
  have hGih : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  set Q := B * G⁻¹ * Bᴴ * J with hQdef
  have hQB : Q * B = B := by
    calc Q * B = B * (G⁻¹ * (Bᴴ * J * B)) := by simp only [hQdef, Matrix.mul_assoc]
      _ = B := by rw [← hGdef, hGi, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    calc Q * Q = (Q * B) * (G⁻¹ * Bᴴ * J) := by simp only [hQdef, Matrix.mul_assoc]
      _ = Q := by rw [hQB]; simp only [hQdef, Matrix.mul_assoc]
  have hQJ : Qᴴ * J = J * Q := by
    simp only [hQdef, Matrix.conjTranspose_mul, hJs, hGih, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  set P := 1 - Q with hPdef
  have hPP : P * P = P := by
    simp only [hPdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  have hPJ : Pᴴ * J = J * P := by
    rw [hPdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hQJ,
      Matrix.one_mul, Matrix.mul_one]
  have hQP : Q * P = 0 := by rw [hPdef, Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
  have hPQ : P * Q = 0 := by rw [hPdef, Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]
  obtain ⟨W1, l1, hW1J, hQW1, hsp1, hcard1, -⟩ := inst_qfamily ε Q hQQ hQJ
  obtain ⟨W2, l2, hW2J, hPW2, -, hcard2, -⟩ := inst_qfamily ε P hPP hPJ
  have hcross : W1ᴴ * J * W2 = 0 := by
    calc W1ᴴ * J * W2 = (Q * W1)ᴴ * J * (P * W2) := by rw [hQW1, hPW2]
      _ = W1ᴴ * (Qᴴ * J) * P * W2 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hQJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q P, hQP]
        simp
  have hcross' : W2ᴴ * J * W1 = 0 := by
    calc W2ᴴ * J * W1 = (P * W2)ᴴ * J * (Q * W1) := by rw [hQW1, hPW2]
      _ = W2ᴴ * (Pᴴ * J) * Q * W1 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hPJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P Q, hPQ]
        simp
  have hrk : Q.rank + P.rank = n := by
    apply le_antisymm
    · have h1 : LinearMap.range P.mulVecLin ≤ LinearMap.ker Q.mulVecLin := by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          hQP, Matrix.zero_mulVec]
      have h2 := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
      have h3 := Submodule.finrank_mono h1
      have h4 : Module.finrank ℂ (Fin n → ℂ) = n := by
        first
          | exact Module.finrank_fin_fun ℂ
          | simp
      unfold Matrix.rank
      omega
    · have h := inst_rank_add_le Q P
      have hsum : Q + P = 1 := by rw [hPdef]; abel
      rw [hsum, Matrix.rank_one, Fintype.card_fin] at h
      exact h
  have hcardsum : Fintype.card ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0}) = n := by
    refine Eq.trans ?_ hrk
    rw [Fintype.card_sum]
    convert congrArg₂ (· + ·) hcard1 hcard2 using 2
  obtain ⟨e⟩ : Nonempty (Fin n ≃ ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0})) :=
    ⟨(Fintype.equivFinOfCardEq hcardsum).symm⟩
  obtain ⟨A, hAe⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, ∀ r k, A r k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k) :=
    ⟨Matrix.of fun r k =>
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k),
      fun _ _ => rfl⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : Fin n → Bool, ∀ k, ε' k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k) :=
    ⟨fun k => Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k), fun _ => rfl⟩
  have hcol : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n), M *ᵥ Pi.single k 1 = fun r => M r k := by
    intro M k
    funext r
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨A, ε', Finset.univ.filter (fun k => (e k).isLeft = true), ?_, ?_, ?_⟩
  · ext k k'
    rw [inst_gram_entry]
    simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, hAe, hε']
    rcases hk : e k with j | j <;> rcases hk' : e k' with j' | j' <;>
      simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [← inst_gram_entry W1 J W1 (j : Fin n) j', hW1J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inl.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l1 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
    · rw [← inst_gram_entry W1 J W2 (j : Fin n) j', hcross, Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inl_ne_inr hk'
    · rw [← inst_gram_entry W2 J W1 (j : Fin n) j', hcross', Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inr_ne_inl hk'
    · rw [← inst_gram_entry W2 J W2 (j : Fin n) j', hW2J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inr.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l2 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hk : e i with j | j
    · refine ⟨G⁻¹ *ᵥ (Bᴴ *ᵥ (J *ᵥ (W1 *ᵥ Pi.single (j : Fin n) 1))), ?_⟩
      have h1 : A *ᵥ Pi.single i 1 = W1 *ᵥ Pi.single (j : Fin n) 1 := by
        rw [hcol, hcol]
        funext r
        show A r i = W1 r (j : Fin n)
        rw [hAe, hk, Sum.elim_inl]
      rw [h1]
      calc W1 *ᵥ Pi.single (j : Fin n) 1 = (Q * W1) *ᵥ Pi.single (j : Fin n) 1 := by rw [hQW1]
        _ = _ := by simp only [hQdef, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rw [hk] at hi
      simp at hi
  · intro j
    have hb : Q *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by rw [Matrix.mulVec_mulVec, hQB]
    obtain ⟨y, hy0, hy⟩ := hsp1 _ hb
    refine ⟨fun k => Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) (e k), ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases he : e k with j' | j'
      · rw [he] at hk
        simp at hk
      · simp only [he, Sum.elim_inr]
    · rw [hy]
      funext r
      simp only [Matrix.mulVec, dotProduct, hAe]
      symm
      rw [Fintype.sum_equiv e _ (fun x => Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j)
        (fun j : {i // l2 i ≠ 0} => W2 r j) x *
          Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) x) (fun k => rfl)]
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => l1 i ≠ 0) (fun i => W1 r i * y i)]
      have h0 : ∑ i : {i // ¬ l1 i ≠ 0}, W1 r i * y i = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hy0 i (not_not.mp i.2), mul_zero]
      rw [h0, add_zero]

end PI.ScMuExists.UnitaryGroupMassFormula
