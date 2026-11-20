import Mathlib
import Formalism.PeriodIntegrals.PairCorankPos

noncomputable section

open scoped Classical

namespace PI.PairCorankPos.W

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hT_swap (S : HSpace E) (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← S.herm.eq x y, starRingEnd_apply]

/- English proof (translation)
Proceed by induction. Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact.

Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem gram_fvec {S : HSpace E} {r : ℕ} {T : E} (F : FlagG S r T) (c i : Fin (r + 1)) :
    S.hT (F.fvec c) (F.fvec i) = if c = Fin.last r ∧ i = Fin.last r then -T else 0 := by
  induction c using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast j =>
      have h1 : Fin.castSucc j ≠ Fin.last r := Fin.castSucc_ne_last j
      simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, h1, and_false, if_false]
      rw [hT_swap, F.z_orth j, star_zero]
  | cast j =>
    have h1 : Fin.castSucc j ≠ Fin.last r := Fin.castSucc_ne_last j
    induction i using Fin.lastCases with
    | last =>
      simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, h1, false_and, if_false]
      exact F.z_orth j
    | cast l =>
      simp only [FlagG.fvec, Fin.snoc_castSucc, h1, false_and, if_false]
      exact F.e_iso j l

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem det_mul_last {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E) (c : E)
    (h : ∀ i, (A *ᵥ v) i = if i = Fin.last r then c else 0) :
    A.det * v (Fin.last r) = (A.submatrix Fin.castSucc Fin.castSucc).det * c := by
  have key : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]
  have k2 := congrFun key (Fin.last r)
  have hv : A *ᵥ v = fun i => if i = Fin.last r then c else 0 := funext h
  rw [hv] at k2
  simp only [Matrix.mulVec, dotProduct, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Pi.smul_apply, smul_eq_mul] at k2
  rw [← k2, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last,
    Even.neg_one_pow ⟨r, rfl⟩, one_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem eq_zero_of_mulVec {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n E) (v : n → E)
    (hA : A.det ≠ 0) (h : A *ᵥ v = 0) : v = 0 := by
  have key : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]
  rw [h, Matrix.mulVec_zero] at key
  exact (smul_eq_zero.1 key.symm).resolve_left hA

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem Dl_top {S : HSpace E} {r : ℕ} {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    Dl F F' (r + 1) = (Zhat F F').det := by
  simp only [Dl, leadMinorE, le_refl, dif_pos]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem Dl_r {S : HSpace E} {r : ℕ} {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    Dl F F' r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det := by
  simp only [Dl, leadMinorE, dif_pos (Nat.le_succ r)]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Take a linear combination of the given relations to obtain the conclusion. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem linIndep {S : HSpace E} {r : ℕ} {T T' : E} (F : FlagG S r T) (F' : FlagG S r T')
    (hG : Gflag F F' ≠ 0) : LinearIndependent E (Sum.elim F.fvec F'.fvec) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set a : Fin (r + 1) → E := fun i => g (Sum.inl i) with ha_def
  set b : Fin (r + 1) → E := fun i => g (Sum.inr i) with hb_def
  have hsum : ∑ i, a i • F.fvec i + ∑ j, b j • F'.fvec j = 0 := by
    rw [Fintype.sum_sum_type] at hg
    simpa using hg
  set Z := Zhat F F' with hZ

  have hZb : ∀ c, (Z *ᵥ b) c = if c = Fin.last r then T * a (Fin.last r) else 0 := by
    intro c
    have h0 := congrArg (S.hT (F.fvec c)) hsum
    simp only [map_add, map_sum, LinearMap.map_smulₛₗ, RingHom.id_apply, map_zero,
      smul_eq_mul, gram_fvec] at h0
    have e1 : ∑ i, a i * (if c = Fin.last r ∧ i = Fin.last r then -T else 0) =
        if c = Fin.last r then -T * a (Fin.last r) else 0 := by
      by_cases hc : c = Fin.last r
      · simp [hc, mul_comm]
      · simp [hc]
    have e2 : ∑ j, b j * S.hT (F.fvec c) (F'.fvec j) = (Z *ᵥ b) c := by
      simp only [Matrix.mulVec, dotProduct, hZ, Zhat, brS]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e1, e2] at h0
    by_cases hc : c = Fin.last r
    · simp only [hc, if_true] at h0 ⊢
      linear_combination h0
    · simp only [hc, if_false] at h0 ⊢
      linear_combination h0

  have hZa : ∀ d, (Z.conjTranspose *ᵥ a) d = if d = Fin.last r then T' * b (Fin.last r) else 0 := by
    intro d
    have h0 := congrArg (S.hT (F'.fvec d)) hsum
    simp only [map_add, map_sum, LinearMap.map_smulₛₗ, RingHom.id_apply, map_zero,
      smul_eq_mul, gram_fvec] at h0
    have e1 : ∑ j, b j * (if d = Fin.last r ∧ j = Fin.last r then -T' else 0) =
        if d = Fin.last r then -T' * b (Fin.last r) else 0 := by
      by_cases hd : d = Fin.last r
      · simp [hd, mul_comm]
      · simp [hd]
    have e2 : ∑ i, a i * S.hT (F'.fvec d) (F.fvec i) = (Z.conjTranspose *ᵥ a) d := by
      simp only [Matrix.mulVec, dotProduct, hZ, Zhat, brS, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT_swap S (F.fvec i) (F'.fvec d), mul_comm]
    rw [e1, e2] at h0
    by_cases hd : d = Fin.last r
    · simp only [hd, if_true] at h0 ⊢
      linear_combination h0
    · simp only [hd, if_false] at h0 ⊢
      linear_combination h0
  set D := Z.det with hD
  set Dr := (Z.submatrix Fin.castSucc Fin.castSucc).det with hDr
  have hGe : Gflag F F' = D * star D - T * T' * (Dr * star Dr) := by
    simp only [Gflag, Dl_top, Dl_r, hD, hDr, hZ]
  rw [hGe] at hG
  have c1 : D * b (Fin.last r) = Dr * (T * a (Fin.last r)) := det_mul_last Z b _ hZb
  have c2 : star D * a (Fin.last r) = star Dr * (T' * b (Fin.last r)) := by
    have := det_mul_last Z.conjTranspose a _ hZa
    rwa [Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix,
      Matrix.det_conjTranspose] at this

  have hlast : a (Fin.last r) = 0 ∧ b (Fin.last r) = 0 := by
    by_contra hne
    apply hG
    by_cases ha : a (Fin.last r) = 0
    · have hb : b (Fin.last r) ≠ 0 := fun hb => hne ⟨ha, hb⟩
      rw [ha, mul_zero, mul_zero] at c1
      rw [ha, mul_zero] at c2
      have hD0 : D = 0 := (mul_eq_zero.1 c1).resolve_right hb
      have h3 : star Dr * T' = 0 := by
        have : star Dr * T' * b (Fin.last r) = 0 := by linear_combination -c2
        exact (mul_eq_zero.1 this).resolve_right hb
      linear_combination (star D) * hD0 - (T * Dr) * h3
    · by_cases hb : b (Fin.last r) = 0
      · rw [hb, mul_zero] at c1
        rw [hb, mul_zero, mul_zero] at c2
        have hsD : star D = 0 := (mul_eq_zero.1 c2).resolve_right ha
        have h3 : Dr * T = 0 := by
          have : Dr * T * a (Fin.last r) = 0 := by linear_combination -c1
          exact (mul_eq_zero.1 this).resolve_right ha
        linear_combination D * hsD - (T' * star Dr) * h3
      · have : a (Fin.last r) * b (Fin.last r) * (D * star D - T * T' * (Dr * star Dr)) = 0 := by
          linear_combination (star D * a (Fin.last r)) * c1 + (Dr * T * a (Fin.last r)) * c2
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (mul_ne_zero ha hb)
        · exact h

  have hZb0 : Z *ᵥ b = 0 := by
    funext c; rw [hZb c, hlast.1, mul_zero]; simp
  have hb0 : b = 0 := by
    by_cases hD0 : D = 0
    · have hDr0 : Dr ≠ 0 := by
        intro h; apply hG; rw [hD0, h]; ring
      have hsub : (Z.submatrix Fin.castSucc Fin.castSucc) *ᵥ (fun i => b (Fin.castSucc i)) = 0 := by
        funext i
        have := congrFun hZb0 (Fin.castSucc i)
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hlast.2, mul_zero, add_zero,
          Pi.zero_apply] at this
        simpa [Matrix.mulVec, dotProduct] using this
      have h' := eq_zero_of_mulVec _ _ hDr0 hsub
      funext i
      induction i using Fin.lastCases with
      | last => exact hlast.2
      | cast j => exact congrFun h' j
    · exact eq_zero_of_mulVec Z b hD0 hZb0

  have hsumA : ∑ i : Fin r, a (Fin.castSucc i) • F.e i = 0 := by
    have h1 := hsum
    rw [hb0] at h1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, Fin.sum_univ_castSucc,
      hlast.1, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last] at h1
    simpa using h1
  have hA : ∀ i : Fin r, a (Fin.castSucc i) = 0 :=
    Fintype.linearIndependent_iff.1 F.e_indep _ hsumA
  rintro (i | j)
  · show a i = 0
    induction i using Fin.lastCases with
    | last => exact hlast.1
    | cast j => exact hA j
  · show b j = 0
    rw [hb0]; rfl

end PI.PairCorankPos.W
