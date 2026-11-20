import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

section
variable {E : Type} [Field E]

/- English proof (translation)
Establish `h0` using `congrArg (coord τ') (atEmb_mul_of_ne h 1 z)`. Rewrite `h0` using `[map_mul, coord_atEmb, map_zero, one_mul]`. Then use the resulting hypothesis.
-/
lemma coord_atEmb_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  have h0 := congrArg (coord τ') (atEmb_mul_of_ne h 1 z)
  rwa [map_mul, coord_atEmb, map_zero, one_mul] at h0

/- English proof (translation)
Establish `: atEmb τ z = atEmb (ComplexEmbedding.conjugate τ) (starRingEnd ℂ z)`. Rewrite using `[atEmb_conj, Complex.conj_conj]`. Rewrite using `[this, coord_atEmb]`.
-/
lemma coord_conj_atEmb [IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    coord (ComplexEmbedding.conjugate τ) (atEmb τ z) = starRingEnd ℂ z := by
  have : atEmb τ z = atEmb (ComplexEmbedding.conjugate τ) (starRingEnd ℂ z) := by
    rw [atEmb_conj, Complex.conj_conj]
  rw [this, coord_atEmb]

/- English proof (translation)
Distinguish the cases in `hm : InfinitePlace.mk τ' = InfinitePlace.mk τ`. Break down `InfinitePlace.mk_eq_iff.mp hm with h | h` into its components or cases. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, coord_atEmb, coord_atEmb, Complex.I_mul_I]`. Evaluate the numerical expressions.

Establish `h' : τ' = ComplexEmbedding.conjugate τ`. Break down `InfinitePlace.mk_eq_iff.mp hm.symm with h2 | h2` into its components or cases. It suffices to derive a contradiction. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ'` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff, h, h2]`.

Conclude with `h2.symm`. Establish `hne : τ' ≠ τ`. Introduce `e`. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ'` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff, h, e]`.

Rewrite using `[if_neg hne, h', coord_conj_atEmb, coord_conj_atEmb, map_one, Complex.conj_I, mul_neg, Complex.I_mul_I]`. Evaluate the numerical expressions. Establish `hne : τ' ≠ τ` using `fun e => hm (by rw [e])`. Rewrite using `[if_neg hne, coord_atEmb_ne hm, coord_atEmb_ne hm]`. Simplify using the standard rewrite rules.
-/
lemma cxkey [IsTotallyComplex E] (τ τ' : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord τ' (atEmb τ 1) - Complex.I * coord τ' (atEmb τ Complex.I)) =
      if τ' = τ then 1 else 0 := by
  by_cases hm : InfinitePlace.mk τ' = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.mp hm with h | h
    · subst h
      rw [if_pos rfl, coord_atEmb, coord_atEmb, Complex.I_mul_I]
      norm_num
    · have h' : τ' = ComplexEmbedding.conjugate τ := by
        rcases InfinitePlace.mk_eq_iff.mp hm.symm with h2 | h2
        · exfalso
          apply IsTotallyComplex.complexEmbedding_not_isReal τ'
          rw [ComplexEmbedding.isReal_iff, h, h2]
        · exact h2.symm
      have hne : τ' ≠ τ := by
        intro e
        apply IsTotallyComplex.complexEmbedding_not_isReal τ'
        rw [ComplexEmbedding.isReal_iff, h, e]
      rw [if_neg hne, h', coord_conj_atEmb, coord_conj_atEmb, map_one, Complex.conj_I, mul_neg,
        Complex.I_mul_I]
      norm_num
  · have hne : τ' ≠ τ := fun e => hm (by rw [e])
    rw [if_neg hne, coord_atEmb_ne hm, coord_atEmb_ne hm]
    simp

end

/- English proof (translation)
Simplify using `only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma half_comb (ι : Type) [Fintype ι] (x x' : ι → ℂ) (y y' : ℂ) :
    (1 / 2 : ℂ) * ((∑ p, x p - y) - Complex.I * (∑ p, x' p - y')) =
      ∑ p, (1 / 2 : ℂ) * (x p - Complex.I * x' p) - (1 / 2 : ℂ) * (y - Complex.I * y') := by
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma half_ite (P : Prop) [Decidable P] (u v : ℂ) :
    (1 / 2 : ℂ) * ((if P then u else 0) - Complex.I * (if P then v else 0)) =
      if P then (1 / 2 : ℂ) * (u - Complex.I * v) else 0 := by
  split_ifs <;> simp

/- English proof (translation)
Introduce `E _ _ _ a Q _ _ lab s`. Use `⟨fun τ i j f => ?_, fun y p p' hp f => ?_⟩` and prove the remaining obligations. Establish `hD : ∀ (z : ℂ) (I J : Q → Fin a), bigD lab s (toL (Matrix.single i j (atEmb τ z))) I J = (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then coord (lab p) (atEmb τ z) else 0) - if I = J ∧ i = j then (s : ℂ) * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ z) else 0`. Introduce `z I J`. Simplify using `only [bigD, Matrix.of_apply, toL, Matrix.of_symm_apply, Matrix.single_apply]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[apply_ite (coord (lab p)), map_zero]`. Distinguish the cases in `h1 : ∀ r, r ≠ p → I r = J r`. Rewrite using `[if_pos h1]`.

Distinguish the cases in `h4 : i = I p ∧ j = J p`. Rewrite using `[if_pos h4, if_pos ⟨h1, h4.1.symm, h4.2.symm⟩]`. Rewrite using `[if_neg h4, if_neg (fun h => h4 ⟨h.2.1.symm, h.2.2.symm⟩)]`. Rewrite using `[if_neg h1, if_neg (fun h => h1 h.1)]`. Distinguish the cases in `h1 : I = J`.

Distinguish the cases in `h2 : i = j`. Substitute `h2` using the available equality. Rewrite using `[if_pos h1, if_pos ⟨h1, rfl⟩]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ' _ => ?_` and prove the remaining obligations.

Simplify using `only [and_self, apply_ite (coord τ'), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[if_pos h1, if_neg (fun h => h2 h.2)]`. Rewrite using `[Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => by`. Rewrite using `[if_neg (fun h => h2 (h.1.trans h.2.symm)), map_zero]]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h1, if_neg (fun h => h1 h.1)]`. Establish `hS : (1 / 2 : ℂ) * (∑ τ' : E →+* ℂ, coord τ' (atEmb τ 1) - Complex.I * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ Complex.I)) = 1`. Simplify using `only [Finset.mul_sum, ← Finset.sum_sub_distrib]`. Simplify using `only [cxkey, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `hE : ∀ I J : Q → Fin a, cx τ (bigD lab s) i j I J = (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then (if lab p = τ then (1 : ℂ) else 0) else 0) - if I = J ∧ i = j then (s : ℂ) else 0`.

Introduce `I J`. Simplify using `only [cx, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hD, half_comb, half_ite, cxkey]`. Use `congr 1`. Use `split_ifs`. Take the linear combination `(s : ℂ) * hS`.

Both sides reduce to the same expression. Establish `hT : ∀ I : Q → Fin a, tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j f I = ∑ p, if lab p = τ then (if I p = i then f (Function.update I p j) else 0) else 0`. Introduce `I`. Simplify using `[tE, lift, eAt, fib, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hl : lab p = τ <;> by_cases hi : I p = i <;> simp [hl, hi]`. Use function extensionality and compare the values at `I`. Simplify using `only [mulVec, dotProduct, hE, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Pi.sub_apply, hT]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : lab p = τ`. Distinguish the cases in `hi : I p = i`. Rewrite using `[Finset.sum_eq_single (Function.update I p j)]`. Establish `hc : (∀ r, r ≠ p → I r = Function.update I p j r) ∧ I p = i ∧ Function.update I p j p = j` using `⟨fun r hr => by rw [Function.update_of_ne hr], hi, by simp⟩`.

Rewrite using `[if_pos hc, if_pos hl, if_pos hl, if_pos hi, one_mul]`. Introduce `J _ hJ`. Rewrite using `[if_neg, zero_mul]`. Introduce `h`. Conclude with `hJ (Function.eq_update_iff.mpr ⟨h.2.2, fun r hr => (h.1 r hr).symm⟩)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [if_pos hl, if_neg hi]`. Use `Finset.sum_eq_zero fun J _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun h => hi h.2.1), zero_mul]`.

Simplify using `only [if_neg hl]`. Simplify using the standard rewrite rules. Distinguish the cases in `h : i = j`. Simplify using `[h]`. Simplify using `[h]`.

Establish `hlab : ∀ r, lab (Equiv.swap p p' r) = lab r`. Introduce `r`. Rewrite using `[Equiv.swap_apply_def]`. Use `split_ifs with h1 h2`. Rewrite using `[h1, hp]`.

Rewrite using `[h2, hp]`. Both sides reduce to the same expression. Establish `hM : ∀ I J : Q → Fin a, bigM lab s y (I ∘ Equiv.swap p p') (J ∘ Equiv.swap p p') = bigM lab s y I J`. Introduce `I J`. Simplify using `only [bigM, Matrix.of_apply, Function.comp_apply]`.

Use `congr 1`. Conclude with `Fintype.prod_equiv (Equiv.swap p p') _ _ (fun r => by rw [hlab])`. Set `e : (Q → Fin a) ≃ (Q → Fin a)` to `⟨fun J => J ∘ Equiv.swap p p', fun J => J ∘ Equiv.swap p p', fun J => by funext r; simp, fun J => by funext r; simp⟩`. Use function extensionality and compare the values at `I`. Simplify using `only [mulVec, dotProduct, pm, LinearMap.pi_apply, LinearMap.proj_apply]`.

Conclude with `Fintype.sum_equiv e _ _ (fun J => by simp only [e, Equiv.coe_fn_mk, hM])`.
-/
theorem bigCx_holds : BigCx := by
  intro E _ _ _ a Q _ _ lab s
  refine ⟨fun τ i j f => ?_, fun y p p' hp f => ?_⟩
  · have hD : ∀ (z : ℂ) (I J : Q → Fin a), bigD lab s (toL (Matrix.single i j (atEmb τ z))) I J =
        (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then coord (lab p) (atEmb τ z) else 0) -
          if I = J ∧ i = j then (s : ℂ) * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ z) else 0 := by
      intro z I J
      simp only [bigD, Matrix.of_apply, toL, Matrix.of_symm_apply, Matrix.single_apply]
      congr 1
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [apply_ite (coord (lab p)), map_zero]
        by_cases h1 : ∀ r, r ≠ p → I r = J r
        · rw [if_pos h1]
          by_cases h4 : i = I p ∧ j = J p
          · rw [if_pos h4, if_pos ⟨h1, h4.1.symm, h4.2.symm⟩]
          · rw [if_neg h4, if_neg (fun h => h4 ⟨h.2.1.symm, h.2.2.symm⟩)]
        · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      · by_cases h1 : I = J
        · by_cases h2 : i = j
          · subst h2
            rw [if_pos h1, if_pos ⟨h1, rfl⟩]
            congr 1
            refine Finset.sum_congr rfl fun τ' _ => ?_
            simp only [and_self, apply_ite (coord τ'), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          · rw [if_pos h1, if_neg (fun h => h2 h.2)]
            rw [Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => by
              rw [if_neg (fun h => h2 (h.1.trans h.2.symm)), map_zero]]
            simp
        · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    have hS : (1 / 2 : ℂ) * (∑ τ' : E →+* ℂ, coord τ' (atEmb τ 1) -
        Complex.I * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ Complex.I)) = 1 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [cxkey, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hE : ∀ I J : Q → Fin a, cx τ (bigD lab s) i j I J =
        (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then (if lab p = τ then (1 : ℂ) else 0) else 0) -
          if I = J ∧ i = j then (s : ℂ) else 0 := by
      intro I J
      simp only [cx, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hD, half_comb, half_ite, cxkey]
      congr 1
      split_ifs
      · linear_combination (s : ℂ) * hS
      · rfl
    have hT : ∀ I : Q → Fin a, tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j f I =
        ∑ p, if lab p = τ then (if I p = i then f (Function.update I p j) else 0) else 0 := by
      intro I
      simp [tE, lift, eAt, fib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hl : lab p = τ <;> by_cases hi : I p = i <;> simp [hl, hi]
    funext I
    simp only [mulVec, dotProduct, hE, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Pi.sub_apply, hT]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hl : lab p = τ
      · by_cases hi : I p = i
        · rw [Finset.sum_eq_single (Function.update I p j)]
          · have hc : (∀ r, r ≠ p → I r = Function.update I p j r) ∧ I p = i ∧ Function.update I p j p = j :=
              ⟨fun r hr => by rw [Function.update_of_ne hr], hi, by simp⟩
            rw [if_pos hc, if_pos hl, if_pos hl, if_pos hi, one_mul]
          · intro J _ hJ
            rw [if_neg, zero_mul]
            intro h
            exact hJ (Function.eq_update_iff.mpr ⟨h.2.2, fun r hr => (h.1 r hr).symm⟩)
          · intro h
            exact absurd (Finset.mem_univ _) h
        · simp only [if_pos hl, if_neg hi]
          refine Finset.sum_eq_zero fun J _ => ?_
          rw [if_neg (fun h => hi h.2.1), zero_mul]
      · simp only [if_neg hl]
        simp
    · by_cases h : i = j
      · simp [h]
      · simp [h]
  · have hlab : ∀ r, lab (Equiv.swap p p' r) = lab r := by
      intro r
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hp]
      · rw [h2, hp]
      · rfl
    have hM : ∀ I J : Q → Fin a,
        bigM lab s y (I ∘ Equiv.swap p p') (J ∘ Equiv.swap p p') = bigM lab s y I J := by
      intro I J
      simp only [bigM, Matrix.of_apply, Function.comp_apply]
      congr 1
      exact Fintype.prod_equiv (Equiv.swap p p') _ _ (fun r => by rw [hlab])
    let e : (Q → Fin a) ≃ (Q → Fin a) :=
      ⟨fun J => J ∘ Equiv.swap p p', fun J => J ∘ Equiv.swap p p',
        fun J => by funext r; simp, fun J => by funext r; simp⟩
    funext I
    simp only [mulVec, dotProduct, pm, LinearMap.pi_apply, LinearMap.proj_apply]
    exact Fintype.sum_equiv e _ _ (fun J => by simp only [e, Equiv.coe_fn_mk, hM])

end PositivityTheory.Rg.Cz.J
