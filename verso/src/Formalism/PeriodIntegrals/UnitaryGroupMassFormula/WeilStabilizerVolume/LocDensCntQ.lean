import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFF

noncomputable section

namespace PI.VolStabW

open Polynomial

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

It suffices to derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Equip the data with the indicated structure. Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  classical
  by_cases hsq : ∃ c : k, c * c = D
  · obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by rintro rfl; exact hD (by rw [← hc, mul_zero])
    let σ' : (k × k) ≃ₐ[k] (k × k) :=
      { RingEquiv.prodComm with commutes' := fun r => rfl }
    have hσ : ∀ x : k × k, σ' x = x.swap := fun x => rfl
    refine ⟨k × k, inferInstance, inferInstance, σ', (c, -c), ⟨fun x => by simp [hσ], Or.inr
      ⟨AlgEquiv.refl, fun x => by simp [hσ]⟩⟩, ?_, ?_, ?_⟩
    · ext <;> simp [hc]
    · ext <;> simp [hσ]
    · have h2c : (2 : k) * c ≠ 0 := mul_ne_zero h2 hc0
      constructor
      · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
        obtain ⟨h1, h2'⟩ := h
        have hy : y1 = y2 := by
          have : (2 * c) * (y1 - y2) = 0 := by linear_combination h1 - h2'
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2c)
        subst hy
        have hx : x1 = x2 := by linear_combination h1
        rw [hx]
      · rintro ⟨u, w⟩
        refine ⟨((u + w) / 2, (u - w) / (2 * c)), ?_⟩
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        constructor
        · field_simp
          ring
        · field_simp
          ring
  · push Not at hsq
    let f : k[X] := X ^ 2 - C D
    have hfdeg : f.natDegree = 2 := natDegree_X_pow_sub_C
    have hnr : ∀ x, ¬ IsRoot f x := by
      intro x hx
      apply hsq x
      have : x ^ 2 - D = 0 := by simpa [f] using hx
      linear_combination this
    have hirr : Irreducible f :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [hfdeg]; decide) hnr
    have : Fact (Irreducible f) := ⟨hirr⟩
    have hf0 : f ≠ 0 := hirr.ne_zero
    let K := AdjoinRoot f
    let r : K := AdjoinRoot.root f
    have hr2 : r * r = algebraMap k K D := by
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      rw [← sq, show algebraMap k K D = AdjoinRoot.of f D from rfl]
      linear_combination h
    have hneg : f.eval₂ (Algebra.ofId k K) (-r) = 0 := by
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq]
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      exact h
    let τ : K →ₐ[k] K := AdjoinRoot.liftAlgHom f (Algebra.ofId k K) (-r) hneg
    have hτr : τ r = -r := AdjoinRoot.liftAlgHom_root _ _ _ _
    have hττ : τ.comp τ = AlgHom.id k K := by
      apply AdjoinRoot.algHom_ext
      show τ (τ r) = r
      rw [hτr, map_neg, hτr, neg_neg]
    let σ' : K ≃ₐ[k] K := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσr : σ' r = -r := hτr
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, mul_zero] at hr2
      exact hD ((algebraMap k K).injective (by rw [← hr2, map_zero]))
    have h2K : (2 : K) ≠ 0 := by
      intro h
      apply h2
      apply (algebraMap k K).injective
      rw [map_ofNat, h, map_zero]
    have hfin : Module.finrank k K = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hfdeg]
    refine ⟨K, inferInstance, inferInstance, σ', r, ⟨fun x => ?_, Or.inl ⟨Field.toIsField K, hfin,
      fun h => ?_⟩⟩, hr2, hσr, ?_⟩
    · show τ (τ x) = x
      exact congrArg (fun g : K →ₐ[k] K => g x) hττ
    · have h1 : σ' r = r := by rw [h]; rfl
      rw [hσr] at h1
      have : (2 : K) * r = 0 := by linear_combination -h1
      exact hr0 ((mul_eq_zero.1 this).resolve_left h2K)
    · have hinj : Function.Injective
          (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
        rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only at h
        by_cases hy : y1 = y2
        · subst hy
          have : algebraMap k K x1 = algebraMap k K x2 := by linear_combination h
          rw [(algebraMap k K).injective this]
        · exfalso
          have hy' : y1 - y2 ≠ 0 := sub_ne_zero.2 hy
          have hyK : algebraMap k K (y1 - y2) ≠ 0 := by
            rw [Ne, map_eq_zero_iff _ (algebraMap k K).injective]; exact hy'
          have hm : algebraMap k K (y1 - y2) * r = algebraMap k K (x2 - x1) := by
            rw [map_sub, map_sub]; linear_combination h
          have hrr : r = algebraMap k K ((x2 - x1) / (y1 - y2)) := by
            rw [map_div₀, eq_div_iff hyK, mul_comm]
            exact hm
          apply hsq ((x2 - x1) / (y1 - y2))
          apply (algebraMap k K).injective
          rw [map_mul, ← hrr, hr2]
      have hKm : Module.Finite k K := (AdjoinRoot.powerBasis hf0).finite
      have hKf : Finite K := Module.finite_of_finite k
      refine hinj.bijective_of_nat_card_le ?_
      letI := Fintype.ofFinite k
      letI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
        hfin, Fintype.card_prod, sq]

end PI.VolStabW
