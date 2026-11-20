import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSelfDualClassesRootDiscr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem doubleCoset_surj_of_le {G : Type*} [Group G] (H K J : Subgroup G) :
    Function.Surjective (fun p : DoubleCoset.Quotient (H : Set G) (K : Set G) × (K ⧸ J.subgroupOf K) =>
      DoubleCoset.mk H J (p.1.out * (p.2.out : G))) := by
  intro c
  obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K c.out
  refine ⟨(DoubleCoset.mk H K c.out, QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K)), ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf K) (⟨k⁻¹, K.inv_mem hk⟩ : K)
  have hjJ : ((j : K) : G) ∈ J := Subgroup.mem_subgroupOf.mp j.2
  simp only
  rw [hj, e]
  conv_rhs => rw [← DoubleCoset.out_eq' H J c]
  rw [eq_comm, DoubleCoset.eq]
  refine ⟨h, hh, _, hjJ, ?_⟩
  simp [mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem doubleCoset_card_le {G : Type*} [Group G] (H K J : Subgroup G)
    [Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))] (hJ : J.relIndex K ≠ 0) :
    Finite (DoubleCoset.Quotient (H : Set G) (J : Set G)) ∧
      Nat.card (DoubleCoset.Quotient (H : Set G) (J : Set G)) ≤
        Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) * J.relIndex K := by
  have : Finite (K ⧸ J.subgroupOf K) := Nat.finite_of_card_ne_zero hJ
  refine ⟨Finite.of_surjective _ (doubleCoset_surj_of_le H K J), ?_⟩
  have := Nat.card_le_card_of_surjective _ (doubleCoset_surj_of_le H K J)
  rwa [Nat.card_prod] at this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the hypotheses and the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem cls_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  intro D N
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hconj : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x := by
    intro x
    apply D.host.φ₀.injective
    have h1 := IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
    have h2 := D.host.conjE_apply D.host.φ₀ x
    exact h1.trans h2.symm
  have hfr : Module.finrank ℚ D.host.E = 2 * fF D := by
    rw [D.host.finrank_cmField, fF, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr D.host.E N
  obtain ⟨hrat, -, hex, -, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hLt, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  have key : ∀ g : GA D N, ∃ L₀ ∈ R, ∃ h ∈ ratG D N, Lt (h⁻¹ * g) = L₀ := by
    intro g
    obtain ⟨h1, h2, h3⟩ := (hSD g).2
    obtain ⟨L₀, hL₀, γ, hγ, hx⟩ := hcov (Lt g) h1 h2 (by
      intro y
      rw [h3 y]
      refine forall_congr' fun x => forall_congr' fun _ => ?_
      constructor
      · rintro ⟨z, hz⟩
        have hz' : (z : D.host.E) = ∑ i, IsCMField.complexConj D.host.E (x i) * y i := hz
        rw [← hz']
        exact z.isIntegral_coe
      · intro hz
        exact ⟨⟨_, hz⟩, rfl⟩)
    have hm : γ.map (IsCMField.complexConj D.host.E) = γ.map D.host.conj := by
      ext i j
      simp only [Matrix.map_apply, hconj]
    rw [hm] at hγ
    obtain ⟨h, hh⟩ := hex γ hγ
    refine ⟨L₀, hL₀, h, (hrat h).2 ⟨γ, hh⟩, ?_⟩
    ext x
    rw [hmv h (h⁻¹ * g) γ hh x, mul_inv_cancel_left, hx]
  choose L₀ hL₀ h hh hL using key
  let f : Cls D N (intG D N) → R := fun c => ⟨L₀ c.out, hL₀ _⟩
  have hf : Function.Injective f := by
    intro c c' e
    have e' : L₀ c.out = L₀ c'.out := congrArg Subtype.val e
    rw [← hL, ← hL, hLt] at e'
    rw [← DoubleCoset.out_eq' _ _ c, ← DoubleCoset.out_eq' _ _ c', DoubleCoset.eq]
    refine ⟨h c'.out * (h c.out)⁻¹, Subgroup.mul_mem _ (hh _) (Subgroup.inv_mem _ (hh _)), _, e', ?_⟩
    group
  have hfin : Finite (Cls D N (intG D N)) := Finite.of_injective f hf
  refine ⟨hfin, ?_, fun J _ hJ => doubleCoset_card_le _ _ J hJ⟩
  have hc : Nat.card (Cls D N (intG D N)) ≤ R.card := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  refine le_trans (by exact_mod_cast hc) (hR.trans (le_of_eq ?_))
  have hrd : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = D.host.rdE := rfl
  rw [hrd, hfr]
  have : 3 * (2 * fF D) * N ^ 2 = 6 * fF D * N ^ 2 := by ring
  rw [this]
  congr 1
  push_cast
  ring

end GlobalTheory.NormSum
