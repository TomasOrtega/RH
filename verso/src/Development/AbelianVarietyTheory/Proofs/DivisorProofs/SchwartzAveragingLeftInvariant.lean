import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg

namespace GlobalTheory.AvgKO

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Substitute using the available equality. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem avg_fin : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (φ : Matrix (Fin n) (Fin n) k → ℂ), φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ (m : ℕ) (w : Fin m → ℂ) (u : Fin m → GL (Fin n) k), (∀ i, u i ∈ KO k (Fin n)) ∧ ∑ i, w i = 1 ∧
      ∀ g ∈ KO k (Fin n), ∀ X, ∑ i, w i * φ ((u i).val * (g.val * X)) = ∑ i, w i * φ ((u i).val * X) := by
  intro k _ _ _ _ n φ hφ
  obtain ⟨hlc, hcs⟩ := hφ

  let H : Subgroup (GL (Fin n) k) :=
    { carrier := {g | ∀ X, φ (g.val * X) = φ X}
      one_mem' := by intro X; simp
      mul_mem' := by
        intro a b ha hb X
        simp only [Set.mem_setOf_eq] at ha hb
        rw [Units.val_mul, Matrix.mul_assoc, ha, hb]
      inv_mem' := by
        intro a ha X
        simp only [Set.mem_setOf_eq] at ha
        have := ha ((a⁻¹ : GL (Fin n) k).val * X)
        rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at this
        exact this.symm }
  have hmemH : ∀ g, g ∈ H ↔ ∀ X, φ (g.val * X) = φ X := fun g => Iff.rfl
  let K := KO k (Fin n)
  have hcont : Continuous (fun p : GL (Fin n) k × Matrix (Fin n) (Fin n) k => p.1.val * p.2) :=
    (Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd
  let S := (fun p : GL (Fin n) k × Matrix (Fin n) (Fin n) k => p.1.val * p.2) '' ((K : Set (GL (Fin n) k)) ×ˢ tsupport φ)
  have hS : IsCompact S := (isCompact_KO.prod hcs).image hcont
  let Z := {p : GL (Fin n) k × Matrix (Fin n) (Fin n) k | φ (p.1.val * p.2) = φ p.2}
  have hZ : IsOpen Z := by
    have h1 : IsLocallyConstant (fun p : GL (Fin n) k × Matrix (Fin n) (Fin n) k => φ (p.1.val * p.2) - φ p.2) :=
      (hlc.comp_continuous hcont).sub (hlc.comp_continuous continuous_snd)
    have : Z = (fun p : GL (Fin n) k × Matrix (Fin n) (Fin n) k => φ (p.1.val * p.2) - φ p.2) ⁻¹' {0} := by
      ext p; simp [Z, sub_eq_zero]
    rw [this]; exact h1.isOpen_fiber 0
  have hsub : ({1} : Set (GL (Fin n) k)) ×ˢ S ⊆ Z := by
    rintro ⟨g, X⟩ ⟨hg, -⟩
    simp only [Set.mem_singleton_iff] at hg
    subst hg; simp [Z]
  obtain ⟨U, V, hU, -, h1U, hSV, hUV⟩ := generalized_tube_lemma isCompact_singleton hS hZ hsub
  have hUK : U ∩ (K : Set (GL (Fin n) k)) ⊆ H := by
    rintro g ⟨hgU, hgK⟩
    change g ∈ H
    rw [hmemH]
    intro X
    by_cases hX : X ∈ S
    · exact hUV (show (g, X) ∈ U ×ˢ V from ⟨hgU, hSV hX⟩)
    · have hX1 : φ X = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hXC
        exact hX ⟨(1, X), ⟨K.one_mem, hXC⟩, by simp⟩
      have hX2 : φ (g.val * X) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hXC
        refine hX ⟨(g⁻¹, g.val * X), ⟨K.inv_mem hgK, hXC⟩, ?_⟩
        simp only
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      rw [hX1, hX2]
  have hHo : IsOpen (H : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_of_mem_nhds H (g := 1)
      (Filter.mem_of_superset ((hU.inter isOpen_KO).mem_nhds ⟨h1U rfl, K.one_mem⟩) hUK)
  let L := H.subgroupOf K
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 isCompact_KO
  haveI : Finite (K ⧸ L) := Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
  haveI : Fintype (K ⧸ L) := Fintype.ofFinite _
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (K ⧸ L)
  have hm : (m : ℂ) ≠ 0 := by
    have : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · have x := e (QuotientGroup.mk 1)
        rw [h] at x
        exact x.elim0
      · exact h
    exact_mod_cast this.ne'
  refine ⟨m, fun _ => 1 / (m : ℂ), fun i => ((Quotient.out (e.symm i) : K) : GL (Fin n) k)⁻¹, ?_, ?_, ?_⟩
  · intro i; exact K.inv_mem (Quotient.out (e.symm i)).2
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro g hg X
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    let F : K ⧸ L → ℂ := fun q => φ ((((Quotient.out q : K) : GL (Fin n) k)⁻¹).val * X)
    have key : ∀ y : K, F (QuotientGroup.mk y) = φ ((((y : GL (Fin n) k))⁻¹).val * X) := by
      intro y
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L y
      simp only [F]
      rw [hh]
      have hh' : ((h : K) : GL (Fin n) k)⁻¹ ∈ H := H.inv_mem (Subgroup.mem_subgroupOf.1 h.2)
      rw [Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
      exact (hmemH _).1 hh' _
    let g' : K := ⟨g, hg⟩
    have hl : ∀ i, φ ((((Quotient.out (e.symm i) : K) : GL (Fin n) k)⁻¹).val * (g.val * X))
        = F (g'⁻¹ • e.symm i) := by
      intro i
      have hq : g'⁻¹ • e.symm i = QuotientGroup.mk (g'⁻¹ * Quotient.out (e.symm i)) := by
        conv_lhs => rw [← QuotientGroup.out_eq' (e.symm i)]
        rfl
      rw [hq, key, Subgroup.coe_mul, _root_.mul_inv_rev, InvMemClass.coe_inv, inv_inv, Units.val_mul,
        Matrix.mul_assoc]
    calc ∑ i, φ ((((Quotient.out (e.symm i) : K) : GL (Fin n) k)⁻¹).val * (g.val * X))
        = ∑ i, F (g'⁻¹ • e.symm i) := Finset.sum_congr rfl fun i _ => hl i
      _ = ∑ q, F (g'⁻¹ • q) := Equiv.sum_comp e.symm (fun q => F (g'⁻¹ • q))
      _ = ∑ q, F q := Equiv.sum_comp (MulAction.toPerm g'⁻¹) F
      _ = ∑ i, F (e.symm i) := (Equiv.sum_comp e.symm F).symm

end GlobalTheory.AvgKO
