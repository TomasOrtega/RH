import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

noncomputable section

namespace GlobalTheory.MeanDual.Alg

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def halfTraceForm : LinearMap.BilinForm ℚ (Fin j → E) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (x ⬝ᵥ y) / 2)
    (fun x x' y => by rw [add_dotProduct, map_add, add_div])
    (fun c x y => by rw [smul_dotProduct, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])
    (fun x y y' => by rw [dotProduct_add, map_add, add_div])
    (fun c x y => by rw [dotProduct_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem halfTraceForm_apply (x y : Fin j → E) :
    halfTraceForm E j x y = Algebra.trace ℚ E (x ⬝ᵥ y) / 2 := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem halfTraceForm_symm : (halfTraceForm E j).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [halfTraceForm_apply, halfTraceForm_apply, dotProduct_comm]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem halfTraceForm_left (x : Fin j → E) (h : ∀ y, halfTraceForm E j x y = 0) : x = 0 := by
  ext i
  rw [Pi.zero_apply]
  by_contra hx

  have h1 := h (Pi.single i (x i)⁻¹)
  rw [halfTraceForm_apply, dotProduct_single, mul_inv_cancel₀ hx, ← map_one (algebraMap ℚ E),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one] at h1
  have h2 : (0 : ℚ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  linarith

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem halfTraceForm_nondegenerate : (halfTraceForm E j).Nondegenerate := by
  refine ⟨halfTraceForm_left E j, fun y hy => halfTraceForm_left E j y fun x => ?_⟩
  rw [(halfTraceForm_symm E j).eq]
  exact hy x

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem restrict_trDual (Λ : Submodule (𝓞 E) (Fin j → E)) :
    (trDual E j Λ).restrictScalars ℤ =
      (halfTraceForm E j).dualSubmodule (Λ.restrictScalars ℤ) := by
  ext y
  simp only [Submodule.restrictScalars_mem, mem_trDual, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, halfTraceForm_apply, eq_intCast]
  constructor
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm, hz]
    ring
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm]
    linarith

/- English proof (translation)
Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem smul_mem_span_rat_restrictScalars (Λ : Submodule (𝓞 E) (Fin j → E)) (a : E) {x : Fin j → E}
    (hx : x ∈ Submodule.span ℚ ((Λ.restrictScalars ℤ : Submodule ℤ (Fin j → E)) : Set (Fin j → E))) :
    a • x ∈ Submodule.span ℚ ((Λ.restrictScalars ℤ : Submodule ℤ (Fin j → E)) : Set (Fin j → E)) := by
  obtain ⟨m, s, hm, hms⟩ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)).exists_nsmul_eq (𝓞 E)
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hsy : s • y ∈ Λ := Λ.smul_mem s hy
    have key : a • y = (m : ℚ)⁻¹ • (s • y) := by
      rw [← algebraMap_smul E s y, ← hms, smul_assoc, ← Nat.cast_smul_eq_nsmul ℚ,
        inv_smul_smul₀ (by exact_mod_cast hm)]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [smul_add]
    exact add_mem hy hz
  | smul q y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hy

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isLattice_restrict (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsLattice E Λ) :
    Submodule.IsLattice ℚ (Λ.restrictScalars ℤ) where
  fg := Submodule.FG.restrictScalars h.fg
  span_eq_top := by
    refine Submodule.eq_top_iff'.mpr fun v => ?_
    have hv : v ∈ Submodule.span E (Λ : Set (Fin j → E)) := by
      rw [h.span_eq_top]
      trivial
    induction hv using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy => exact smul_mem_span_rat_restrictScalars E j Λ a hy

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities.
-/
theorem exists_basis (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsLattice E Λ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (Fin j → E)),
      Λ.restrictScalars ℤ = Submodule.span ℤ (Set.range b) := by

  have := isLattice_restrict E j Λ h
  let bF := Module.finBasis ℤ (Λ.restrictScalars ℤ)
  refine ⟨_, bF.extendOfIsLattice ℚ, ?_⟩
  have hb : ⇑(bF.extendOfIsLattice ℚ) = (Λ.restrictScalars ℤ).subtype ∘ bF :=
    funext fun k => bF.extendOfIsLattice_apply ℚ k
  rw [hb, Set.range_comp, ← Submodule.map_span, bF.span_eq, Submodule.map_top,
    Submodule.range_subtype]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLattice_trDual_and_trDual_trDual :
    ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)),
      Submodule.IsLattice E Λ →
        Submodule.IsLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  intro E _ _ j Λ h
  obtain ⟨n, b, hb⟩ := exists_basis E j Λ h
  have hB := halfTraceForm_nondegenerate E j
  have hS := halfTraceForm_symm E j

  have hD : (trDual E j Λ).restrictScalars ℤ =
      Submodule.span ℤ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
    rw [restrict_trDual, hb, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Submodule.FG.of_restrictScalars ℤ
    rw [hD]
    exact Submodule.fg_span (Set.finite_range _)
  · refine eq_top_iff.mpr fun v _ => ?_
    have hv : v ∈ Submodule.span ℚ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
      rw [((halfTraceForm E j).dualBasis hB b).span_eq]
      trivial
    have h1 : Set.range ((halfTraceForm E j).dualBasis hB b) ⊆ (trDual E j Λ : Set (Fin j → E)) := by
      rintro _ ⟨k, rfl⟩
      have hk : (halfTraceForm E j).dualBasis hB b k ∈ (trDual E j Λ).restrictScalars ℤ := by
        rw [hD]
        exact Submodule.subset_span ⟨k, rfl⟩
      exact hk
    exact Submodule.span_le_restrictScalars ℚ E _ (Submodule.span_mono h1 hv)
  · apply Submodule.restrictScalars_injective ℤ _ _
    rw [restrict_trDual, restrict_trDual, hb,
      LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hB hS]

end GlobalTheory.MeanDual.Alg
