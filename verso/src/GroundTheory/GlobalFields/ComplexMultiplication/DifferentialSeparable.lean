import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Differential

namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [E.IsElliptic] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem D_comap_mem_span (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    D F E.toAffine.FunctionField (φ.comap f) ∈
      Submodule.span E.toAffine.FunctionField {isogenyPullback φ (invariantDifferential E')} := by
  rw [← isogenyPullback_D, ← invCoeff_smul E' (D F _ f), isogenyPullback_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem span_isogenyPullback_eq_top (φ : Isogeny E E') (hφ : φ.IsSeparable) :
    Submodule.span E.toAffine.FunctionField {isogenyPullback φ (invariantDifferential E')} = ⊤ := by
  set M := φ.comap.fieldRange
  set K := E.toAffine.FunctionField
  have : Algebra.IsSeparable M K := hφ
  have : Algebra.FormallyUnramified M K := .of_isSeparable _ _
  refine eq_top_iff.mpr fun ω hω ↦ ?_
  clear hω
  obtain ⟨z, rfl⟩ := (exact_mapBaseChange_map F M K ω).mp (Subsingleton.elim _ _)
  induction z with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hb : b ∈ Submodule.span M (Set.range (D F M)) := by
      rw [span_range_derivation]; trivial
    induction hb using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨e, rfl⟩ := h
      rw [map_D]
      obtain ⟨f, hf⟩ := e.2
      change D F K (e : K) ∈ _
      rw [← hf]
      exact D_comap_mem_span φ f
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c _ _ h =>
      rw [map_smul, algebra_compatible_smul K c]
      exact Submodule.smul_mem _ _ h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Check the elementary cases of the proposition. A detailed English derivation is pending.
-/
theorem isogenyPullback_ne_zero_of_isSeparable (φ : Isogeny E E') (hφ : φ.IsSeparable) :
    isogenyPullback φ (invariantDifferential E') ≠ 0 := by
  intro h0
  have htop := span_isogenyPullback_eq_top φ hφ
  rw [h0, Submodule.span_singleton_eq_bot.mpr rfl] at htop
  have hmem : invariantDifferential E ∈ (⊥ : Submodule E.toAffine.FunctionField _) := by
    rw [htop]; trivial
  exact invariantDifferential_ne_zero E ((Submodule.mem_bot _).mp hmem)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isSeparable_of_isogenyPullback_ne_zero (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') ≠ 0) : φ.IsSeparable := by
  set M := φ.comap.fieldRange
  set K := E.toAffine.FunctionField
  have hc : isogCoeff φ ≠ 0 := by
    intro h; apply hφ; rw [isogenyPullback_invariantDifferential_eq_smul, h, zero_smul]
  have htop : Submodule.span K {isogenyPullback φ (invariantDifferential E')} = ⊤ := by
    rw [isogenyPullback_invariantDifferential_eq_smul,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]
    exact span_invariantDifferential E
  have hx : φ.comap (genX E') ∈ M := ⟨genX E', rfl⟩
  have hzero : KaehlerDifferential.map F M K K (isogenyPullback φ (invariantDifferential E')) = 0 := by
    rw [invariantDifferential_eq, isogenyPullback_smul, isogenyPullback_D, map_smul, map_D]
    have : D M K (algebraMap K K (φ.comap (genX E'))) = D M K (algebraMap M K ⟨_, hx⟩) := rfl
    rw [this, Derivation.map_algebraMap, smul_zero]
  have hsub : Subsingleton Ω[K⁄M] := by
    refine subsingleton_of_forall_eq 0 fun ω' ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective F M K ω'
    have hω : ω ∈ Submodule.span K {isogenyPullback φ (invariantDifferential E')} := by
      rw [htop]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    rw [map_smul, hzero, smul_zero]
  have : Algebra.FormallyUnramified M K := ⟨hsub⟩
  have : FiniteDimensional M K := φ.finiteDimensional
  have : Algebra.EssFiniteType M K := inferInstance
  exact Algebra.FormallyUnramified.isSeparable M K

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isSeparable_iff_isogenyPullback_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogenyPullback φ (invariantDifferential E') ≠ 0 :=
  ⟨isogenyPullback_ne_zero_of_isSeparable φ, isSeparable_of_isogenyPullback_ne_zero φ⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem isSeparable_iff_isogCoeff_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogCoeff φ ≠ 0 := by
  rw [isSeparable_iff_isogenyPullback_ne_zero, isogenyPullback_invariantDifferential_eq_smul]
  exact ⟨fun h h0 => h (by rw [h0, zero_smul]),
    fun h h0 => h ((smul_eq_zero.mp h0).resolve_right (invariantDifferential_ne_zero E))⟩

end GroundTheory.Global
