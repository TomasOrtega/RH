import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.IntegralPoints

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Supply the required witnesses or components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isOpen_isCompact_intGL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (O : Subring R) (ho : IsOpen (O : Set R)) (hc : IsCompact (O : Set R)) (n : ℕ) :
    IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} ∧
    IsCompact {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} := by
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} =
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) ∩
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) := by
      ext g
      simp [Set.mem_iInter]
    rw [e]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_coe_inv.matrix_elem i j)
  · have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
      have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hc
      have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
          Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R) :=
        Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
      exact e ▸ this
    have := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage
      (hM.prod (hM.image MulOpposite.continuous_op))
    convert this using 1
    ext g
    exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
      have : A = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := MulOpposite.op_injective e
      exact this ▸ hA i j⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem coe_Kf (n : ℕ) : (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) | (∀ i j, (g : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈ Formalism.UG.intAd E) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈
        Formalism.UG.intAd E} := by
  ext g
  simp only [SetLike.mem_coe, PositivityTheory.Rg.BcB.G8.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i j w => ?_, fun i j w => ?_⟩
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      exact h1.1 i j
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      have h2 := h1.2 i j
      rw [← map_inv] at h2
      exact h2
  · rintro ⟨h1, h2⟩ w
    rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => h1 i j w, fun i j => ?_⟩
    rw [← map_inv]
    exact h2 i j w

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem kfOC : PositivityTheory.Rg.BcB.G8.KfOC := by
  intro E _ _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  rw [coe_Kf]
  exact isOpen_isCompact_intGL (Formalism.UG.intAd E) Formalism.MainNotions.Gaps.LevGap.isOpen_intAd
    Formalism.MainNotions.Gaps.LevGap.isCompact_intAd n

end GlobalTheory.CompanionTheory.IntegralPoints
