import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassOrbitsEqTsumFiber
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem sumData_nT_eq_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (C : Set S.FrP) (P : S.Datum → Submodule L.O S.V → Prop), (∀ h ∈ S.H0, ∀ d Λ, S.IsTerm d Λ → P d Λ → P (h • d) (h • Λ)) → (S.sumData fun d => S.nT d C (P d)) = ∑' o : MulAction.orbitRel.Quotient S.H0 (Submodule L.O S.V), if ∃ d, S.IsTerm d o.out ∧ P d o.out ∧ S.Fr d o.out = C then ENNReal.ofReal (invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV o.out)) else 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S C P hP
  let π : Submodule L.O S.V → S.Datum := fun Λ =>
    if H : ∃ d, S.IsTerm d Λ then H.choose else (⊥, ⊥, ∅)
  have hπ : ∀ d Λ, S.IsTerm d Λ → π Λ = d := by
    intro d Λ hd
    have H : ∃ d, S.IsTerm d Λ := ⟨d, hd⟩
    simp only [π, dif_pos H]
    exact (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hd).2.2.2.2.2.2.2 _ H.choose_spec
  obtain ⟨v1, v2⟩ := GlobalTheory.HL.Frames.stab_commensurable_invVol_smul L r k S
  have hlat : ∀ d Λ, S.IsTerm d Λ → IsLat L Λ := fun d Λ hd =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hd).1.1
  have key := mass_orbits_eq_tsum_fiber S.H0 S.complementReferenceCompactSubgroup
    (fun Λ : Submodule L.O S.V => ∃ d, S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C) π inf_le_left
    (by
      rintro h hh Λ ⟨d, hd, hp, hc⟩
      obtain ⟨a1, -, -, -, -, a6⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hd h hh
      refine ⟨⟨h • d, a1, hP h hh d Λ hd hp, a6.trans hc⟩, ?_, (v1 Λ (hlat d Λ hd)).2.2 h hh⟩
      rw [hπ _ _ a1, hπ _ _ hd])
    (by
      rintro Λ ⟨d, hd, -, -⟩
      rw [hπ _ _ hd]
      exact ⟨(v1 Λ (hlat d Λ hd)).1, (v1 Λ (hlat d Λ hd)).2.1, (v2 d Λ hd).1, (v2 d Λ hd).2⟩)
  refine Eq.trans ?_ (key.symm.trans ?_)
  · unfold Frames.sumData Frames.nu Frames.nT
    refine tsum_congr fun c => ?_
    refine congrArg (fun s : Set (Submodule L.O S.V) => _ * ((s.encard : ℕ∞) : ℝ≥0∞)) ?_
    ext Λ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hd, hp, hc⟩
      exact ⟨⟨_, hd, hp, hc⟩, hπ _ _ hd⟩
    · rintro ⟨⟨d, hd, hp, hc⟩, e⟩
      rw [hπ _ _ hd] at e
      rw [← e]
      exact ⟨hd, hp, hc⟩
  · refine tsum_congr fun o => ?_
    congr

end GlobalTheory.HL
