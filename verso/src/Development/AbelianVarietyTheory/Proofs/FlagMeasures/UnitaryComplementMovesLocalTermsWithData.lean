import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.LocalMove

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Simplify by unfolding definitions. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Express the relevant assertion in an equivalent form by its definition. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP h hh d d' τ hτ hmv
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨hH0, -, -, hlat, -⟩ := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, hmov, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh0 : c.grp h ∈ S.H0 := (hH0 h).1 hh
  have ge : ∀ (g : V ≃ₗ[E] V) (x : V), c.grp g (c.e x) = c.e (g x) := GlobalTheory.HL.CoordTerm.grp_e c
  obtain ⟨Λ, f, f', T, T'⟩ := τ
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, hG⟩ := hτ
  dsimp only at hT hT' hf hΛ hf' hΛ' hG ⊢
  subst hT hT' hf hf'

  have fixA : ∀ b, h (n (P.A.f b)) = n (P.A.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_left
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn) (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  have fixB : ∀ b, h (n' (P.B.f b)) = n' (P.B.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f'_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_right
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn') (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  simp only [fixA, fixB]
  refine ⟨?_, ?_⟩
  · have hW := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d n n' Λ).1
      ⟨⟨rfl, rfl, ⟨n, hn, rfl, hΛ⟩, ⟨n', hn', rfl, hΛ'⟩, hG⟩, hn, hn', hΛ, hΛ'⟩
    obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hh0
    rw [(hmov h hh d d').1 hmv, ← hlat] at hW'
    obtain ⟨m0, rfl⟩ := c.grp.surjective m
    obtain ⟨m0', rfl⟩ := c.grp.surjective m'
    have e1 : (fun b => m0 (P.A.f b)) = fun b => n (P.A.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f_eq]; exact hm b
    have e2 : (fun b => m0' (P.B.f b)) = fun b => n' (P.B.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f'_eq]; exact hm' b
    have := ((GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d' m0 m0' (LocNG.img h Λ)).2 hW').1
    rw [e1, e2] at this
    exact this
  ·
    set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with ht
    have fam : ∀ i, h (H.MMfam t i) = H.MMfam t i := by
      intro i
      unfold HermSp.MMfam
      cases M.split with
      | none => rcases i with b | b <;> simp [ht, fixA, fixB]
      | some g => rcases i with b | b <;> simp [ht, fixA, fixB, map_sub]
    have fixS : ∀ x ∈ Submodule.span E (Set.range (H.MMfam t)), h x = x := by
      intro x hx
      have := LinearMap.eqOn_span' (f := (h : V →ₗ[E] V)) (g := LinearMap.id)
        (s := Set.range (H.MMfam t)) (by rintro _ ⟨i, rfl⟩; exact fam i) hx
      simpa using this
    change (∃ v ∈ LocNG.img h Λ, _) ↔ ∃ v ∈ Λ, _
    constructor
    · rintro ⟨v, hv, hE, hO⟩
      obtain ⟨w, hw, rfl⟩ := hv
      have hw' : h w = w := by
        have := fixS _ hE
        exact h.injective (by simpa using this)
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hE hO ⊢
      rw [hw'] at hE hO
      exact ⟨w, hw, hE, hO⟩
    · rintro ⟨v, hv, hE, hO⟩
      exact ⟨v, ⟨v, hv, fixS v hE⟩, hE, hO⟩

end GlobalTheory.HL.LocalMove
