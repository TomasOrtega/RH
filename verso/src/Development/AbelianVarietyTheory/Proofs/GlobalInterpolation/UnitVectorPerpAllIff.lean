import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.UnitVectorOrthogonal
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeComplements

noncomputable section

namespace GlobalTheory.UnitVectorPerpCompare

open NumberField Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem perp_eq (W : HSpace E) (x : W.V) : UnitVectorOrthogonal.perp W x = SelfDualLatticeComplements.perp W x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem perpLat_eq (W : HSpace E) (L : Submodule (𝓞 E) W.V) (x : W.V) :
    UnitVectorOrthogonal.perpLat W L x = L ⊓ (SelfDualLatticeComplements.perp W x).restrictScalars (𝓞 E) := rfl

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem selfDual_iff (W : HSpace E) (L : Submodule (𝓞 E) W.V) :
    UnitVectorOrthogonal.IsSelfDualLat W L ↔ SelfDualLatticeComplements.IsSelfDualLattice W L := Iff.rfl

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem ofKind_iff (W : HSpace E) (M P Q : ℕ) :
    UnitVectorOrthogonal.OfKind W M P Q ↔ SelfDualLatticeComplements.OfKind W M P Q :=
  ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem hasComplement_iff (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) :
    UnitVectorOrthogonal.HasComplement W x M' P' Q' ↔ SelfDualLatticeComplements.HasComplement W x M' P' Q' := by
  constructor
  · rintro ⟨L, hL, hx, hs, W', ι, hk, hi, hr, hm⟩
    exact ⟨L, W', ι, (selfDual_iff W L).1 hL, hx, (ofKind_iff _ _ _ _).1 hk, hi, hr, hm, hs⟩
  · rintro ⟨L, W', ι, hL, hx, hk, hi, hr, hm, hs⟩
    exact ⟨L, (selfDual_iff W L).2 hL, hx, hs, W', ι, (ofKind_iff _ _ _ _).2 hk, hi, hr, hm⟩

omit [NumberField E] [StarRing E] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem forall_step_iff (P Q : ℕ) (C : E → ℕ → ℕ → Prop) :
    (∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' → C β P' Q') ↔
      (1 ≤ P → C 1 (P - 1) Q) ∧ (1 ≤ Q → C (-1) P (Q - 1)) := by
  constructor
  · intro h
    exact ⟨fun hP => h _ _ _ (Or.inl ⟨rfl, hP, rfl, rfl⟩),
      fun hQ => h _ _ _ (Or.inr ⟨rfl, hQ, rfl, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ β P' Q' (⟨rfl, hP, rfl, rfl⟩ | ⟨rfl, hQ, rfl, rfl⟩)
    · exact h1 hP
    · exact h2 hQ

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem conclusion_iff (W : HSpace E) (M P Q : ℕ) :
    ((1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) (P - 1) Q) ∧
      (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) P (Q - 1))) ↔
    ∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q' := by
  rw [forall_step_iff P Q
    (fun β P' Q' => ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q')]
  simp only [hasComplement_iff]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem conclusionAll_iff (W : HSpace E) (M P Q : ℕ) :
    ((1 ≤ P → (∃ x : W.V, W.hD x x = 1) ∧
        ∀ x : W.V, W.hD x x = 1 → UnitVectorOrthogonal.HasComplement W x (M - 1) (P - 1) Q) ∧
      (1 ≤ Q → (∃ x : W.V, W.hD x x = -1) ∧
        ∀ x : W.V, W.hD x x = -1 → UnitVectorOrthogonal.HasComplement W x (M - 1) P (Q - 1))) ↔
    ∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' →
      (∃ x : W.V, W.hD x x = β) ∧
        ∀ x : W.V, W.hD x x = β → SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q' := by
  rw [forall_step_iff P Q
    (fun β P' Q' => (∃ x : W.V, W.hD x x = β) ∧
        ∀ x : W.V, W.hD x x = β → SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q')]
  simp only [hasComplement_iff]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem over_iff : UnitVectorOrthogonal.UnitVectorPerpOver E ↔ SelfDualLatticeComplements.ExistsPerpOver E := by
  refine forall_congr' fun W => forall_congr' fun M => forall_congr' fun P =>
    forall_congr' fun Q => imp_congr (ofKind_iff W M P Q) (imp_congr Iff.rfl ?_)
  exact conclusion_iff W M P Q

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem overAll_iff : UnitVectorOrthogonal.UnitVectorPerpEveryOver E ↔ SelfDualLatticeComplements.ForallPerpOver E := by
  refine forall_congr' fun W => forall_congr' fun M => forall_congr' fun P =>
    forall_congr' fun Q => imp_congr (ofKind_iff W M P Q) (imp_congr Iff.rfl ?_)
  exact conclusionAll_iff W M P Q

end General

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitVectorPerp_iff (D : D7) : UnitVectorOrthogonal.UnitVectorPerp D ↔ SelfDualLatticeComplements.UnitVectorPerp D :=
  @over_iff D.host.E _ _ D.host.cmStar

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitVectorPerpAll_iff (D : D7) :
    UnitVectorOrthogonal.UnitVectorPerpEvery D ↔ SelfDualLatticeComplements.UnitVectorPerpAll D :=
  @overAll_iff D.host.E _ _ D.host.cmStar

end GlobalTheory.UnitVectorPerpCompare

end
