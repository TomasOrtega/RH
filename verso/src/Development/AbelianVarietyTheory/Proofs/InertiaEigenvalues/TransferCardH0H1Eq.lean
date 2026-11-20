import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem transfer_card_H0_H1 : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  intro O _ G G' _ _ _ _ i M _ _ ρ p r _ c h
  letI := levZ (M := M) p r h

  have hact : ∀ (g' : G') (x : Lev M c),
      levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = levRep ρ c (i.symm g') x :=
    fun g' x => rfl
  constructor
  · apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro x
    show (∀ g, levRep ρ c g x = x) ↔ ∀ g', levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = x
    constructor
    · intro hx g'; rw [hact]; exact hx _
    · intro hx g
      have := hx (i g)
      rw [hact, ContinuousMulEquiv.symm_apply_apply] at this
      exact this
  · apply Nat.card_congr
    let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
    have hs : Continuous (i.symm : G' → G) := i.symm.continuous
    have hi : Continuous (i : G → G') := i.continuous
    let e : Z1 (levRep ρ c) ≃ Z1 ρ' :=
      { toFun := fun f => ⟨(f : G → Lev M c) ∘ i.symm, f.2.1.comp hs, fun a b => by
          show (f : G → Lev M c) (i.symm (a * b)) = (f : G → Lev M c) (i.symm a) + ρ' a ((f : G → Lev M c) (i.symm b))
          rw [map_mul, f.2.2]; rfl⟩
        invFun := fun f => ⟨(f : G' → Lev M c) ∘ i, f.2.1.comp hi, fun a b => by
          show (f : G' → Lev M c) (i (a * b)) = (f : G' → Lev M c) (i a) + levRep ρ c a ((f : G' → Lev M c) (i b))
          rw [map_mul, f.2.2, hact, ContinuousMulEquiv.symm_apply_apply]⟩
        left_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G → Lev M c) (i.symm (i g)) = _
          rw [ContinuousMulEquiv.symm_apply_apply]
        right_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G' → Lev M c) (i (i.symm g)) = _
          rw [ContinuousMulEquiv.apply_symm_apply] }
    refine Quotient.congr e ?_
    intro a b
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.coe_subtype, mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g' => ?_⟩
      have := hm (i.symm g')
      rw [hact]
      exact this
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (i g)
      rw [hact] at this
      change (a : G → Lev M c) (i.symm (i g)) - (b : G → Lev M c) (i.symm (i g)) = _ at this
      rw [ContinuousMulEquiv.symm_apply_apply] at this
      exact this

end GlobalTheory.ShapeNeg
