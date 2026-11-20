import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace GlobalTheory.IntDescend

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem lift_units {Γ A B : Type} [Group Γ] [Monoid A] [Monoid B] (φ : A →* B) (hφ : Function.Injective φ)
    (f : Γ →* Bˣ) (hf : ∀ g, ((f g : Bˣ) : B) ∈ Set.range φ) : ∃ f' : Γ →* Aˣ, (Units.map φ).comp f' = f := by
  classical
  have h1 : ∀ g, φ (Function.invFun φ ((f g : Bˣ) : B)) = f g := fun g => Function.invFun_eq (hf g)
  have hu : ∀ g, Function.invFun φ ((f g : Bˣ) : B) * Function.invFun φ ((f g⁻¹ : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, mul_inv_cancel, map_one f, Units.val_one]
  have hv : ∀ g, Function.invFun φ ((f g⁻¹ : Bˣ) : B) * Function.invFun φ ((f g : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, inv_mul_cancel, map_one f, Units.val_one]
  refine ⟨MonoidHom.mk' (fun g => ⟨Function.invFun φ ((f g : Bˣ) : B), Function.invFun φ ((f g⁻¹ : Bˣ) : B), hu g, hv g⟩) ?_, ?_⟩
  · intro a b
    apply Units.ext
    apply hφ
    change φ (Function.invFun φ ((f (a * b) : Bˣ) : B)) = φ (Function.invFun φ ((f a : Bˣ) : B) * Function.invFun φ ((f b : Bˣ) : B))
    rw [h1, map_mul φ, h1, h1, map_mul f, Units.val_mul]
  · ext g
    exact h1 g

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

def liftInt (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) : ↥(OL LL) :=
  ⟨⟨x, hx.1⟩, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l LL ⟨x, hx.1⟩).2 hx.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftInt_spec (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) :
    ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) (liftInt LL x hx) = x := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem incl_injective : Function.Injective ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

end GlobalTheory.IntDescend

namespace GlobalTheory.IntDescend

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem descend : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Γ : Type) [Group Γ], (∀ (n : ℕ) (f : Γ →* GL (Fin n) (PadicAlgCl l)), (∀ g i j, (f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1 ∧ ‖(f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1) → ∃ f' : Γ →* GL (Fin n) ↥(OL LL), (Matrix.GeneralLinearGroup.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom))).comp f' = f) ∧ ∀ χ : Γ →* (PadicAlgCl l)ˣ, (∀ g, ((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 ∧ ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1) → ∃ ψ : Γ →* (↥(OL LL))ˣ, (Units.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).toMonoidHom).comp ψ = χ := by
  intro l _ LL Γ _
  refine ⟨?_, ?_⟩
  · intro n f hf
    have hinj : Function.Injective
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro M N h
      refine Matrix.ext fun i j => ?_
      apply incl_injective LL
      have := congrArg (fun P : Matrix (Fin n) (Fin n) (PadicAlgCl l) => P i j) h
      simpa only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hr : ∀ g, ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) ∈ Set.range
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro g
      refine ⟨Matrix.of fun i j => liftInt LL _ (hf g i j), ?_⟩
      ext i j
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact liftInt_spec LL _ (hf g i j)
    exact lift_units _ hinj f hr
  · intro χ hχ
    refine lift_units _ (incl_injective LL) χ ?_
    intro g
    exact ⟨liftInt LL _ ⟨(hχ g).1, (hχ g).2.le⟩, liftInt_spec LL _ _⟩

end GlobalTheory.IntDescend
