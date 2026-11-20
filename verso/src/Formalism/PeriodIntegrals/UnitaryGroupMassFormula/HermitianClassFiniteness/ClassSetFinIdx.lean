import Mathlib
import Formalism.SatakeDualWeyl.Statement

namespace PI.UnitaryGroupMassFormula.InHHClassFin

open DoubleCoset

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately. A detailed English derivation is pending.
-/
theorem classSet_mono {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K ≤ K') :
    Finite (Formalism.UG.ClassSet Γ K) → Finite (Formalism.UG.ClassSet Γ K') := by
  intro hfin
  let f : Formalism.UG.ClassSet Γ K → Formalism.UG.ClassSet Γ K' := Quotient.map' id (fun a b hab => by
    have hb : b ∈ DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) := by
      rw [show DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) = DoubleCoset.doubleCoset b Γ K from hab]
      exact DoubleCoset.mem_doubleCoset_self Γ K b
    obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.mp hb
    have hb' : b ∈ DoubleCoset.doubleCoset a (Γ : Set G) (K' : Set G) :=
      DoubleCoset.mem_doubleCoset.mpr ⟨x, hx, y, h hy, hxy⟩
    exact (DoubleCoset.doubleCoset_eq_of_mem hb').symm)
  refine Finite.of_surjective f (fun q => ?_)
  induction q using Quotient.inductionOn' with
  | h x => exact ⟨Quotient.mk'' x, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem classSet_finIdx {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K' ≤ K)
    (hi : K'.relIndex K ≠ 0) :
    Finite (Formalism.UG.ClassSet Γ K) → Finite (Formalism.UG.ClassSet Γ K') := by
  intro hf
  haveI : (K'.subgroupOf K).FiniteIndex := ⟨hi⟩
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  let f : Formalism.UG.ClassSet Γ K × (K ⧸ K'.subgroupOf K) → Formalism.UG.ClassSet Γ K' :=
    fun p => DoubleCoset.mk Γ K' (p.1.out * ((p.2.out : K) : G))
  refine Finite.of_surjective f ?_
  intro q
  obtain ⟨g, rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  let k : K := ⟨b⁻¹, K.inv_mem hb⟩
  refine ⟨(DoubleCoset.mk Γ K g, (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)), ?_⟩
  have ht : ((QuotientGroup.mk k : K ⧸ K'.subgroupOf K).out)⁻¹ * k ∈ K'.subgroupOf K :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  rw [Subgroup.mem_subgroupOf] at ht
  show DoubleCoset.mk Γ K' _ = DoubleCoset.mk Γ K' g
  rw [DoubleCoset.eq]
  refine ⟨a⁻¹, Γ.inv_mem ha, _, ht, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, k]
  rw [hab]; group

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately.

Proceed by induction. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem classSet_map {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ K : Subgroup G) :
    Finite (Formalism.UG.ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom)) →
      Finite (Formalism.UG.ClassSet Γ K) := by
  intro hfin
  have himg : ∀ a : G, Φ '' DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) =
      DoubleCoset.doubleCoset (Φ a) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
        ((K.map Φ.toMonoidHom : Subgroup G') : Set G') := by
    intro a
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
      exact DoubleCoset.mem_doubleCoset.2 ⟨Φ h, ⟨h, hh, rfl⟩, Φ k, ⟨k, hk, rfl⟩, by simp [map_mul]⟩
    · intro hy
      obtain ⟨h', ⟨h, hh, rfl⟩, k', ⟨k, hk, rfl⟩, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
      exact ⟨h * a * k, DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩, by simp [map_mul]⟩
  let f : Formalism.UG.ClassSet Γ K → Formalism.UG.ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) :=
    Quotient.map' Φ (fun a b hab => by
      show DoubleCoset.doubleCoset (Φ a) _ _ = DoubleCoset.doubleCoset (Φ b) _ _
      rw [← himg, ← himg]
      exact congrArg (fun s => Φ '' s) hab)
  refine Finite.of_injective f (fun x y hxy => ?_)
  induction x using Quotient.inductionOn' with
  | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      apply Quotient.sound'
      have h1 : DoubleCoset.doubleCoset (Φ a) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
          ((K.map Φ.toMonoidHom : Subgroup G') : Set G') =
          DoubleCoset.doubleCoset (Φ b) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
          ((K.map Φ.toMonoidHom : Subgroup G') : Set G') := Quotient.exact' hxy
      rw [← himg, ← himg] at h1
      exact (Set.image_injective.2 Φ.injective) h1

end PI.UnitaryGroupMassFormula.InHHClassFin
