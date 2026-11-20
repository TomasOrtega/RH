import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

def Scheme.Modules.SupportedIn (F : X.Modules) (T : Set X) : Prop :=
  ∀ U : X.Opens, Disjoint (U : Set X) T → ∀ s : Γ(F, U), s = 0

namespace Scheme.Modules.SupportedIn

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
lemma mono {F : X.Modules} {T T' : Set X} (h : Scheme.Modules.SupportedIn F T) (hT : T ⊆ T') :
    Scheme.Modules.SupportedIn F T' :=
  fun U hU s => h U (hU.mono_right hT) s

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities.
-/
lemma of_iso {F G : X.Modules} (e : F ≅ G) {T : Set X} (h : Scheme.Modules.SupportedIn F T) :
    Scheme.Modules.SupportedIn G T := by
  intro U hU s
  have h1 : e.inv.app U s = 0 := h U hU _
  have h2 : e.hom.app U (e.inv.app U s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [← h2, h1, map_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
lemma pushforward {Z : Scheme.{u}} (j : Z ⟶ X) {G : Z.Modules} {T' : Set Z}
    (h : Scheme.Modules.SupportedIn G T') :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pushforward j).obj G) (j.base '' T') := by
  intro U hU s
  refine h (j ⁻¹ᵁ U) ?_ s
  rw [Set.disjoint_left]
  intro z hz hzT
  exact Set.disjoint_left.1 hU hz ⟨z, hzT, rfl⟩

end Scheme.Modules.SupportedIn

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma isIso_of_bijective_app {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ U : X.Opens, Function.Bijective (φ.app U)) : IsIso φ := by
  have : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    have : ∀ U : (X.Opens)ᵒᵖ, IsIso (((Scheme.Modules.toPresheaf X).map φ).app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h U.unop)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) (U : X.Opens) (s : Γ(F, U)) : s = 0 := by
  have : (𝟙 F : F ⟶ F).app U s = (0 : F ⟶ F).app U s := by rw [hF.eq_of_src (𝟙 F) 0]
  simpa using this

section Restrict

variable {F G : X.Modules} (φ : F ⟶ G) (W : X.Opens)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
lemma kernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (kernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  apply kernel_ι_app_injective φ U
  apply (h U hUW).1
  rw [map_zero, map_zero, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    kernel.condition]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma cokernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (cokernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  let R := Scheme.Modules.restrictFunctor W.ι
  have hφ : IsIso (R.map φ) := isIso_of_bijective_app _ fun V =>
    h _ ((W.ι.image_le_opensRange V).trans (by simp))
  have hZ : IsZero (R.obj (cokernel φ)) :=
    (isZero_cokernel_of_epi (R.map φ)).of_iso (PreservesCokernel.iso R φ)
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUW
  have h0 : (cokernel φ).presheaf.map (eqToHom hE).op s = 0 :=
    eq_zero_of_isZero hZ (W.ι ⁻¹ᵁ U) _
  have hinv : (cokernel φ).presheaf.map (eqToHom hE.symm).op
      ((cokernel φ).presheaf.map (eqToHom hE).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hinv, h0, map_zero]

end Restrict

end

end GroundTheory.Arith.SchemeCoh
