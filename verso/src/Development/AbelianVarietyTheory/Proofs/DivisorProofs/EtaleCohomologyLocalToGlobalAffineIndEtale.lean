import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.LocGlobIndEt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eqv_of_comp_iso {R : Type} [CommRing R] {E E' E'' : Spc} (g : E ⟶ E') (e : E' ⟶ E'') [IsIso e] (F : Shv R)
    (h : Eqv R (g ≫ e) F) : Eqv R g F := by
  intro n
  have he : Function.Bijective (pull R e F n) := by
    refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv e) F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    · rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  refine (Function.Bijective.of_comp_iff (pull R g F n) he).1 ?_
  have : (⇑(pull R g F n) ∘ ⇑(pull R e F n)) = ⇑(pull R (g ≫ e) F n) := funext fun x => (pull_comp R g e F n x).symm
  rw [this]
  exact h n

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality.

A detailed English derivation is pending.
-/
theorem main : ∀ (q : ℕ) (B : Type) [CommRing B] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact f]
    [QuasiSeparated f], IsUnit (q : B) → ∀ i : ℤ, (∀ (A : Type) [CommRing A] [Algebra B A], SH A → IndEt B A →
      Eqv _ (sch.map (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B A))))) (tw q i)) →
    Eqv _ (sch.map f) (tw q i) := by
  intro q B _ Y f _ _ _ i hyp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y (Spec (CommRingCat.of B)) (Spec (CommRingCat.of B)) f
    (𝟙 _) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hind, rfl⟩ := isStalk_affine B O s hs
  have key := @hyp O _ inst hSH hind
  refine eqv_of_comp_iso _ (sch.map (pullback.snd (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap B O))))) _ ?_
  rw [← sch.map_comp, pullback.lift_snd, Category.comp_id]
  generalize hf : f ≫ 𝟙 _ = f'
  rw [Category.comp_id] at hf
  subst hf
  exact key

end GlobalTheory.LocGlobIndEt
