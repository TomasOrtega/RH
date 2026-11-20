import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCompAlgebraMapEq
open Polynomial
namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `@_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq`.

Consider the case `exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq`. Consider the case `exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq`. Consider the case `(apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> first | assumption | infer_instance)`.

Consider the case `(intros; exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq ..)`.
-/
theorem exists_ringHom_extension_algClosed_of_isIntegral_injective {R S K : Type*} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (ψ : R →+* K) : ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq ..)

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ _ hinj g φ z`. Prove the components needed by the constructor for the conclusion. Introduce `h haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `hg : IsIntegral A g` using `Algebra.IsIntegral.isIntegral g`. Establish `h' : (minpoly A g).eval₂ φ z = 0` using `by rwa [IsRoot, eval_map] at h`.

Set `e` to `minpoly.equivAdjoin hg`. Set `ψ : Algebra.adjoin A {g} →+* ℂ` to `(AdjoinRoot.lift φ z h').comp (e.symm : _ →+* _)`. Use `haveI : Algebra.IsIntegral (Algebra.adjoin A {g}) B := Algebra.IsIntegral.tower_top A`. Take `⟨x, hx⟩` from `exists_ringHom_extension_algClosed_of_isIntegral_injective (S := B) Subtype.val_injective ψ`. Establish `hx' : ∀ r : Algebra.adjoin A {g}, x r = ψ r` using `fun r => RingHom.congr_fun hx r`.

Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Use `hx' (algebraMap A _ a)` as an intermediate fact. Simplify using `only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of] at this`. Conclude with `this`.

Establish `h1 : (e (AdjoinRoot.root _) : B) = g`. Express the relevant statement in the definitionally equal form `((AdjoinRoot.Minpoly.toAdjoin A g (AdjoinRoot.root _) : Algebra.adjoin A {g}) : B) = g`. Simplify using `[AdjoinRoot.Minpoly.toAdjoin]`. Use `hx' (e (AdjoinRoot.root _))` as an intermediate fact. Simplify using `only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_root] at this`.

Rewrite `this` using `[h1]`. Then use the resulting hypothesis. Introduce and unpack `⟨x, rfl, rfl⟩`. Rewrite using `[IsRoot, eval_map, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]`.
-/
theorem isRoot_map_minpoly_iff_exists_ringHom : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by
  intro A B _ _ _ _ _ _ _ hinj g φ z
  constructor
  · intro h
    haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    have hg : IsIntegral A g := Algebra.IsIntegral.isIntegral g
    have h' : (minpoly A g).eval₂ φ z = 0 := by rwa [IsRoot, eval_map] at h
    let e := minpoly.equivAdjoin hg
    let ψ : Algebra.adjoin A {g} →+* ℂ := (AdjoinRoot.lift φ z h').comp (e.symm : _ →+* _)
    haveI : Algebra.IsIntegral (Algebra.adjoin A {g}) B := Algebra.IsIntegral.tower_top A
    obtain ⟨x, hx⟩ := exists_ringHom_extension_algClosed_of_isIntegral_injective (S := B) Subtype.val_injective ψ
    have hx' : ∀ r : Algebra.adjoin A {g}, x r = ψ r := fun r => RingHom.congr_fun hx r
    refine ⟨x, ?_, ?_⟩
    · ext a
      have := hx' (algebraMap A _ a)
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of] at this
      exact this
    · have h1 : (e (AdjoinRoot.root _) : B) = g := by
        change ((AdjoinRoot.Minpoly.toAdjoin A g (AdjoinRoot.root _) : Algebra.adjoin A {g}) : B) = g
        simp [AdjoinRoot.Minpoly.toAdjoin]
      have := hx' (e (AdjoinRoot.root _))
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_root] at this
      rwa [h1] at this
  · rintro ⟨x, rfl, rfl⟩
    rw [IsRoot, eval_map, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

end GlobalTheory
