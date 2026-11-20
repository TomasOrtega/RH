import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwiseStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.Descent

/- English proof (translation)
Introduce `R _ F T _ Cov _ Φ Φ' α hRef hS hI U`. Take `⟨hneg, cl, hcl_surj, hcl_eq, hcl_zero, hpull⟩` from `GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F`. Establish `key` using `GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent T Cov (Φ' ⋙ HC R F) (Φ ⋙ HC R F) (Functor.whiskerRight α (HC R F)) ?_ ?_ ?_ ?_ U`. Conclude with `(GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise R F _ _ (α.app U).unop).2 key`. Conclude with `⟨0, fun n hn V => ⟨hneg _ n hn, hneg _ n hn⟩⟩`.

Introduce `U' V' g hg`. Take `⟨X, a, h, hga, h1, h2⟩` from `hRef U' V' g hg`. Conclude with `⟨X, a, h, hga, fun n => ⟨GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ' U' X a h2 n, GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ U' X a h1 n⟩⟩`. Introduce `n U' z hz`. Take `⟨V, g, hg, y, hy⟩` from `hS U' n (cl (Φ.obj U').unop n z hz)`.

Take `⟨c, hc, rfl⟩` from `hcl_surj (Φ'.obj V).unop n y`. Take `⟨h1, e1⟩` from `hpull _ _ (α.app V).unop n c hc`. Take `⟨h2, e2⟩` from `hpull _ _ (Φ.map g).unop n z hz`. Rewrite `hy` using `[e1, e2, hcl_eq]`. Take `⟨y', hy'⟩` from `hy`.

Conclude with `⟨V, g, hg, c, y', hc, hy'⟩`. Introduce `n U' c hc ⟨y, hy⟩`. Establish `h0 : pull R (α.app U').unop F n (cl (Φ'.obj U').unop n c hc) = 0`. Take `⟨h1, e1⟩` from `hpull _ _ (α.app U').unop n c hc`. Rewrite using `[e1, hcl_zero]`.

Conclude with `⟨y, hy⟩`. Take `⟨V, g, hg, hV⟩` from `hI U' n _ h0`. Take `⟨h2, e2⟩` from `hpull _ _ (Φ'.map g).unop n c hc`. Rewrite `hV` using `[e2, hcl_zero]`. Take `⟨b, hb⟩` from `hV`.

Conclude with `⟨V, g, hg, b, hb.symm⟩`.
-/
theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  intro R _ F T _ Cov _ Φ Φ' α hRef hS hI U
  obtain ⟨hneg, cl, hcl_surj, hcl_eq, hcl_zero, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  have key := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent T Cov (Φ' ⋙ HC R F) (Φ ⋙ HC R F) (Functor.whiskerRight α (HC R F)) ?_ ?_ ?_ ?_ U
  · exact (GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise R F _ _ (α.app U).unop).2 key
  · exact ⟨0, fun n hn V => ⟨hneg _ n hn, hneg _ n hn⟩⟩
  · intro U' V' g hg
    obtain ⟨X, a, h, hga, h1, h2⟩ := hRef U' V' g hg
    exact ⟨X, a, h, hga, fun n => ⟨GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ' U' X a h2 n, GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ U' X a h1 n⟩⟩
  · intro n U' z hz
    obtain ⟨V, g, hg, y, hy⟩ := hS U' n (cl (Φ.obj U').unop n z hz)
    obtain ⟨c, hc, rfl⟩ := hcl_surj (Φ'.obj V).unop n y
    obtain ⟨h1, e1⟩ := hpull _ _ (α.app V).unop n c hc
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ.map g).unop n z hz
    rw [e1, e2, hcl_eq] at hy
    obtain ⟨y', hy'⟩ := hy
    exact ⟨V, g, hg, c, y', hc, hy'⟩
  · intro n U' c hc ⟨y, hy⟩
    have h0 : pull R (α.app U').unop F n (cl (Φ'.obj U').unop n c hc) = 0 := by
      obtain ⟨h1, e1⟩ := hpull _ _ (α.app U').unop n c hc
      rw [e1, hcl_zero]
      exact ⟨y, hy⟩
    obtain ⟨V, g, hg, hV⟩ := hI U' n _ h0
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ'.map g).unop n c hc
    rw [e2, hcl_zero] at hV
    obtain ⟨b, hb⟩ := hV
    exact ⟨V, g, hg, b, hb.symm⟩

end GlobalTheory.EtC.Descent
