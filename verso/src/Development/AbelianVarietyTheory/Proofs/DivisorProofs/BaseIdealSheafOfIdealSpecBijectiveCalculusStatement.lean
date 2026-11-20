import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculus
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBaseIdealSheafOfIdealSpecBijectiveCalculus.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus : (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  first | exact @GlobalTheory.FormalAlg.specIdeal | exact GlobalTheory.FormalAlg.specIdeal | (intros; apply GlobalTheory.FormalAlg.specIdeal <;> assumption)
