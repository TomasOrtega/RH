import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `Y Z s _ _ I _`. Take `⟨k, ⟨e⟩⟩` from `Finite.exists_equiv_fin I`. Establish `hfold` using `GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y k`. Set `i : (∐ fun _ : I => Y) ≅ ∐ fun _ : Fin k => Y` to `Sigma.whiskerEquiv (f := fun _ : I => Y) (g := fun _ : Fin k => Y) e fun _ => Iso.refl Y`. Establish `hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y) ≫ s`.

Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[i]`. Use `⟨by rw [hd]; infer_instance, ?_⟩` and prove the remaining obligations. Use `HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)` as an intermediate fact.

Conclude with `IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.sigmaFEt_of :
    SigmaFEt := by
  intro Y Z s _ _ I _
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y k
  let i : (∐ fun _ : I => Y) ≅ ∐ fun _ : Fin k => Y :=
    Sigma.whiskerEquiv (f := fun _ : I => Y) (g := fun _ : Fin k => Y) e fun _ => Iso.refl Y
  have hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y) ≫ s := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
