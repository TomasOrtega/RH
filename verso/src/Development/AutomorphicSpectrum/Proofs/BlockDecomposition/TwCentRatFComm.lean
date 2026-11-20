import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatCentComm

/- English proof (translation)
Establish `h1 : g * D = D * θ g` using `hg`. Establish `h2 : θ g = D⁻¹ * g * D` using `by rw [mul_assoc, h1]; group`. Establish `h3` using `congrArg θ h2`. Rewrite `h3` using `[hθ, map_mul, map_mul, map_inv, h2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem commute_norm {G : Type} [Group G] (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (D g : G)
    (hg : g ∈ twCent θ D) : g * (D * θ D) = (D * θ D) * g := by
  have h1 : g * D = D * θ g := hg
  have h2 : θ g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg θ h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * θ D)
      = (D * θ D) * ((θ D)⁻¹ * (D⁻¹ * g * D) * θ D) := by group
    _ = _ := by rw [← h3]

/- English proof (translation)
Introduce `E _ _ _ n δ hs a ha b hb`. Establish `hθ : ∀ g, thF E n (thF E n g) = g` using `GlobalTheory.LocTwist.thetaGL_thetaGL n _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y)`. Take `⟨v, hv⟩` from `GlobalTheory.ClassParam.exists_cyclic_field _ hs`. Establish `hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E n δ * thF E n (ratF E n δ)).val (algebraMap E (Af E) ∘ v)).det`. Establish `h1` using `(IsUnit.mk0 _ hv).map (algebraMap E (Af E))`.

Rewrite `h1` using `[RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map]`. Rewrite using `[GlobalTheory.MassNorm.thF_ratF, ← map_mul]`. Conclude with `h1`. Establish `hc : ∀ g ∈ twCent (thF E n) (ratF E n δ), Commute g.val (ratF E n δ * thF E n (ratF E n δ)).val` using `fun g hg => by`. Express the relevant statement in the definitionally equal form `g.val * _ = _ * g.val`.

Rewrite using `[← Units.val_mul, ← Units.val_mul, commute_norm _ hθ _ _ hg]`. Take `⟨p, hp⟩` from `GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc a ha)`. Take `⟨q, hq⟩` from `GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc b hb)`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem twCent_ratF_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
    (δ * thE E n δ).val.charpoly.Separable →
    ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  intro E _ _ _ n δ hs a ha b hb
  have hθ : ∀ g, thF E n (thF E n g) = g :=
    GlobalTheory.LocTwist.thetaGL_thetaGL n _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y)
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E n δ * thF E n (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [GlobalTheory.MassNorm.thF_ratF, ← map_mul]
    exact h1
  have hc : ∀ g ∈ twCent (thF E n) (ratF E n δ),
      Commute g.val (ratF E n δ * thF E n (ratF E n δ)).val := fun g hg => by
    change g.val * _ = _ * g.val
    rw [← Units.val_mul, ← Units.val_mul, commute_norm _ hθ _ _ hg]
  obtain ⟨p, hp⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc a ha)
  obtain ⟨q, hq⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc b hb)
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]

end GlobalTheory.CompanionTheory.RatCentComm
