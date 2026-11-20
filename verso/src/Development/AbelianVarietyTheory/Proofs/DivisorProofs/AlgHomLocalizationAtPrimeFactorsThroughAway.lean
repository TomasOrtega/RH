import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumDen
open IsLocalRing TensorProduct

namespace GlobalTheory
namespace FactorAway

/- English proof (translation)
Introduce `R A B _ _ _ _ _ _ p _ φ`. Set `φ' : B ⊗[R] A →ₐ[B] Localization.AtPrime p` to `Algebra.TensorProduct.lift (Algebra.ofId B _) φ (fun _ _ => Commute.all _ _)`. Take `⟨g, hg, s, ι, hι⟩` from `SpreadOut.spread_out B (B ⊗[R] A) p φ'`. Use `⟨g, hg, (s.restrictScalars R).comp Algebra.TensorProduct.includeRight, fun a => ?_⟩` and prove the remaining obligations. Establish `hext : (Localization.awayLift (algebraMap B (Localization.AtPrime p)) g (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl))) = (ι : Localization.Away g →+* Localization.AtPrime p)`.

Apply `IsLocalization.ringHom_ext (Submonoid.powers g)` to reduce the goal to its premises. Use extensionality with `b`. Simplify using `[Localization.awayLift]`. Establish `h1` using `congrArg (fun h => h ((1 : B) ⊗ₜ[R] a)) hι`. Simplify using `only [AlgHom.comp_apply, φ', Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h1`.

Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]`. Rewrite using `[hext]`. Conclude with `h1`.
-/
theorem factor_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime]
    (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p)
      (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift
        (algebraMap B (Localization.AtPrime p)) g
        (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  intro R A B _ _ _ _ _ _ p _ φ
  let φ' : B ⊗[R] A →ₐ[B] Localization.AtPrime p :=
    Algebra.TensorProduct.lift (Algebra.ofId B _) φ (fun _ _ => Commute.all _ _)
  obtain ⟨g, hg, s, ι, hι⟩ := SpreadOut.spread_out B (B ⊗[R] A) p φ'
  refine ⟨g, hg, (s.restrictScalars R).comp Algebra.TensorProduct.includeRight, fun a => ?_⟩
  have hext : (Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
      (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl))) =
      (ι : Localization.Away g →+* Localization.AtPrime p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext b
    simp [Localization.awayLift]
  have h1 := congrArg (fun h => h ((1 : B) ⊗ₜ[R] a)) hι
  simp only [AlgHom.comp_apply, φ', Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h1
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
  rw [hext]
  exact h1

end FactorAway
end GlobalTheory
