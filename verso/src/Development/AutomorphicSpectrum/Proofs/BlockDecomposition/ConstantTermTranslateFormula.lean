import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

/- English proof (translation)
Introduce `E _ _ _ a r φ hl _ _ _ μ 𝓕 hμ h𝓕 y g`. Use `haveI := countable_ratN (E := E) (a := a) r`. Establish `hper : ∀ n ∈ ratN E a r, ∀ x, φ.1 (unip (n + x) * g) = φ.1 (unip x * g)`. Introduce and unpack `_ ⟨q, rfl⟩ x`. Rewrite using `[unip_add, mul_assoc]`.

Conclude with `(congrArg (fun u => φ.1 (u * _)) (unip_algebraMap q)).trans (hl _ _)`. Establish `h` using `Formalism.IndefR.Tow.fd_setIntegral_add h𝓕 (f := fun x => φ.1 (unip x * g)) hper y`. Simplify `h` using `only [unip_add, mul_assoc]`.
-/
theorem constTerm_unip_left : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
    ∀ (y : BlockIx a r → Ad E) (g : GA E a),
      ∫ x in 𝓕, φ.1 (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  intro E _ _ _ a r φ hl _ _ _ μ 𝓕 hμ h𝓕 y g
  haveI := countable_ratN (E := E) (a := a) r
  have hper : ∀ n ∈ ratN E a r, ∀ x, φ.1 (unip (n + x) * g) = φ.1 (unip x * g) := by
    rintro _ ⟨q, rfl⟩ x
    rw [unip_add, mul_assoc]
    exact (congrArg (fun u => φ.1 (u * _)) (unip_algebraMap q)).trans (hl _ _)
  have h := Formalism.IndefR.Tow.fd_setIntegral_add h𝓕 (f := fun x => φ.1 (unip x * g)) hper y
  simpa only [unip_add, mul_assoc] using h

end GlobalTheory.CompanionTheory.CTFin
