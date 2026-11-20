import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocModel

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v Y _ Xm hXm ρ hρ Γ _ j ω hω actY hact g x`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest (F := F) (Fin a × Fin (a + a')) v`. Establish `hS` using `IsUWeilPair.isUSplitting hT.weil`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `φ`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ φ.2).1` to reduce the goal to its premises. Simplify using `only [Module.End.mul_apply]`. Establish `h1` using `(hω g (ρ x φ) _).2 rfl R (hR _ (ρ x φ).2)`. Establish `h2` using `hρ x φ R (hR _ φ.2)`.

Establish `h3` using `(hω g φ _).2 rfl R (hR _ φ.2)`. Establish `h4` using `hρ (actY g x) (ω g φ) R (hR _ (ω g φ).2)`. Establish `h5` using `hS.impl (j g) (Xm x) (tens (evFin F v) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) R) (hR _ φ.2).2`. Rewrite using `[← h1, ← h4, ← h2, h5, hact, h3]`.
-/
theorem weil_normalises_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (AE F E)),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v Y _ Xm hXm ρ hρ Γ _ j ω hω actY hact g x
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a × Fin (a + a')) v
  have hS := IsUWeilPair.isUSplitting hT.weil
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ φ.2).1
  simp only [Module.End.mul_apply]
  have h1 := (hω g (ρ x φ) _).2 rfl R (hR _ (ρ x φ).2)
  have h2 := hρ x φ R (hR _ φ.2)
  have h3 := (hω g φ _).2 rfl R (hR _ φ.2)
  have h4 := hρ (actY g x) (ω g φ) R (hR _ (ω g φ).2)
  have h5 := hS.impl (j g) (Xm x) (tens (evFin F v) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) R) (hR _ φ.2).2
  rw [← h1, ← h4, ← h2, h5, hact, h3]

end GlobalTheory.InertLocModel
