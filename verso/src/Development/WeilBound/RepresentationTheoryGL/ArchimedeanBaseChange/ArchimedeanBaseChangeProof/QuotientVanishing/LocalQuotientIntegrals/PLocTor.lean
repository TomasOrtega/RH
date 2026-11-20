import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBasisDiagonalTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable

noncomputable section

open Matrix PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.LocalTorus

/- English proof (translation)
Establish `hθθ : ∀ g : GL (Fin n) ℂ, thC n (thC n g) = g`. Introduce `g`. Apply `Units.ext` to reduce the goal to its premises. Use `show ((((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = (g : Matrix (Fin n) (Fin n) ℂ)`. Establish `e : (((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ` using `rfl`.

Rewrite using `[e]`. Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.transpose_apply]`. Establish `key : ∀ x ∈ twCent (thC n) d, Commute ((d * thC n d : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ)`. Introduce `x hx`.

Establish `h1 : x⁻¹ * d * thC n x = d` using `hx`. Establish `h2 : d * thC n x = x * d`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : thC n d * x = thC n x * thC n d`. Establish `h4` using `congrArg (thC n) h2`.

Rewrite `h4` using `[map_mul, map_mul, hθθ]`. Conclude with `h4`. Apply `Commute.units_val` to reduce the goal to its premises. Use `show (d * thC n d) * x = x * (d * thC n d)`. Rewrite using `[mul_assoc, h3, ← mul_assoc, h2, mul_assoc]`.

Establish `hc` using `GlobalTheory.BCT.CentComm.commute_of_commute_separable hs (key s hs') (key t ht)`. Conclude with `Units.ext (by simpa using hc.eq)`.
-/
theorem comm (n : ℕ) (d : GL (Fin n) ℂ) (hs : (d * thC n d).val.charpoly.Separable)
    (s : GL (Fin n) ℂ) (hs' : s ∈ twCent (thC n) d) (t : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    s * t = t * s := by
  have hθθ : ∀ g : GL (Fin n) ℂ, thC n (thC n g) = g := by
    intro g
    apply Units.ext
    show ((((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = (g : Matrix (Fin n) (Fin n) ℂ)
    have e : (((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ := rfl
    rw [e]
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply]
  have key : ∀ x ∈ twCent (thC n) d,
      Commute ((d * thC n d : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ) := by
    intro x hx
    have h1 : x⁻¹ * d * thC n x = d := hx
    have h2 : d * thC n x = x * d := by
      calc d * thC n x = x * (x⁻¹ * d * thC n x) := by group
        _ = x * d := by rw [h1]
    have h3 : thC n d * x = thC n x * thC n d := by
      have h4 := congrArg (thC n) h2
      rw [map_mul, map_mul, hθθ] at h4
      exact h4
    apply Commute.units_val
    show (d * thC n d) * x = x * (d * thC n d)
    rw [mul_assoc, h3, ← mul_assoc, h2, mul_assoc]
  have hc := GlobalTheory.BCT.CentComm.commute_of_commute_separable hs (key s hs') (key t ht)
  exact Units.ext (by simpa using hc.eq)

end PositivityTheory.Rg.BcB.CV.LocalTorus

/- English proof (translation)
Introduce `n d hs`. Conclude with `⟨GlobalTheory.CompanionTheory.LocVan.isClosed_twCent d, PositivityTheory.Rg.BcB.CV.LocalTorus.comm n d hs, GlobalTheory.CompanionTheory.LocVan.continuous_thC, GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n, GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n⟩`.
-/
theorem PositivityTheory.Rg.BcB.CV.pf_LocTor : PositivityTheory.Rg.BcB.CV.LocTor := by
  intro n d hs
  exact ⟨GlobalTheory.CompanionTheory.LocVan.isClosed_twCent d, PositivityTheory.Rg.BcB.CV.LocalTorus.comm n d hs,
    GlobalTheory.CompanionTheory.LocVan.continuous_thC, GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n, GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n⟩

end
