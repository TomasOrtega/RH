import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismFamilyDirectSummandCancellationStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WD

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a b c`. Proceed by induction on `a using ind with`. Consider the case `hP n a`. Proceed by induction on `b using ind with`. Consider the case `hP m b`.

Proceed by induction on `c using ind with`. Consider the case `hP k c`. Introduce `hab`. Rewrite `hab` using `[lpSum_mk, lpSum_mk, mk_eq_mk]`. Take `⟨e, h1, h2⟩` from `hab`.

Set `fa : Option (Weil h) → Module.End ℂ (Fin n → ℂ)` to `fun o => o.elim a.N a.ρ`. Set `fb : Option (Weil h) → Module.End ℂ (Fin m → ℂ)` to `fun o => o.elim b.N b.ρ`. Set `fc : Option (Weil h) → Module.End ℂ (Fin k → ℂ)` to `fun o => o.elim c.N c.ρ`. Take `⟨e', he'⟩` from `GlobalTheory.T.endomorphismFamily_direct_summand_cancellation ℂ (Option (Weil h)) (Fin n → ℂ) (Fin m → ℂ) (Fin k → ℂ) fa fb fc ⟨e, fun i x => by`. Consider the cases of `i with`.

Consider the case `none => exact h2 x`. Consider the case `some σ => exact h1 σ x⟩`. Conclude with `sound ⟨e', fun σ v => he' (some σ) v, fun v => he' none v⟩`.
-/
theorem lpSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  intro hab
  rw [lpSum_mk, lpSum_mk, mk_eq_mk] at hab
  obtain ⟨e, h1, h2⟩ := hab
  let fa : Option (Weil h) → Module.End ℂ (Fin n → ℂ) := fun o => o.elim a.N a.ρ
  let fb : Option (Weil h) → Module.End ℂ (Fin m → ℂ) := fun o => o.elim b.N b.ρ
  let fc : Option (Weil h) → Module.End ℂ (Fin k → ℂ) := fun o => o.elim c.N c.ρ
  obtain ⟨e', he'⟩ := GlobalTheory.T.endomorphismFamily_direct_summand_cancellation ℂ (Option (Weil h)) (Fin n → ℂ) (Fin m → ℂ) (Fin k → ℂ)
    fa fb fc ⟨e, fun i x => by
      cases i with
      | none => exact h2 x
      | some σ => exact h1 σ x⟩
  exact sound ⟨e', fun σ v => he' (some σ) v, fun v => he' none v⟩

end GlobalTheory.WeilDeligne.WD
