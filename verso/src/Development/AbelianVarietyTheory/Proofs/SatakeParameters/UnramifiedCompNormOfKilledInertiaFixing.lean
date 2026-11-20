import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

/- English proof (translation)
Introduce `Ω _ E _ _ _ _ M _ _ _ _ _ _ A w u h h' _ n ξ a ha H j x hx`. Take `⟨a', ha'⟩` from `GlobalTheory.localArtinExists_holds M Ω A u h'`. Establish `h1 : ValuativeRel.valuation (u.adicCompletion M) (x : u.adicCompletion M) = 1`. Establish `: (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Conclude with `(ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion M)) (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.2 hx`.

Take `⟨τ, rfl⟩` from `ha'.surj x`. Establish `hdeg : deg τ = 0`. Use `ha'.ord_eq τ` as an intermediate fact. Rewrite `this` using `[GlobalTheory.SmGL.ord_eq_zero_iff.2 h1]`. Use linear arithmetic over natural numbers and integers.

Take `⟨t, ht, hd⟩` from `GlobalTheory.AboveL.exists_weil_restrict E M Ω A w u h h' τ`. Rewrite using `[← GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' t τ ht]`. Conclude with `H t (hd.2 hdeg) (fun y => by rw [ht]; exact AlgEquiv.commutes _ y) j`.
-/
theorem unram_comp_normU_of_fix : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  intro Ω _ E _ _ _ _ M _ _ _ _ _ _ A w u h h' _ n ξ a ha H j x hx
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  have h1 : ValuativeRel.valuation (u.adicCompletion M) (x : u.adicCompletion M) = 1 := by
    have : (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion M))
      (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.2 hx
  obtain ⟨τ, rfl⟩ := ha'.surj x
  have hdeg : deg τ = 0 := by
    have := ha'.ord_eq τ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at this
    omega
  obtain ⟨t, ht, hd⟩ := GlobalTheory.AboveL.exists_weil_restrict E M Ω A w u h h' τ
  rw [← GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' t τ ht]
  exact H t (hd.2 hdeg) (fun y => by rw [ht]; exact AlgEquiv.commutes _ y) j

end GlobalTheory.RoadU
