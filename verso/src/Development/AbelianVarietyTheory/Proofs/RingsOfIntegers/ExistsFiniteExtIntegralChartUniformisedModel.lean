import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformizedStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntChartFrTruncExists

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hstar T io y hT`. Take `⟨T', io', y', e, hA, he, hU, φ, hv, hφ⟩` from `GlobalTheory.T.exists_extension_all_models_uniformized E H Dw l Xo c T io y hT`. Take `⟨iT, hiT⟩ : ∃ iT : T.Fr →+* T'.Fr, (letI` from `io.toAlgebra; letI := io'.toAlgebra; φ.toRingHom) = iT := ⟨_, rfl⟩`. Establish `hio : io' = iT.comp io`. Substitute `hiT` using the available equality.

Use `letI := io.toAlgebra`. Use `letI := io'.toAlgebra`. Conclude with `RingHom.ext fun a => (φ.commutes a).symm`. Establish `hv' : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a`. Introduce `a`.

Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using `[vV]`. Rewrite using `[← hiT]`. Conclude with `hv a ha`.

Substitute `hio` using the available equality. Take `⟨C', hC'⟩` from `GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T' (iT.comp io) y'`. Conclude with `⟨T', iT, e, y', C', ⟨he, hv', φ, hiT, hφ⟩, hA, hC', hU C'.I⟩`.
-/
theorem GlobalTheory.PlaceInt.exists_ext_intChart_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y hT
  obtain ⟨T', io', y', e, hA, he, hU, φ, hv, hφ⟩ := GlobalTheory.T.exists_extension_all_models_uniformized E H Dw l Xo c T io y hT
  obtain ⟨iT, hiT⟩ : ∃ iT : T.Fr →+* T'.Fr,
      (letI := io.toAlgebra; letI := io'.toAlgebra; φ.toRingHom) = iT := ⟨_, rfl⟩
  have hio : io' = iT.comp io := by
    subst hiT
    letI := io.toAlgebra
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (φ.commutes a).symm
  have hv' : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp [vV]
    · rw [← hiT]
      exact hv a ha
  subst hio
  obtain ⟨C', hC'⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T' (iT.comp io) y'
  exact ⟨T', iT, e, y', C', ⟨he, hv', φ, hiT, hφ⟩, hA, hC', hU C'.I⟩
