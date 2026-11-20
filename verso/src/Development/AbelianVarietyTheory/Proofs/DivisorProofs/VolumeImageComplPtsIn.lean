import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt

namespace GlobalTheory.Mean4O.CoverInt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem volume_image_compl_ptsIn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → (∀ W : X.Opens, Nonempty W → Function.Injective (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W)) → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (D : ℕ) (c : AlgChart p σ D), MeasureTheory.volume (c.e '' (c.e.source ∩ (ptsIn p σ U)ᶜ)) = 0 := by
  intro k _ X _ p σ hσ _ U hU D c
  have : IsDomain k := hσ.isDomain σ
  refine measure_mono_null ?_ (ae_iff.1 (SemiPosBir.ae_mem hσ c (U := U) ⟨_, hU⟩))
  rintro _ ⟨z, hz, rfl⟩ h
  have h₁ := h (c.e.map_source hz.1)
  rw [c.e.left_inv hz.1] at h₁
  exact hz.2 h₁

end GlobalTheory.Mean4O.CoverInt
