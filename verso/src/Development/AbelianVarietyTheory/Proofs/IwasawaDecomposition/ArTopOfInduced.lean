import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUniqueStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

/- English proof (translation)
Introduce `hc hd F _ _ C Y A M L k cf hI`. Use `M.ar.isIntegral` as an intermediate fact. Take `⟨h, hh⟩` from `(hc.1 _ M.X M.p Y.dim M.ar).1 L`. Establish `hex : ∃ t, A.IsArTop t` using `⟨_, M, L, k, cf, _, hI, ⟨h, hh, rfl⟩, rfl⟩`. Establish `htop : A.IsArTop A.arTop`.

Unfold `Adl.arTop`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Conclude with `⟨htop, fun a ha => GlobalTheory.T.arakelov_top_unique hc hd F C Y A _ _ htop ⟨M, L, k, cf, a, hI, ha, rfl⟩⟩`.
-/
theorem arTop_of_induced : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.IsArTop A.arTop ∧ ∀ a : ℝ, (haveI := M.ar.isIntegral; L.IsSelfInter a) → A.arTop = (a / (((k : ℕ) : ℝ) * (A.n : ℕ)) ^ (Y.dim + 1) + ((Y.dim : ℝ) + 1) * A.deg * ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ) := by
  intro hc hd F _ _ C Y A M L k cf hI
  have := M.ar.isIntegral
  obtain ⟨h, hh⟩ := (hc.1 _ M.X M.p Y.dim M.ar).1 L
  have hex : ∃ t, A.IsArTop t := ⟨_, M, L, k, cf, _, hI, ⟨h, hh, rfl⟩, rfl⟩
  have htop : A.IsArTop A.arTop := by
    unfold Adl.arTop
    rw [dif_pos hex]
    exact hex.choose_spec
  exact ⟨htop, fun a ha => GlobalTheory.T.arakelov_top_unique hc hd F C Y A _ _ htop ⟨M, L, k, cf, a, hI, ha, rfl⟩⟩

end GlobalTheory.TrueGeo
