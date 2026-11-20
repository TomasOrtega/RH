import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

open NumberField IsDedekindDomain in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hpq hgood hA`. Take `⟨hGI, hQH⟩` from `_root_.GlobalTheory.Moduli.jointExistence_and_moduliScheme`. Establish `hne : ∀ l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l')`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab at hQH`. Conclude with `fun l' => hQH E H Dw l' hpq`.

Set `family : (l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l'` to `Function.update (fun l' => Classical.choice (hne l')) l Xo`. Establish `hfam : family l = Xo` using `Function.update_self _ _ _`. Use `⟨fun la => ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `_root_.GlobalTheory.Reg.modelAt_of_good_level hGI E H Dw hpq family l c la (fun p hp _ => hgood p hp)`. Rewrite `h` using `[hfam]`. Then use the resulting hypothesis.

Establish `hGI'` using `hGI`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI at hGI'`. Take `⟨Y, -, hY⟩` from `hGI'.2 E H Dw hpq family`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N6 at hY`. Take `⟨Ygl, -⟩` from `hY l c hgood hA`.

Rewrite `Ygl` using `[hfam]`. Conclude with `⟨Ygl⟩`.
-/
theorem _root_.GlobalTheory.Reg.modelAt_and_nonempty_global_model : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 →
    (∀ la, _root_.GlobalTheory.Reg.ModelAt Xo c la) ∧
      Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) := by
  classical
  intro E _ _ _ H Dw l Xo c hpq hgood hA
  obtain ⟨hGI, hQH⟩ := _root_.GlobalTheory.Moduli.jointExistence_and_moduliScheme
  have hne : ∀ l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l') := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab at hQH
    exact fun l' => hQH E H Dw l' hpq
  let family : (l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l' :=
    Function.update (fun l' => Classical.choice (hne l')) l Xo
  have hfam : family l = Xo := Function.update_self _ _ _
  refine ⟨fun la => ?_, ?_⟩
  · have h := _root_.GlobalTheory.Reg.modelAt_of_good_level hGI E H Dw hpq family l c la
      (fun p hp _ => hgood p hp)
    rwa [hfam] at h
  · have hGI' := hGI
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI at hGI'
    obtain ⟨Y, -, hY⟩ := hGI'.2 E H Dw hpq family
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N6 at hY
    obtain ⟨Ygl, -⟩ := hY l c hgood hA
    rw [hfam] at Ygl
    exact ⟨Ygl⟩

end GlobalTheory.Reg
