import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormOpen

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn v c φ f`. Establish `hO` using `normOpen F E σ hσ hp n hn v`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `hM _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν`. Take `⟨ha, hb⟩` from `hM mE mF hE hF h1 h2 γ hγ ν hν`.

Distinguish the cases in `hg : γ ∈ normSet E n v`. Establish `horb : orb mF γ ν ((normSet E n v).indicator f) = orb mF γ ν f`. Unfold `orb`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Conclude with `Set.indicator_of_mem ((hO.2 γ x).2 hg) f`. Rewrite using `[horb]`. Conclude with `⟨ha, hb⟩`. Establish `horb : orb mF γ ν ((normSet E n v).indicator f) = 0`. Establish `hz : (fun x => (normSet E n v).indicator f (x⁻¹ * γ * x)) = fun _ => (0 : ℂ)`.

Use function extensionality and compare the values at `x`. Conclude with `Set.indicator_of_notMem (fun h => hg ((hO.2 γ x).1 h)) f`. Unfold `orb quotInt`. Rewrite using `[hz]`. Simplify using the standard rewrite rules.

Conclude with `⟨fun δ hδ => absurd (normLoc F E σ hσ hp n hn v γ δ hδ) hg, fun _ => horb⟩`. Introduce `hT`. Take `⟨h1, h2⟩ : IsLocallyConstant f ∧ HasCompactSupport f` from `hT`. Conclude with `⟨(LocallyConstant.indicator (⟨f, h1⟩ : LocallyConstant _ ℂ) hO.1).isLocallyConstant, h2.mono fun x hx hx0 => hx (Set.indicator_apply_eq_zero.2 fun _ => hx0)⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.G.matchCut :
    UpperTheory.Gal.InertialTypesAlt.G.MatchCut := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v c φ f
  have hO := normOpen F E σ hσ hp n hn v
  refine ⟨?_, ?_⟩
  · intro hM _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν
    obtain ⟨ha, hb⟩ := hM mE mF hE hF h1 h2 γ hγ ν hν
    by_cases hg : γ ∈ normSet E n v
    · have horb : orb mF γ ν ((normSet E n v).indicator f) = orb mF γ ν f := by
        unfold orb
        congr 1
        funext x
        exact Set.indicator_of_mem ((hO.2 γ x).2 hg) f
      rw [horb]
      exact ⟨ha, hb⟩
    · have horb : orb mF γ ν ((normSet E n v).indicator f) = 0 := by
        have hz : (fun x => (normSet E n v).indicator f (x⁻¹ * γ * x)) = fun _ => (0 : ℂ) := by
          funext x
          exact Set.indicator_of_notMem (fun h => hg ((hO.2 γ x).1 h)) f
        unfold orb quotInt
        rw [hz]
        simp
      exact ⟨fun δ hδ => absurd (normLoc F E σ hσ hp n hn v γ δ hδ) hg, fun _ => horb⟩
  · intro hT
    obtain ⟨h1, h2⟩ : IsLocallyConstant f ∧ HasCompactSupport f := hT
    exact ⟨(LocallyConstant.indicator (⟨f, h1⟩ : LocallyConstant _ ℂ) hO.1).isLocallyConstant,
      h2.mono fun x hx hx0 => hx (Set.indicator_apply_eq_zero.2 fun _ => hx0)⟩
