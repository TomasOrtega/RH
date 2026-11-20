import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Introduce `hKl _ _ II hII K _ ι _ W e L hW hL hnef`. Establish `hK : Nonempty K` using `hW.1`. Establish `hDG` using `GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system ⟨II, hII⟩)`. Establish `hI` using `GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι`. Establish `hQ` using `GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW`.

Establish `key` using `hKl ℚ K ι _ _ e (fun j => (L j).a) hI hQ (by`. Introduce `j V hV hle`. Take `⟨hVar, hVmap⟩` from `GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.isArithVar_comap_of_isProjVarF hV`. Establish `h0` using `hnef j _ hVar (Ideal.map_le_iff_le_comap.mp hle)`. Establish `hd` using `hDG K ι _ 1 (fun _ => L j) hVar (fun _ => hL j)`.

Rewrite `hd` using `[hVmap]`. Establish `h1 : (0 : ℝ) ≤ (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V (fun _ : Fin 1 => (L j).a) : ℤ)`. Rewrite using `[← hd]`. Conclude with `h0`. Establish `h2 : (fun _ : Fin 1 => (L j).a) = ![(L j).a]`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Conclude with `h1)` after adjusting the coercions.

Establish `hd` using `hDG K ι W e L hW hL`. Use `show 0 ≤ ptsIntegral W (pot L) (fun _ => 1)`. Rewrite using `[hd]`. Conclude with `key` after adjusting the coercions.
-/
theorem RootFieldNumerics.arithmetic_intersection_divisor_support : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι), IsArithVar W (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  intro hKl _ _ II hII K _ ι _ W e L hW hL hnef
  classical
  have hK : Nonempty K := hW.1
  have hDG := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system ⟨II, hII⟩)
  have hI := GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hQ := GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW
  have key := hKl ℚ K ι _ _ e (fun j => (L j).a) hI hQ (by
    intro j V hV hle
    obtain ⟨hVar, hVmap⟩ :=
      GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.isArithVar_comap_of_isProjVarF hV
    have h0 := hnef j _ hVar (Ideal.map_le_iff_le_comap.mp hle)
    have hd := hDG K ι _ 1 (fun _ => L j) hVar (fun _ => hL j)
    rw [hVmap] at hd
    have h1 : (0 : ℝ) ≤ (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V (fun _ : Fin 1 => (L j).a) : ℤ) := by
      rw [← hd]; exact h0
    have h2 : (fun _ : Fin 1 => (L j).a) = ![(L j).a] := by
      funext i; fin_cases i; rfl
    rw [h2] at h1
    exact_mod_cast h1)
  have hd := hDG K ι W e L hW hL
  show 0 ≤ ptsIntegral W (pot L) (fun _ => 1)
  rw [hd]
  exact_mod_cast key
