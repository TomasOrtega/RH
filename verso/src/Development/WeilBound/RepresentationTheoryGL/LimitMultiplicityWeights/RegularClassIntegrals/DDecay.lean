import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

namespace DDecay

/- English proof (translation)
Establish `hS : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)) = rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) : Set (GF V))`. Rewrite using `[← Subgroup.coe_map, map_unipRat, hB]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tsum_eq (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r)
    (hB : NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j))
    (g : GA D V → ℂ) :
    ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν) =
      ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := by
  have hS : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)) =
      rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) : Set (GF V)) := by
    rw [← Subgroup.coe_map, map_unipRat, hB]; rfl
  calc ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν)
      = ∑' b : (rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) :
          Set (GF V))), g b := (tsum_image g (ratEmb_injective _ _).injOn).symm
    _ = ∑' c : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)),
          g (Equiv.setCongr hS c) := (Equiv.tsum_eq (Equiv.setCongr hS) (fun b => g b)).symm
    _ = ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := rfl

end DDecay

/- English proof (translation)
Introduce `hCore hBridge D V r X Y hW c hc j f hf hU C W hC hW'`. Take `⟨A, hA⟩` from `hCore D V r X Y hW c hc j`. Establish `hB` using `hBridge D V r X Y hW j`. Establish `hV : Van (unipRad D.sp.cm.sig V.gram (pre X j)) f`. Establish `h0 : Van (NA (frameFlag (isIsoFrame_firstCols hW j))) f` using `fun ν _ x y => (hU ν x y).2`.

Rewrite `h0` using `[hB]`. Conclude with `h0`. Use `⟨A, fun m => ?_⟩` and prove the remaining obligations. Take `⟨B, hBd⟩` from `hA m f hf hV C W hC hW'`. Use `⟨B, fun t ht a ha x hx y hy => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hBd t ht a ha x hx y hy`. Establish `h2 : ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, f (x * (a⁻¹ * rat V ν * a) * y) = nsum (NF D.sp.cm.sig V.gram (pre X j)) f (x * a⁻¹) (a * y)`. Rewrite using `[nsum, ← DDecay.tsum_eq D V r X Y hW j hB (fun g => f (x * a⁻¹ * g * (a * y)))]`. Use `congr 1`. Use function extensionality and compare the values at `ν`.

Use `congr 1`. Use `group`. Rewrite using `[h2]`. Conclude with `h1`.
-/
theorem decay : Core → Bridge → Decay := by
  intro hCore hBridge D V r X Y hW c hc j f hf hU C W hC hW'
  obtain ⟨A, hA⟩ := hCore D V r X Y hW c hc j
  have hB := hBridge D V r X Y hW j
  have hV : Van (unipRad D.sp.cm.sig V.gram (pre X j)) f := by
    have h0 : Van (NA (frameFlag (isIsoFrame_firstCols hW j))) f := fun ν _ x y => (hU ν x y).2
    rw [hB] at h0
    exact h0
  refine ⟨A, fun m => ?_⟩
  obtain ⟨B, hBd⟩ := hA m f hf hV C W hC hW'
  refine ⟨B, fun t ht a ha x hx y hy => ?_⟩
  have h1 := hBd t ht a ha x hx y hy
  have h2 : ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
      f (x * (a⁻¹ * rat V ν * a) * y) = nsum (NF D.sp.cm.sig V.gram (pre X j)) f (x * a⁻¹) (a * y) := by
    rw [nsum, ← DDecay.tsum_eq D V r X Y hW j hB (fun g => f (x * a⁻¹ * g * (a * y)))]
    congr 1; funext ν; congr 1; group
  rw [h2]
  exact h1

end MainStatements.WeightKernel.Dec
