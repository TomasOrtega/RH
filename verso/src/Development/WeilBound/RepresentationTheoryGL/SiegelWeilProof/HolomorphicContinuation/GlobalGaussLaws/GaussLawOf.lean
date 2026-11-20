import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussP

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

/- English proof (translation)
Introduce `hTI hN hM hV hMul hGZ hLNe D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL`. Take `⟨e, hLev⟩` from `hM D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL`. Use `⟨e, fun y Z hZ => ?_⟩` and prove the remaining obligations. Establish `hc : 0 < cLoc l τ`. Unfold `cLoc`.

Conclude with `mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl τ))`. Establish `hI` using `isSiegel_I (n := n)`. Establish `hGi : IsSch (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1))` using `hGZ V.rank n ε _ _ hc (abs_tLoc l τ) _ hI`. Take `⟨q, hq21, hqZ⟩` from `siegelOrb n Z hZ`. Take `⟨p0, k, hyq, hp0, hk⟩` from `iwaGR n (y * q)`.

Establish `e1` using `pLaw hN hMul hcx hL hLev q hq21 (Complex.I • 1) hGi`. Rewrite `e1` using `[hqZ]`. Use `set p := cnt (epsT (tLoc l τ) ε) true`. Use `set p' := cnt (epsT (tLoc l τ) ε) false`. Establish `hjq : jF e p p' q (Complex.I • 1) ≠ 0`.

Rewrite using `[siegelP_jF q hq21]`. Take `⟨hA, -, -⟩` from `siegelP_data q hq21`. Conclude with `mul_ne_zero (zpow_ne_zero _ hA.ne_zero) (zpow_ne_zero _ (hA.star).ne_zero)`. Establish `hGZeq : gZf ε (tLoc l τ) (cLoc l τ) Z = fun u => (jF e p p' q (Complex.I • 1))⁻¹ * L q (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) u`. Use function extensionality and compare the values at `u`.

Rewrite using `[e1]`. Clear the denominators using the available nonvanishing facts. Establish `hVk` using `hV D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL e hLev k hk`. Simplify using `only [vac] at hVk`. Rewrite using `[hGZeq, locLin hTI hcx hL y _ (hL.1 q _ hGi), ← hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y q _ hGi, hyq, hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL p0 k _ hGi, hVk, locLin hTI hcx hL p0 _ hGi, pLaw hN hMul hcx hL hLev p0 hp0 (Complex.I • 1) hGi]`.

Establish `cy` using `(cocycleZ n e p p' y q (Complex.I • 1) hI).2.2.2`. Establish `cp` using `(cocycleZ n e p p' p0 k (Complex.I • 1) hI).2.2.2`. Rewrite `cy` using `[hqZ]`. Rewrite `cp` using `[actZ_K hk]`. Rewrite `cy` using `[hyq]`.

Establish `hact : actZ p0 (Complex.I • 1) = actZ y Z` using `cp.1.symm.trans cy.1`. Establish `hrel : jF e p p' y Z * jF e p p' q (Complex.I • 1) = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1)` using `cy.2.symm.trans cp.2`. Establish `hjy : jF e p p' y Z = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) * (jF e p p' q (Complex.I • 1))⁻¹`. Rewrite using `[← hrel]`. Clear the denominators using the available nonvanishing facts.

Use function extensionality and compare the values at `u`. Rewrite using `[hact, hjy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussLaw_of : TensInj → LawN → LawM → VacK → LocMul → GZSch → LNe → GaussLaw := by
  intro hTI hN hM hV hMul hGZ hLNe D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨e, hLev⟩ := hM D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  refine ⟨e, fun y Z hZ => ?_⟩
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl τ))
  have hI := isSiegel_I (n := n)
  have hGi : IsSch (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) := hGZ V.rank n ε _ _ hc (abs_tLoc l τ) _ hI
  obtain ⟨q, hq21, hqZ⟩ := siegelOrb n Z hZ
  obtain ⟨p0, k, hyq, hp0, hk⟩ := iwaGR n (y * q)
  have e1 := pLaw hN hMul hcx hL hLev q hq21 (Complex.I • 1) hGi
  rw [hqZ] at e1
  set p := cnt (epsT (tLoc l τ) ε) true
  set p' := cnt (epsT (tLoc l τ) ε) false
  have hjq : jF e p p' q (Complex.I • 1) ≠ 0 := by
    rw [siegelP_jF q hq21]
    obtain ⟨hA, -, -⟩ := siegelP_data q hq21
    exact mul_ne_zero (zpow_ne_zero _ hA.ne_zero) (zpow_ne_zero _ (hA.star).ne_zero)
  have hGZeq : gZf ε (tLoc l τ) (cLoc l τ) Z =
      fun u => (jF e p p' q (Complex.I • 1))⁻¹ * L q (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) u := by
    funext u
    rw [e1]
    field_simp
  have hVk := hV D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL e hLev k hk
  simp only [vac] at hVk
  rw [hGZeq, locLin hTI hcx hL y _ (hL.1 q _ hGi),
    ← hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y q _ hGi, hyq,
    hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL p0 k _ hGi, hVk, locLin hTI hcx hL p0 _ hGi,
    pLaw hN hMul hcx hL hLev p0 hp0 (Complex.I • 1) hGi]
  have cy := (cocycleZ n e p p' y q (Complex.I • 1) hI).2.2.2
  have cp := (cocycleZ n e p p' p0 k (Complex.I • 1) hI).2.2.2
  rw [hqZ] at cy
  rw [actZ_K hk] at cp
  rw [hyq] at cy
  have hact : actZ p0 (Complex.I • 1) = actZ y Z := cp.1.symm.trans cy.1
  have hrel : jF e p p' y Z * jF e p p' q (Complex.I • 1) = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) :=
    cy.2.symm.trans cp.2
  have hjy : jF e p p' y Z = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) * (jF e p p' q (Complex.I • 1))⁻¹ := by
    rw [← hrel]; field_simp
  funext u
  rw [hact, hjy]
  ring

end PositivityTheory.Rg.Sw.Glob
