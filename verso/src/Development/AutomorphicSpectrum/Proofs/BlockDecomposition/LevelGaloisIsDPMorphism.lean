import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsDPMorphismOfCompat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatSigDP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

/- English proof (translation)
Take `⟨u, hu⟩` from `GlobalTheory.CompanionTheory.TwFil.exists_gal_xi (toBot g.1)`. Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `e : galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)) = wittToBDeRhamPlus (normInteger ℂ_[l]) l (u * xi0 l)`. Rewrite using `[← hu, ← gal_smul_wittToBDeRhamPlus]`. Both sides reduce to the same expression.

Use `show Ideal.Quotient.mk _ (galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l))) = _`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem exists_gB_xi (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    ∃ u : Ainf l, gB h k g (fk l k (xi0 l)) = fk l k (u * xi0 l) := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.TwFil.exists_gal_xi (toBot g.1)
  refine ⟨u, ?_⟩
  have e : galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (u * xi0 l) := by
    rw [← hu, ← gal_smul_wittToBDeRhamPlus]
    rfl
  show Ideal.Quotient.mk _ (galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l))) = _
  rw [e]
  rfl

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_gB_xi h k g`. Conclude with `GlobalTheory.CompanionTheory.LatDP.isDPMorphism_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) u hu (h.hc k) (h.hc k)`.
-/
theorem sigA_isDPMorphism (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  obtain ⟨u, hu⟩ := exists_gB_xi h k g
  exact GlobalTheory.CompanionTheory.LatDP.isDPMorphism_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) u hu
    (h.hc k) (h.hc k)

end GlobalTheory.CompanionTheory.LatSigDP
