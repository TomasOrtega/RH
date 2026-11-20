import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sigmaB_fixes_K {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : ∀ g (a : K),
    (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  intro g a
  have key : gP l g (kP l K a) = kP l K a := by
    have h1 : galBdRHom (toBot g.1) (algClToBdR l (a : PadicAlgCl l))
        = algClToBdR l ((toBot g.1) (a : PadicAlgCl l)) :=
      gal_smul_algClToBdR (toBot g.1) (a : PadicAlgCl l)
    have h2 : (toBot g.1) (a : PadicAlgCl l) = (a : PadicAlgCl l) := g.2 a
    rw [h2] at h1
    exact h1
  change gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  change Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = Ideal.Quotient.mk _ (kP l K a)
  rw [Ideal.quotientMap_mk, key]

end GlobalTheory.CompanionTheory.LatC
