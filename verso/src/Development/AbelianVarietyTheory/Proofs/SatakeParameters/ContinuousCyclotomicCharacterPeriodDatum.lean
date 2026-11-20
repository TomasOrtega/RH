import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Introduce `l _ P K LL`. Establish `h` using `(GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1`. Establish `e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) = fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l])`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _`.

Rewrite using `[P.PD_χ]`. Rewrite using `[e]`. Use `Continuous.subtype_mk (f := fun g : ↥(GK K) => algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _` and prove the remaining obligations. Conclude with `(continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)`.
-/
theorem continuous_cycLL_period : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l),
    Continuous (fun s => ((cycLL (P.PD K) ↥LL.1 s : (↥LL.1)ˣ) : ↥LL.1)) := by
  intro l _ P K LL
  have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
  have e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) =
      fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    funext g
    change algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
    rw [P.PD_χ]
  rw [e]
  refine Continuous.subtype_mk (f := fun g : ↥(GK K) =>
    algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _
  exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)

end GlobalTheory.HTW.Rec
