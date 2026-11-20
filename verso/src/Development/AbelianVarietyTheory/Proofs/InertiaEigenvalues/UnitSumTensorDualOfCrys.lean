import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveIffGram
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineQuotientTensorDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitForOfTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart

noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (LocQuotCrys LocTensorCrys LocDualCrys)

set_option synthInstance.maxHeartbeats 400000

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hC : IsAlgClosed (Cb l)` using `(GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1`. Establish `hf : Function.Surjective (frobenius (Cb l) l)` using `by first`. Consider the case `exact surjective_frobenius (Cb l) l`. Consider the case `exact (bijective_frobenius (Cb l) l).2`. Consider the case `exact fun y => ⟨(frobeniusEquiv (Cb l) l).symm y, by simp⟩`.

Introduce `y`. Take `⟨x, hx⟩` from `WittVector.map_surjective (p := l) _ hf y`. Unfold `frobW`. Conclude with `⟨x, hx⟩`.
-/
private theorem frobW_surjective_lemma : Function.Surjective (frobW l) := by
  have hC : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have hf : Function.Surjective (frobenius (Cb l) l) := by
    first
      | exact surjective_frobenius (Cb l) l
      | exact (bijective_frobenius (Cb l) l).2
      | exact fun y => ⟨(frobeniusEquiv (Cb l) l).symm y, by simp⟩
  intro y
  obtain ⟨x, hx⟩ := WittVector.map_surjective (p := l) _ hf y
  unfold frobW
  exact ⟨x, hx⟩

/- English proof (translation)
Establish `hg : Function.Surjective (frobW l).toLinearMap` using `frobW_surjective_lemma`. Introduce `y`. Take `⟨x, rfl⟩` from `LinearMap.lTensor_surjective (↥(OL LL)) hg y`. Use `⟨x, ?_⟩` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [φRW]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem φRW_surjective (LL : FinExt l) : Function.Surjective (φRW LL) := by
  have hg : Function.Surjective (frobW l).toLinearMap := frobW_surjective_lemma
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (↥(OL LL)) hg y
  refine ⟨x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φRW]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Establish `: FiniteDimensional ℚ_[l] LL.1` using `LL.2`. Unfold `OL`. Conclude with `integralClosure.isFractionRing_of_finite_extension ℚ_[l] _`.
-/
theorem isFractionRing_OL (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 := by
  have : FiniteDimensional ℚ_[l] LL.1 := LL.2
  unfold OL
  exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] _

/- English proof (translation)
Establish `: Module.Finite ℤ_[l] ↥(OL LL)` using `GlobalTheory.EtaleExact.finite_OL LL`. Establish `: IsNoetherianRing ↥(OL LL)` using `by first`. Consider the case `infer_instance`. Consider the case `exact isNoetherian_of_tower ℤ_[l] inferInstance`. Use `GlobalTheory.EtaleExact.map_ne_top_of_tie E.tie (fun c => ?_) (fun x hx => ?_) m hm` and prove the remaining obligations.

Rewrite using `[P.PD_p K]`. Conclude with `GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL c`. Conclude with `GlobalTheory.EtaleExact.sep_RW LL x (by simpa [P.PD_p K] using hx)`.
-/
theorem map_ne_top {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (m : Ideal W.EE) (hm : m.IsMaximal) :
    m.map E.tie.ioE.toRingHom ≠ ⊤ := by
  have : Module.Finite ℤ_[l] ↥(OL LL) := GlobalTheory.EtaleExact.finite_OL LL
  have : IsNoetherianRing ↥(OL LL) := by
    first
      | infer_instance
      | exact isNoetherian_of_tower ℤ_[l] inferInstance
  refine GlobalTheory.EtaleExact.map_ne_top_of_tie E.tie (fun c => ?_) (fun x hx => ?_) m hm
  · rw [P.PD_p K]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL c
  · exact GlobalTheory.EtaleExact.sep_RW LL x (by simpa [P.PD_p K] using hx)

/- English proof (translation)
Introduce `ι _ M w hg hw i`. Conclude with `GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed l P AI K s LL h W E ι M 0 w hg (fun i => by simpa using hw i) i`.
-/
theorem descends {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) : Descends E.tie := by
  intro ι _ M w hg hw i
  exact GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed l P AI K s LL h W E ι M 0 w hg (fun i => by simpa using hw i) i

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocQuotCrys GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocTensorCrys GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocDualCrys GlobalTheory.IndefiniteRowSideFullH …`. Establish `: ∀ LL : FinExt l, IsFractionRing ↥(OL LL) ↥LL.1` using `isFractionRing_OL`. Use `⟨GlobalTheory.WachUnit.unitPart l P AI H F, GlobalTheory.WachSum.sumPart l P H, fun K s LL h => ?_, fun K s LL h => ?_⟩` and prove the remaining obligations. Use `this LL` as an intermediate fact. Conclude with `tensorFor (F.E K s LL h).tie (fun m hm => map_ne_top (F.E K s LL h) m hm) (φRW_surjective LL) (descends (F.E K s LL h)) (hq K LL) (ht K LL) (hU K s LL h) (hF K s LL h)`.

Use `this LL` as an intermediate fact. Conclude with `dualFor (F.E K s LL h).tie (fun m hm => map_ne_top (F.E K s LL h) m hm) (φRW_surjective LL) (descends (F.E K s LL h)) (hq K LL) (hd K LL) (hU K s LL h) (hF K s LL h)`.
-/
theorem unitSumTensorDual_of_crys (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (hq : LocQuotCrys l P) (ht : LocTensorCrys l P)
    (hd : LocDualCrys l P) (hU : GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse.WachUnique l P H)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.WachLettersFree l P H) : UnitSumTensorDual l P AI H F := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocQuotCrys GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocTensorCrys GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocDualCrys
    GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse.WachUnique at *
  have : ∀ LL : FinExt l, IsFractionRing ↥(OL LL) ↥LL.1 := isFractionRing_OL
  refine ⟨GlobalTheory.WachUnit.unitPart l P AI H F, GlobalTheory.WachSum.sumPart l P H, fun K s LL h => ?_,
    fun K s LL h => ?_⟩
  · have := this LL
    exact tensorFor (F.E K s LL h).tie (fun m hm => map_ne_top (F.E K s LL h) m hm)
      (φRW_surjective LL) (descends (F.E K s LL h)) (hq K LL) (ht K LL) (hU K s LL h) (hF K s LL h)
  · have := this LL
    exact dualFor (F.E K s LL h).tie (fun m hm => map_ne_top (F.E K s LL h) m hm) (φRW_surjective LL)
      (descends (F.E K s LL h)) (hq K LL) (hd K LL) (hU K s LL h) (hF K s LL h)

/- English proof (translation)
Take `⟨hq, ht, hd⟩` from `GlobalTheory.T.crystalline_quotient_tensor_dual l P AI hS`. Conclude with `unitSumTensorDual_of_crys l P AI H F hq ht hd hU hF`.
-/
theorem unitSumTensorDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (hS : GlobalTheory.Per.IsStd P AI)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse.WachUnique l P H) (hF : GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.WachLettersFree l P H) :
    UnitSumTensorDual l P AI H F := by
  obtain ⟨hq, ht, hd⟩ := GlobalTheory.T.crystalline_quotient_tensor_dual l P AI hS
  exact unitSumTensorDual_of_crys l P AI H F hq ht hd hU hF

end GlobalTheory.WachTensor
