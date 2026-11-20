import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeComplexBaseChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenNearCover
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

/- English proof (translation)
Introduce `K _ ι _ P d hP Q hQ`. Take `⟨hK, ⟨hPp, hPm, hPr⟩, hPh, hdim⟩` from `hP`. Establish `hc : Q.comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P` using `GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.comap_of_minimal P hPh Q hQ`. Establish `hCm : IsMultiHomogIdeal (cxIdeal P)`. Take `⟨T, hT, hPT⟩` from `hPm`.

Use `⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [cxIdeal, hPT, Ideal.map_span]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hT f hf`. Conclude with `⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩`. Establish `hQm : IsMultiHomogIdeal Q` using `GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearCover.isMultiHomogIdeal_of_mem_minimalPrimes hCm hQ`.

Establish `hQr : IsRelevant Q` using `fun k => by`. Take `⟨i, hi⟩` from `hPr k`. Use `⟨i, fun hX => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, Ideal.mem_comap, MvPolynomial.map_X]`. Conclude with `hX`.

Establish `hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0` using `fun m hm => by`. Establish `: m ∈ P.comap (C : ℤ →+* MRing ι)` using `hm`. Rewrite `this` using `[hPh]`. Conclude with `this`. Take `⟨hQp, -, hQdim⟩` from `ReciprocityTheory.AnForm.R.extQ_spec P hP'`.

Establish `hmapP : cxIdeal P = (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ))`. Rewrite using `[cxIdeal, GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.map_int_complex_eq, ← Ideal.map_map]`. Both sides reduce to the same expression. Establish `hQ'` using `hQ`. Rewrite `hQ'` using `[hmapP]`.

Use `⟨⟨hK, ⟨hQ.1.1, hQm, hQr⟩, ?_⟩, hc⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']`. Rewrite `hQdim` using `[hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega]`. Conclude with `GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.dim_cancel_one hQdim`.
-/
theorem isCxVar_of_mem_minimalPrimes_cxIdeal :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P (d + 1) →
    ∀ Q ∈ (cxIdeal P).minimalPrimes, IsCxVar Q d ∧
      Q.comap (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P := by
  classical
  intro K _ ι _ P d hP Q hQ
  obtain ⟨hK, ⟨hPp, hPm, hPr⟩, hPh, hdim⟩ := hP
  have hc : Q.comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P :=
    GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.comap_of_minimal P hPh Q hQ
  have hCm : IsMultiHomogIdeal (cxIdeal P) := by
    obtain ⟨T, hT, hPT⟩ := hPm
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [cxIdeal, hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩
  have hQm : IsMultiHomogIdeal Q :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearCover.isMultiHomogIdeal_of_mem_minimalPrimes hCm hQ
  have hQr : IsRelevant Q := fun k => by
    obtain ⟨i, hi⟩ := hPr k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hc, Ideal.mem_comap, MvPolynomial.map_X]
    exact hX
  have hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [hPh] at this
    exact this
  obtain ⟨hQp, -, hQdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have hmapP : cxIdeal P =
      (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [cxIdeal, GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.map_int_complex_eq, ← Ideal.map_map]
    rfl
  have hQ' := hQ
  rw [hmapP] at hQ'
  refine ⟨⟨hK, ⟨hQ.1.1, hQm, hQr⟩, ?_⟩, hc⟩
  rw [ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']
  rw [hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega] at hQdim
  exact GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.dim_cancel_one hQdim

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
