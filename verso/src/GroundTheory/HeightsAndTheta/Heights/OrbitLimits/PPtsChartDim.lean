import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar)

/- English proof (translation)
Introduce `K _ ι _ P e i hP J hJ`. Use `set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ`. Establish `hvar` using `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP`. Establish `: PQ.IsPrime` using `hvar.1.isPrime`. Use `set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC`.

Establish `hext : ReciprocityTheory.AnForm.R.extC PQ = PC`. Rewrite using `[ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]`. Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_C]`.

Use `congr 1`. Simplify using the standard rewrite rules. Establish `hdim : ∀ Q ∈ PC.minimalPrimes, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)`. Introduce `Q hQ`. Rewrite `hQ` using `[← hext]`.

Rewrite using `[ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]`. Conclude with `hvar.2`. Establish `hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC`. Take `⟨S, hS, hPS⟩` from `hP.2.1.2.1`. Use `⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩`. Set `g : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ` to `(rename (PtsSegreChart.coordEquiv (ι := ι))).toRingHom`. Set `f : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →+* MvPolynomial (Σ k, ι k) ℂ` to `(rename (PtsSegreChart.coordEquiv (ι := ι)).symm).toRingHom`.

Establish `hfg : ∀ b, f (g b) = b` using `fun b => by simp [f, g, rename_rename]`. Establish `hgf : ∀ a, g (f a) = a` using `fun a => by simp [f, g, rename_rename]`. Establish `hI : PtsSegreChart.ideal P i = (ReciprocityTheory.AnForm.R.chartIdeal PC i).map g`. Rewrite using `[PtsSegreChart.ideal, ReciprocityTheory.AnForm.R.chartIdeal, Ideal.map_sup, Ideal.map_span, hPC, Ideal.map_map, ← Set.range_comp]`. Use `congr 3`.

Use function extensionality and compare the values at `k`. Simplify using `[g]`. Take `⟨hmin, hd⟩` from `SegreChartDim.minimalPrimes_transfer f g (PtsSegreChart.ideal P i) (ReciprocityTheory.AnForm.R.chartIdeal PC i) (by`. Rewrite using `[hI, Ideal.map_le_iff_le_comap]`. Introduce `b hb`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hfg]`. Conclude with `hb)`. Use the proof step `(by rw [hI]; exact Ideal.le_comap_map)`. Use the proof step `(fun a => by rw [hgf, sub_self]; exact Ideal.zero_mem _)`. Use the proof step `(fun b => by rw [hfg, sub_self]; exact Ideal.zero_mem _) J hJ`.

Rewrite using `[hd]`. Conclude with `SegreChartDim.ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin`.
-/
theorem PtsChartDim.proof : PtsChartDim.Statement := by
  classical
  intro K _ ι _ P e i hP J hJ

  set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
  have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  have : PQ.IsPrime := hvar.1.isPrime
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
    rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      congr 1
    · simp
  have hdim : ∀ Q ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hext] at hQ
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]
    exact hvar.2
  have hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩

  let g : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
    (rename (PtsSegreChart.coordEquiv (ι := ι))).toRingHom
  let f : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →+* MvPolynomial (Σ k, ι k) ℂ :=
    (rename (PtsSegreChart.coordEquiv (ι := ι)).symm).toRingHom
  have hfg : ∀ b, f (g b) = b := fun b => by simp [f, g, rename_rename]
  have hgf : ∀ a, g (f a) = a := fun a => by simp [f, g, rename_rename]
  have hI : PtsSegreChart.ideal P i = (ReciprocityTheory.AnForm.R.chartIdeal PC i).map g := by
    rw [PtsSegreChart.ideal, ReciprocityTheory.AnForm.R.chartIdeal, Ideal.map_sup, Ideal.map_span, hPC, Ideal.map_map,
      ← Set.range_comp]
    congr 3
    funext k
    simp [g]
  obtain ⟨hmin, hd⟩ := SegreChartDim.minimalPrimes_transfer f g (PtsSegreChart.ideal P i)
    (ReciprocityTheory.AnForm.R.chartIdeal PC i)
    (by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_comap, hfg]
      exact hb)
    (by rw [hI]; exact Ideal.le_comap_map)
    (fun a => by rw [hgf, sub_self]; exact Ideal.zero_mem _)
    (fun b => by rw [hfg, sub_self]; exact Ideal.zero_mem _) J hJ
  rw [hd]
  exact SegreChartDim.ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin

end GroundTheory.Heights₂.Heights
