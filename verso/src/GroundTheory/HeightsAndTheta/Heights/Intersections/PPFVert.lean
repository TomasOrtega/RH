import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ProjectionFormulaVertical

open PointVertical

/- English proof (translation)
Use `set p := charOf W with hpdef`. Establish `: Fact p.Prime` using `⟨hpr⟩`. Establish `hpW : ((p : ℕ) : MRing ι') ∈ W` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W`. Establish `hWp : IsProjVarF (W.map (red p)) (d + r)` using `⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩`. Establish `hImm : IsMultiProjPrime (imageZ v W)` using `isMultiProjPrime_imageZ hv hWm`.

Establish `hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W` using `by show rename v ((p : ℕ) : MRing ι) ∈ W`. Simplify using `using hpW`. Establish `hVm` using `isMultiProjPrime_red p hImm hpI`. Take `⟨D, hKD, hD⟩` from `exists_dim_F p _ hVm`. Take `⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩` from `hP`.

Use `hQp` as an intermediate fact. Establish `hle : imageZ v P' ≤ imageZ v W` using `Ideal.comap_mono hPW`. Establish `hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P'`. Introduce `h`. Establish `h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι)`.

Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `h`. Rewrite `h2` using `[hQh, Ideal.mem_bot]`. Conclude with `hpr.ne_zero (by exact_mod_cast h2)`. Establish `hdim` using `krullDim_quot_add_one_le hle hpI hpQ`.

Rewrite `hdim` using `[← ringKrullDim_red p hpI, hD, hQd]`. Establish `hD' : D + 1 ≤ d + Fintype.card K` using `by exact_mod_cast hdim`. Establish `hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K)`. Rewrite using `[imageVar_red p v hpW]`. Use `⟨hVm, ?_⟩` and prove the remaining obligations.

Rewrite using `[hD, Nat.sub_add_cancel hKD]`. Take `⟨I, hI, -⟩` from `hR4 (ZMod p) K' ι'`. Rewrite using `[hGeo K' ι' p I hI W (d + r) _ hWm hpW hWp]`. Conclude with `hCMF (ZMod p) K ι K' ι' I hI κ v _ (D - Fintype.card K) d r L N hv hWp hVi (by omega)`.
-/
theorem geoNum_mixed_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d r : ℕ}
    (hP : IsArithVar (imageZ v P') d) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((d + r + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (L : Fin d → K → ℤ) (N : Fin r → K' → ℤ) :
    geoNum (d + r) W (Fin.append (fun j => pullDeg κ (L j)) N) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) (d + r) :=
    ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  obtain ⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩ := hP
  have := hQp
  have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
  have hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P' := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact h
    rw [hQh, Ideal.mem_bot] at h2
    exact hpr.ne_zero (by exact_mod_cast h2)
  have hdim := krullDim_quot_add_one_le hle hpI hpQ
  rw [← ringKrullDim_red p hpI, hD, hQd] at hdim
  have hD' : D + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K' ι'
  rw [hGeo K' ι' p I hI W (d + r) _ hWm hpW hWp]
  exact hCMF (ZMod p) K ι K' ι' I hI κ v _ (D - Fintype.card K) d r L N hv hWp hVi (by omega)

end ProjectionFormulaVertical

open ProjectionFormulaVertical in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' d r L L' N s a W hv hP' hP hL hs hsP hW hh`. Establish `hsec : IsSectionOn P' (HermLine.sqMetric (ι` using `ι') a) s := ⟨a, fun _ => rfl, hs, hsP⟩`. Take `⟨-, hvert⟩` from `divSuppArith K' ι' P' (d + r) _ _ W hP' hsec hW`. Take `⟨hWm, hpr, hWd⟩` from `hvert hh`. Establish `hPW : P' ≤ W` using `le_sup_left.trans hW.1.1.2`.

Establish `e : (fun j => (Fin.append L' N j).a) = Fin.append (fun j => pullDeg κ (L j).a) (fun j => (N j).a)`. Use function extensionality and compare the values at `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Simplify using `[(hL i).1]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `geoNum_mixed_eq_zero hGeo hR4 hCMF hv hP hPW hWm hpr hWd _ _`.
-/
theorem PFVert.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement) :
    PFVert.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N s a W hv hP' hP hL hs hsP hW hh
  classical
  have hsec : IsSectionOn P' (HermLine.sqMetric (ι := ι') a) s := ⟨a, fun _ => rfl, hs, hsP⟩
  obtain ⟨-, hvert⟩ := divSuppArith K' ι' P' (d + r) _ _ W hP' hsec hW
  obtain ⟨hWm, hpr, hWd⟩ := hvert hh
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  have e : (fun j => (Fin.append L' N j).a) =
      Fin.append (fun j => pullDeg κ (L j).a) (fun j => (N j).a) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [(hL i).1]
    · simp
  rw [e]
  exact geoNum_mixed_eq_zero hGeo hR4 hCMF hv hP hPW hWm hpr hWd _ _

end GroundTheory.Heights₂.Heights.Inter
