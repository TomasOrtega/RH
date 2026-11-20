import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilIntegralIdentity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsIsCharAF
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityOfFourierPairingIntegrable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens NumberField

open GlobalTheory.CompanionTheory.SiegelND.Coef (gramH)

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens

/- English proof (translation)
Use `haveI := hF`. Take `⟨k, eK, hK⟩` from `PI.VolStabS.exists_coord_tens F E`. Take `⟨k1, e1, h1⟩` from `PI.VolStabS.exists_coord_pi eK hK (Fin M)`. Take `⟨N, eV, hV⟩` from `PI.VolStabS.exists_coord_pi e1 h1 (Fin n)`. Set `eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)` to `{ eV.toEquiv with map_add' := hV }`.

Establish `hb : Bornology.IsBounded (eV '' S)` using `(hS.image eV.continuous).isBounded`. Take `⟨R, hR0, hR⟩` from `hb.subset_closedBall_lt 0 0`. Set `β : ContDiffBump (0 : Fin N → ℝ)` to `⟨R, R + 1, hR0, by linarith⟩`. Establish `hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ)` using `β.hasCompactSupport.comp_left Complex.ofReal_zero`. Set `f : SchwartzMap (Fin N → ℝ) ℂ` to `hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)`.

Use `⟨fun X => ⟨β (eV X), β.nonneg⟩, ?_, ?_, fun X hX => ?_, ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (β.continuous.comp eV.continuous) _`. Establish `h2 : HasCompactSupport fun X => β (eV X)` using `β.hasCompactSupport.comp_homeomorph eV`. Establish `h3 : (fun X => (⟨β (eV X), β.nonneg⟩ : ℝ≥0)) = Real.toNNReal ∘ fun X => β (eV X)`. Use function extensionality and compare the values at `fun X => (Real.toNNReal_of_nonneg β.nonneg).symm`.

Rewrite using `[h3]`. Conclude with `h2.comp_left (g := Real.toNNReal) (by simp)`. Establish `: β (eV X) = 1` using `β.one_of_mem_closedBall (hR ⟨X, hX, rfl⟩)`. Conclude with `NNReal.coe_le_coe.1 (show (1 : ℝ) ≤ β (eV X) from this.ge)`.
-/
theorem exists_cutoff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hF : IsTotallyReal F) (n M : ℕ) (S : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (hS : IsCompact S) :
    ∃ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0, Continuous P ∧ HasCompactSupport P ∧ (∀ X ∈ S, 1 ≤ P X) ∧
      GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (F := F) (E := E) fun X => ((P X : ℝ) : ℂ) := by
  haveI := hF
  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin n)
  let eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  have hb : Bornology.IsBounded (eV '' S) := (hS.image eV.continuous).isBounded
  obtain ⟨R, hR0, hR⟩ := hb.subset_closedBall_lt 0 0
  let β : ContDiffBump (0 : Fin N → ℝ) := ⟨R, R + 1, hR0, by linarith⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : SchwartzMap (Fin N → ℝ) ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  refine ⟨fun X => ⟨β (eV X), β.nonneg⟩, ?_, ?_, fun X hX => ?_,
    ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩⟩
  · exact Continuous.subtype_mk (β.continuous.comp eV.continuous) _
  · have h2 : HasCompactSupport fun X => β (eV X) := β.hasCompactSupport.comp_homeomorph eV
    have h3 : (fun X => (⟨β (eV X), β.nonneg⟩ : ℝ≥0)) = Real.toNNReal ∘ fun X => β (eV X) :=
      funext fun X => (Real.toNNReal_of_nonneg β.nonneg).symm
    rw [h3]
    exact h2.comp_left (g := Real.toNNReal) (by simp)
  · have : β (eV X) = 1 := β.one_of_mem_closedBall (hR ⟨X, hX, rfl⟩)
    exact NNReal.coe_le_coe.1 (show (1 : ℝ) ≤ β (eV X) from this.ge)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n _ hM d b lam hlam S hS`. Establish `hLoc` using `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1`. Take `⟨l1, l2, l3, l4, -, -, -, -⟩` from `id hLoc`. Use `haveI := l1`. Use `haveI := l2`.

Use `haveI := l3`. Use `haveI := l4`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Take `⟨t1, t2, t3, t4, -, -, -, t8, -, t10⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)`. Use `haveI := t1`.

Use `haveI := t2`. Use `haveI := t3`. Use `haveI := t4`. Use `haveI := t8 n M`. Take `⟨x1, x2, x3, x4, -⟩` from `GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n`.

Use `haveI := x1`. Use `haveI := x2`. Use `haveI := x3`. Use `haveI := x4`. Use `haveI : LocallyCompactSpace (HermR (Ainf F) σ n) := x1`.

Use `haveI : SecondCountableTopology (HermR (Ainf F) σ n) := x2`. Use `haveI : T2Space (HermR (Ainf F) σ n) := x3`. Use `haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Take `⟨-, hW, hH⟩` from `GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b lam hlam`.

Use `set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμdef`. Set `ν : Measure (HermR (Ainf F) σ n)` to `GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n`. Use `haveI hμH : μ.IsAddHaarMeasure := hW n M`. Use `haveI hνH : ν.IsAddHaarMeasure := hH n`. Establish `hqc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => gramH hCM hJ (Ainf F) X` using `(t10 n M J).subtype_mk _`.

Take `⟨ψ, hψ⟩` from `GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F`. Take `⟨ρ, e, hρ, he, heρ, -, -⟩` from `GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1`. Take `⟨a, ha, hinf, -, -, -⟩` from `GlobalTheory.T.adelic_character_archimedean_form F hCM.1 ρ e hρ he heρ ψ hψ`. Take `⟨τ, Θ, hΘ⟩` from `GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hCM ρ e hρ he heρ`. Establish `c1 : Continuous Θ` using `hΘ.1.continuous`.

Establish `c2 : Continuous Θ.symm` using `HermCoord.continuous_symm Θ hΘ.1`. Set `Ψ0` to `HermCoord.hermEquiv σ Θ hΘ.2.1 n`. Establish `h1 : Continuous Ψ0` using `HermCoord.continuous_hermEquiv σ Θ hΘ.2.1 c1 n`. Establish `h2 : Continuous Ψ0.symm` using `HermCoord.continuous_hermEquiv_symm σ Θ hΘ.2.1 c2 n`. Set `Ψh : HermR (Ainf F) σ n ≃ₜ (InfinitePlace F → hermC n)` to `{ toEquiv := Ψ0.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }`.

Set `Ψ : HermR (Ainf F) σ n ≃ᵐ (InfinitePlace F → hermC n)` to `Ψh.toMeasurableEquiv`. Establish `hνΨ : (ν.map Ψ).IsAddHaarMeasure` using `AddEquiv.isAddHaarMeasure_map ν Ψ0 h1 h2`. Take `⟨P, hPc, hPs, hP1, hPS⟩` from `exists_cutoff (E := E) hCM.1 n M S hS`. Set `c : InfinitePlace F → ℝ` to `fun w => ρ w a`. Establish `hc : ∀ w, c w ≠ 0` using `fun w => by simpa [c] using (map_ne_zero (ρ w)).2 ha`.

Establish `hfin : ∫⁻ X, P X ∂μ ≠ ⊤`. Establish `hcs : HasCompactSupport fun X => (P X : ℝ)` using `hPs.comp_left (g := fun x : ℝ≥0 => (x : ℝ)) rfl`. Establish `hint : Integrable (fun X => (P X : ℝ)) μ` using `(NNReal.continuous_coe.comp hPc).integrable_of_hasCompactSupport hcs`. Use `ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hint.2)` and prove the remaining obligations. Use `lintegral_congr fun X => ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[Real.enorm_eq_ofReal (NNReal.coe_nonneg (P X)), ENNReal.ofReal_coe_nnreal]`. Establish `hstar` using `integrable_starLoc_inf F E σ hCM M J hJ n hM ψ hψ μ hμH ν hνH _ hPS`. Establish `hphase : ∀ (b' : HermR (Ainf F) σ n) (X : Fin n → Fin M → Ainf F ⊗[F] E), psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (Matrix.trace ((b' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * gramR (Ainf F) σ J X))) = Complex.exp (2 * Real.pi * Complex …`. Introduce `b' X`.

Rewrite using `[GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J _ X]`. Use `congr 3`. Rewrite using `[phaseM, pairC_apply]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[PhaseCoord.gramC_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, ← PhaseCoord.coord_gramR σ e τ Θ hΘ]`.

Both sides reduce to the same expression. Establish `hi : Integrable (fun b' => ∫ X, ((P X : ℝ≥0) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((pairC n c (Ψ b') (Ψ (gramH hCM hJ (Ainf F) X)) : ℝ) : ℂ)) ∂μ) ν`. Use `hstar.congr (Filter.Eventually.of_forall fun b' => ?_)` and prove the remaining obligations. Use `show ∫ X, _ ∂μ = _`. Use `integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[hphase]`. Take `⟨C, hC, h⟩` from `density_transport (pairC n c) (fun u hu => pairC_nondeg hc u hu) μ ν Ψ hνΨ (fun X => gramH hCM hJ (Ainf F) X) hqc.measurable P hPc.measurable hfin S hP1 hi`. Conclude with `⟨C, hC, h⟩`.
-/
theorem density_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ S : Set (Fin n → Fin M → Ainf F ⊗[F] E), IsCompact S → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n) (GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F)) S C := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM d b lam hlam S hS
  have hLoc := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  obtain ⟨l1, l2, l3, l4, -, -, -, -⟩ := id hLoc
  haveI := l1
  haveI := l2
  haveI := l3
  haveI := l4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  obtain ⟨x1, x2, x3, x4, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n
  haveI := x1
  haveI := x2
  haveI := x3
  haveI := x4
  haveI : LocallyCompactSpace (HermR (Ainf F) σ n) := x1
  haveI : SecondCountableTopology (HermR (Ainf F) σ n) := x2
  haveI : T2Space (HermR (Ainf F) σ n) := x3
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b lam hlam
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμdef
  let ν : Measure (HermR (Ainf F) σ n) := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n
  haveI hμH : μ.IsAddHaarMeasure := hW n M
  haveI hνH : ν.IsAddHaarMeasure := hH n
  have hqc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => gramH hCM hJ (Ainf F) X :=
    (t10 n M J).subtype_mk _
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1
  obtain ⟨a, ha, hinf, -, -, -⟩ := GlobalTheory.T.adelic_character_archimedean_form F hCM.1 ρ e hρ he heρ ψ hψ
  obtain ⟨τ, Θ, hΘ⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hCM ρ e hρ he heρ
  have c1 : Continuous Θ := hΘ.1.continuous
  have c2 : Continuous Θ.symm := HermCoord.continuous_symm Θ hΘ.1
  let Ψ0 := HermCoord.hermEquiv σ Θ hΘ.2.1 n
  have h1 : Continuous Ψ0 := HermCoord.continuous_hermEquiv σ Θ hΘ.2.1 c1 n
  have h2 : Continuous Ψ0.symm := HermCoord.continuous_hermEquiv_symm σ Θ hΘ.2.1 c2 n
  let Ψh : HermR (Ainf F) σ n ≃ₜ (InfinitePlace F → hermC n) :=
    { toEquiv := Ψ0.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  let Ψ : HermR (Ainf F) σ n ≃ᵐ (InfinitePlace F → hermC n) := Ψh.toMeasurableEquiv
  have hνΨ : (ν.map Ψ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν Ψ0 h1 h2
  obtain ⟨P, hPc, hPs, hP1, hPS⟩ := exists_cutoff (E := E) hCM.1 n M S hS
  let c : InfinitePlace F → ℝ := fun w => ρ w a
  have hc : ∀ w, c w ≠ 0 := fun w => by simpa [c] using (map_ne_zero (ρ w)).2 ha
  have hfin : ∫⁻ X, P X ∂μ ≠ ⊤ := by
    have hcs : HasCompactSupport fun X => (P X : ℝ) := hPs.comp_left (g := fun x : ℝ≥0 => (x : ℝ)) rfl
    have hint : Integrable (fun X => (P X : ℝ)) μ :=
      (NNReal.continuous_coe.comp hPc).integrable_of_hasCompactSupport hcs
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hint.2)
    refine lintegral_congr fun X => ?_
    beta_reduce
    rw [Real.enorm_eq_ofReal (NNReal.coe_nonneg (P X)), ENNReal.ofReal_coe_nnreal]
  have hstar := integrable_starLoc_inf F E σ hCM M J hJ n hM ψ hψ μ hμH ν hνH _ hPS
  have hphase : ∀ (b' : HermR (Ainf F) σ n) (X : Fin n → Fin M → Ainf F ⊗[F] E),
      psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace ((b' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * gramR (Ainf F) σ J X))) =
      Complex.exp (2 * Real.pi * Complex.I * ((pairC n c (Ψ b') (Ψ (gramH hCM hJ (Ainf F) X)) : ℝ) : ℂ)) := by
    intro b' X
    rw [GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J _ X]
    congr 3
    rw [phaseM, pairC_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [PhaseCoord.gramC_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      ← PhaseCoord.coord_gramR σ e τ Θ hΘ]
    rfl
  have hi : Integrable (fun b' => ∫ X, ((P X : ℝ≥0) : ℂ) * Complex.exp (2 * Real.pi * Complex.I *
      ((pairC n c (Ψ b') (Ψ (gramH hCM hJ (Ainf F) X)) : ℝ) : ℂ)) ∂μ) ν := by
    refine hstar.congr (Filter.Eventually.of_forall fun b' => ?_)
    show ∫ X, _ ∂μ = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    beta_reduce
    rw [hphase]
  obtain ⟨C, hC, h⟩ := density_transport (pairC n c) (fun u hu => pairC_nondeg hc u hu) μ ν Ψ hνΨ
    (fun X => gramH hCM hJ (Ainf F) X) hqc.measurable P hPc.measurable hfin S hP1 hi
  exact ⟨C, hC, h⟩

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
