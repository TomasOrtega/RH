import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.Reduce
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace PositivityTheory.PfSWUS.SchInf

open GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Use `set B : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g with hB`. Use `⟨B, fun y => ?_⟩` and prove the remaining obligations. Establish `h1` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g y`. Rewrite `h1` using `[norm_iteratedFDeriv_zero]`. Establish `hy : 0 < 1 + ‖y‖` using `by positivity`.

Rewrite using `[Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem schwartz_decay {N : ℕ} (g : SchwartzMap (Fin N → ℝ) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := by
  set B : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g with hB
  refine ⟨B, fun y => ?_⟩
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g y
  rw [norm_iteratedFDeriv_zero] at h1
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖g y‖ * (1 + ‖y‖) ^ k = (1 + ‖y‖) ^ k * ‖g y‖ := by ring
    _ ≤ B := h1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hm φ hφ`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Establish `hloc : IsLocR (Ainf F)` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1`. Take `⟨i1, i2, i3, i4, -, -, -, hBor, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)`. Use `i1` as an intermediate fact.

Use `i2` as an intermediate fact. Use `i3` as an intermediate fact. Use `i4` as an intermediate fact. Use `hBor n M` as an intermediate fact. Take `⟨-, hcomp, hone, hmem, -⟩` from `GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Ainf F) n`.

Take `⟨N, eV, heV, heVs, L, hL, hLe⟩` from `hC F E σ hσ n M`. Take `⟨g, hg⟩` from `hφ N eV heV heVs`. Establish `hφeq : ∀ X, φ X = g (eV X)` using `fun X => by rw [hg, AddEquiv.symm_apply_apply]`. Set `T : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)` to `{ toEquiv := eV.toEquiv, continuous_toFun := heV, continuous_invFun := heVs }`. Establish `hTm : MeasurableEmbedding eV` using `T.measurableEmbedding`.

Establish `hμ' : (μ.map eV).IsAddHaarMeasure` using `eV.isAddHaarMeasure_map μ heV heVs`. Establish `key : ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → ∀ g' : (Fin N → ℝ) → ℂ, Continuous g' → (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g' y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) → (∀ᶠ S in 𝓝 c, Integrable g' ((m S).map eV)) ∧ ContinuousAt (fun S => ∫ y, g' y ∂((m S). …`. Introduce `c hc g' hg'c hg'd`. Take `⟨O, hO, hcO, hsec⟩` from `hB F E σ hσ n c hc`. Take `⟨A, C, hAc, hCc, hAC⟩` from `hD F E σ hσ n M μ ν hμ hν`.

Use `hA N (HermR (Ainf F) σ n) (μ.map eV) hμ' (fun S => (m S).map eV) c O hO hcO ?_ ?_ g' hg'c hg'd` and prove the remaining obligations. Introduce `f hf hfin U hU hne`. Rewrite `hfin` using `[lintegral_map hf hTm.measurable]`. Take `⟨S, hS, hS'⟩` from `hE F E σ hσ M J hJ n μ ν m hμ hν hm (fun X => f (eV X)) (hf.comp hTm.measurable) hfin U hU hne`. Conclude with `⟨S, hS, by rwa [lintegral_map hf hTm.measurable]⟩`.

Introduce `s₀ hs₀`. Take `⟨h, hinv, hhc, hhic, hhS⟩` from `hsec s₀ hs₀`. Establish `hunit : ∀ S ∈ O, IsUnit (h S).det` using `fun S hS => Matrix.isUnit_det_of_right_inverse (hhS S hS).1`. Establish `hcn : O ∈ 𝓝 c` using `hO.mem_nhds hcO`. Establish `hh_at : ContinuousAt h c` using `hhc.continuousAt hcn`.

Establish `hhi_at : ContinuousAt hinv c` using `hhic.continuousAt hcn`. Establish `hU_ev : ∀ᶠ S in 𝓝 c, h S ∈ {g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det}` using `Filter.mem_of_superset hcn fun S hS => hunit S hS`. Establish `htends : Filter.Tendsto h (𝓝 c) (𝓝[{g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det}] (h c))` using `tendsto_nhdsWithin_iff.2 ⟨hh_at, hU_ev⟩`. Establish `hA_at : ContinuousAt (fun S => A (h S)) c` using `(hAc (h c) (hunit c hcO)).tendsto.comp htends`. Establish `hC_at : ContinuousAt (fun S => C (h S)) c` using `(hCc (h c) (hunit c hcO)).tendsto.comp htends`.

Use `⟨fun S => L (h S), fun S => L (hinv S), fun S => C (h S) * (A (h S))⁻¹, hL.continuousAt.comp hh_at, hL.continuousAt.comp hhi_at, hC_at.mul (hA_at.inv₀ (hAC _ (hunit c hcO)).1), ?_, ?_⟩` and prove the remaining obligations. Introduce `S hS y`. Take `⟨X, rfl⟩` from `eV.surjective y`. Use `show L (hinv S) (L (h S) (eV X)) = eV X`. Rewrite using `[← hLe, ← hLe, hcomp, (hhS S hS).1, hone]`.

Introduce `S hS`. Establish `hu` using `hunit S hS`. Take `⟨hA0, -, hAm, hCm⟩` from `hAC (h S) hu`. Set `τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n` to `fun S' => ⟨cT (sigR (Ainf F) σ) (h S) * (S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h S, hmem S' (h S)⟩`. Establish `hτ : ∀ S', (τ S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) (h S) * S' * h S` using `fun _ => rfl`.

Establish `hk` using `GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc n μ ν m hμ hν hm (h S) hu τ hτ (A (h S)) (C (h S)) hAm (hCm τ hτ) s₀`. Establish `hτs : τ s₀ = S` using `Subtype.ext (hhS S hS).2.2.symm`. Rewrite `hk` using `[hτs]`. Establish `hmS : m S = (C (h S) * (A (h S))⁻¹) • (m s₀).map (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S))`. Rewrite using `[mul_comm, ← smul_smul, ← hk, smul_smul, inv_mul_cancel₀ hA0, one_smul]`.

Establish `hrm : Measurable (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S))`. Establish `: (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) = fun X => eV.symm (L (h S) (eV X))`. Use function extensionality and compare the values at `X`. Rewrite using `[← hLe, AddEquiv.symm_apply_apply]`. Rewrite using `[this]`.

Conclude with `(heVs.comp ((L (h S)).continuous.comp heV)).measurable`. Use `show (m S).map eV = _`. Rewrite using `[hmS, Measure.map_smul, Measure.map_map hTm.measurable hrm, Measure.map_map (L (h S)).continuous.measurable hTm.measurable]`. Use `congr 2`. Use function extensionality and compare the values at `X`.

Conclude with `hLe (h S) X`. Establish `hgk : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))` using `schwartz_decay g`. Establish `hng : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖((‖g y‖ : ℝ) : ℂ)‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))`. Introduce `k`. Take `⟨C, hC⟩` from `hgk k`.

Conclude with `⟨C, fun y => by simpa using hC y⟩`. Establish `hngc : Continuous fun y => ((‖g y‖ : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp g.continuous.norm`. Establish `hφc : Continuous φ`. Rewrite using `[show φ = fun X => g (eV X) from funext hφeq]`. Conclude with `g.continuous.comp heV`.

Establish `hIntS : ∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)`. Introduce `S hS`. Establish `h1` using `((key S hS g g.continuous hgk).1).self_of_nhds`. Rewrite `h1` using `[hTm.integrable_map_iff]`. Rewrite using `[show φ = (⇑g ∘ ⇑eV) from funext hφeq]` and apply the resulting hypothesis.

Establish `hcont : ContinuousOn (fun S => ∫ X, φ X ∂(m S)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}`. Introduce `S hS`. Use `((key S hS g g.continuous hgk).2.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt` and prove the remaining obligations. Use `show ∫ y, g y ∂((m S').map eV) = ∫ X, φ X ∂(m S')`. Rewrite using `[hTm.integral_map]`.

Simplify using `only [hφeq]`. Establish `hcontn : ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}`. Introduce `S hS`. Establish `h3 : ContinuousAt (fun S' => (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re) S` using `Complex.continuous_re.continuousAt.comp (key S hS _ hngc hng).2`. Use `(h3.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt` and prove the remaining obligations.

Use `show (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re = ∫ X, ‖φ X‖ ∂(m S')`. Rewrite using `[hTm.integral_map, integral_complex_ofReal, Complex.ofReal_re]`. Simplify using `only [hφeq]`. Establish `hφμ : Integrable φ μ`. Take `⟨C0, hC0⟩` from `hgk (Module.finrank ℝ (Fin N → ℝ) + 1)`.

Establish `hW : Integrable (fun y : Fin N → ℝ => (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin N → ℝ) + 1 : ℕ) : ℝ))) (μ.map eV)` using `integrable_one_add_norm (by push_cast; linarith)`. Establish `hgμ : Integrable g (μ.map eV)` using `Integrable.mono' (hW.const_mul C0) g.continuous.aestronglyMeasurable (ae_of_all _ hC0)`. Rewrite `hgμ` using `[hTm.integrable_map_iff]`. Rewrite using `[show φ = (⇑g ∘ ⇑eV) from funext hφeq]` and apply the resulting hypothesis. Conclude with `⟨hφc, ⟨hcont, fun K hK hKB => hF F E σ hσ M J hJ n μ ν m hμ hν hm φ hφc hφμ hIntS hcontn K hK hKB⟩, hIntS⟩`.
-/
theorem schwartzDensInf_of (hA : FamCont) (hB : SecInf) (hC : CoordInf) (hD : ScaleInf) (hE : FinOpen)
    (hF : DensInt) : PositivityTheory.PfSWUS.HMass.SchwartzDensInf := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hm φ hφ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hloc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have := i1
  have := i2
  have := i3
  have := i4
  have := hBor n M
  obtain ⟨-, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Ainf F) n
  obtain ⟨N, eV, heV, heVs, L, hL, hLe⟩ := hC F E σ hσ n M
  obtain ⟨g, hg⟩ := hφ N eV heV heVs
  have hφeq : ∀ X, φ X = g (eV X) := fun X => by rw [hg, AddEquiv.symm_apply_apply]
  let T : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ) :=
    { toEquiv := eV.toEquiv, continuous_toFun := heV, continuous_invFun := heVs }
  have hTm : MeasurableEmbedding eV := T.measurableEmbedding
  have hμ' : (μ.map eV).IsAddHaarMeasure := eV.isAddHaarMeasure_map μ heV heVs
  have key : ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
      ∀ g' : (Fin N → ℝ) → ℂ, Continuous g' → (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g' y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) →
      (∀ᶠ S in 𝓝 c, Integrable g' ((m S).map eV)) ∧
        ContinuousAt (fun S => ∫ y, g' y ∂((m S).map eV)) c := by
    intro c hc g' hg'c hg'd
    obtain ⟨O, hO, hcO, hsec⟩ := hB F E σ hσ n c hc
    obtain ⟨A, C, hAc, hCc, hAC⟩ := hD F E σ hσ n M μ ν hμ hν
    refine hA N (HermR (Ainf F) σ n) (μ.map eV) hμ' (fun S => (m S).map eV) c O hO hcO ?_ ?_ g' hg'c hg'd
    · intro f hf hfin U hU hne
      rw [lintegral_map hf hTm.measurable] at hfin
      obtain ⟨S, hS, hS'⟩ := hE F E σ hσ M J hJ n μ ν m hμ hν hm (fun X => f (eV X))
        (hf.comp hTm.measurable) hfin U hU hne
      exact ⟨S, hS, by rwa [lintegral_map hf hTm.measurable]⟩
    · intro s₀ hs₀
      obtain ⟨h, hinv, hhc, hhic, hhS⟩ := hsec s₀ hs₀
      have hunit : ∀ S ∈ O, IsUnit (h S).det := fun S hS =>
        Matrix.isUnit_det_of_right_inverse (hhS S hS).1
      have hcn : O ∈ 𝓝 c := hO.mem_nhds hcO
      have hh_at : ContinuousAt h c := hhc.continuousAt hcn
      have hhi_at : ContinuousAt hinv c := hhic.continuousAt hcn
      have hU_ev : ∀ᶠ S in 𝓝 c, h S ∈ {g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det} :=
        Filter.mem_of_superset hcn fun S hS => hunit S hS
      have htends : Filter.Tendsto h (𝓝 c)
          (𝓝[{g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det}] (h c)) :=
        tendsto_nhdsWithin_iff.2 ⟨hh_at, hU_ev⟩
      have hA_at : ContinuousAt (fun S => A (h S)) c := (hAc (h c) (hunit c hcO)).tendsto.comp htends
      have hC_at : ContinuousAt (fun S => C (h S)) c := (hCc (h c) (hunit c hcO)).tendsto.comp htends
      refine ⟨fun S => L (h S), fun S => L (hinv S), fun S => C (h S) * (A (h S))⁻¹,
        hL.continuousAt.comp hh_at, hL.continuousAt.comp hhi_at,
        hC_at.mul (hA_at.inv₀ (hAC _ (hunit c hcO)).1), ?_, ?_⟩
      · intro S hS y
        obtain ⟨X, rfl⟩ := eV.surjective y
        show L (hinv S) (L (h S) (eV X)) = eV X
        rw [← hLe, ← hLe, hcomp, (hhS S hS).1, hone]
      · intro S hS
        have hu := hunit S hS
        obtain ⟨hA0, -, hAm, hCm⟩ := hAC (h S) hu
        let τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S' =>
          ⟨cT (sigR (Ainf F) σ) (h S) * (S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h S, hmem S' (h S)⟩
        have hτ : ∀ S', (τ S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
            cT (sigR (Ainf F) σ) (h S) * S' * h S := fun _ => rfl
        have hk := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc n μ ν m hμ hν hm (h S) hu τ hτ
          (A (h S)) (C (h S)) hAm (hCm τ hτ) s₀
        have hτs : τ s₀ = S := Subtype.ext (hhS S hS).2.2.symm
        rw [hτs] at hk
        have hmS : m S = (C (h S) * (A (h S))⁻¹) • (m s₀).map (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) := by
          rw [mul_comm, ← smul_smul, ← hk, smul_smul, inv_mul_cancel₀ hA0, one_smul]
        have hrm : Measurable (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) := by
          have : (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) = fun X => eV.symm (L (h S) (eV X)) := by
            funext X
            rw [← hLe, AddEquiv.symm_apply_apply]
          rw [this]
          exact (heVs.comp ((L (h S)).continuous.comp heV)).measurable
        show (m S).map eV = _
        rw [hmS, Measure.map_smul, Measure.map_map hTm.measurable hrm,
          Measure.map_map (L (h S)).continuous.measurable hTm.measurable]
        congr 2
        funext X
        exact hLe (h S) X
  have hgk : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := schwartz_decay g
  have hng : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖((‖g y‖ : ℝ) : ℂ)‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := by
    intro k
    obtain ⟨C, hC⟩ := hgk k
    exact ⟨C, fun y => by simpa using hC y⟩
  have hngc : Continuous fun y => ((‖g y‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp g.continuous.norm
  have hφc : Continuous φ := by
    rw [show φ = fun X => g (eV X) from funext hφeq]
    exact g.continuous.comp heV
  have hIntS : ∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
      Integrable φ (m S) := by
    intro S hS
    have h1 := ((key S hS g g.continuous hgk).1).self_of_nhds
    rw [hTm.integrable_map_iff] at h1
    rwa [show φ = (⇑g ∘ ⇑eV) from funext hφeq]
  have hcont : ContinuousOn (fun S => ∫ X, φ X ∂(m S))
      {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
    intro S hS
    refine ((key S hS g g.continuous hgk).2.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt
    show ∫ y, g y ∂((m S').map eV) = ∫ X, φ X ∂(m S')
    rw [hTm.integral_map]
    simp only [hφeq]
  have hcontn : ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S))
      {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
    intro S hS
    have h3 : ContinuousAt (fun S' => (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re) S :=
      Complex.continuous_re.continuousAt.comp (key S hS _ hngc hng).2
    refine (h3.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt
    show (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re = ∫ X, ‖φ X‖ ∂(m S')
    rw [hTm.integral_map, integral_complex_ofReal, Complex.ofReal_re]
    simp only [hφeq]
  have hφμ : Integrable φ μ := by
    obtain ⟨C0, hC0⟩ := hgk (Module.finrank ℝ (Fin N → ℝ) + 1)
    have hW : Integrable (fun y : Fin N → ℝ => (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin N → ℝ) + 1 : ℕ) : ℝ)))
        (μ.map eV) := integrable_one_add_norm (by push_cast; linarith)
    have hgμ : Integrable g (μ.map eV) :=
      Integrable.mono' (hW.const_mul C0) g.continuous.aestronglyMeasurable (ae_of_all _ hC0)
    rw [hTm.integrable_map_iff] at hgμ
    rwa [show φ = (⇑g ∘ ⇑eV) from funext hφeq]
  exact ⟨hφc, ⟨hcont, fun K hK hKB => hF F E σ hσ M J hJ n μ ν m hμ hν hm φ hφc hφμ hIntS hcontn K hK hKB⟩,
    hIntS⟩

end PositivityTheory.PfSWUS.SchInf

end
