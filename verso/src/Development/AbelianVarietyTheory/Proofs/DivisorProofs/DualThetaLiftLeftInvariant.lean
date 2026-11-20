import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaRightInv

/- English proof (translation)
Use `haveI : SMulInvariantMeasure Γ Gr μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩`. Establish `h0 : μ 𝓕 ≠ 0` using `h𝓕.measure_ne_zero (NeZero.ne μ)`. Use `⟨measurable_mul_const g, ?_⟩` and prove the remaining obligations. Use `set c := Measure.haarScalarFactor (Measure.map (· * g) μ) μ with hcdef`. Establish `e : Measure.map (· * g) μ = c • μ` using `Measure.isMulLeftInvariant_eq_smul _ _`.

Establish `hq : Measure.QuasiMeasurePreserving (· * g) μ μ` using `⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩`. Establish `h2 : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ` using `h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id fun γ x => by show γ.1 * x * g = γ.1 * (x * g)`. Rewrite using `[mul_assoc]`. Establish `h1 : Measure.map (· * g) μ 𝓕 = μ 𝓕`. Rewrite using `[(measurableEmbedding_mulRight g).map_apply]`.

Conclude with `h2.measure_eq h𝓕`. Rewrite `h1` using `[e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `hc : ((c : ENNReal)) = 1`. Establish `h3 : (c : ENNReal) * μ 𝓕 / μ 𝓕 = (c : ENNReal)` using `ENNReal.mul_div_cancel_right h0 htop`. Rewrite `h3` using `[h1, ENNReal.div_self h0 htop]`.

Conclude with `h3.symm`. Establish `hc' : c = 1` using `by exact_mod_cast hc`. Rewrite using `[e, hc', one_smul]`.
-/
theorem measurePreserving_mul_right_of_fundDom {Gr : Type} [Group Gr] [TopologicalSpace Gr] [IsTopologicalGroup Gr]
    [LocallyCompactSpace Gr] [SecondCountableTopology Gr] [MeasurableSpace Gr] [BorelSpace Gr] (μ : Measure Gr)
    [μ.IsHaarMeasure] (Γ : Subgroup Gr) [Countable Γ] (𝓕 : Set Gr) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (htop : μ 𝓕 ≠ ⊤) (g : Gr) : MeasurePreserving (· * g) μ μ := by
  haveI : SMulInvariantMeasure Γ Gr μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  refine ⟨measurable_mul_const g, ?_⟩
  set c := Measure.haarScalarFactor (Measure.map (· * g) μ) μ with hcdef
  have e : Measure.map (· * g) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have hq : Measure.QuasiMeasurePreserving (· * g) μ μ :=
    ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
  have h2 : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id fun γ x => by
      show γ.1 * x * g = γ.1 * (x * g)
      rw [mul_assoc]
  have h1 : Measure.map (· * g) μ 𝓕 = μ 𝓕 := by
    rw [(measurableEmbedding_mulRight g).map_apply]
    exact h2.measure_eq h𝓕
  rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : ((c : ENNReal)) = 1 := by
    have h3 : (c : ENNReal) * μ 𝓕 / μ 𝓕 = (c : ENNReal) := ENNReal.mul_div_cancel_right h0 htop
    rw [h1, ENNReal.div_self h0 htop] at h3
    exact h3.symm
  have hc' : c = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

/- English proof (translation)
Introduce `hP hTB F E _ _ _ _ _ σ B a a' G X om om' hT _ Φ' hΦ' g h`. Establish `hpair` using `(GlobalTheory.ThK.Check.isPair_of_isTriple hT).2`. Establish `hinv` using `((hTB F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hpair).1 Φ' hΦ').2.1`. Take `⟨hTG, hLC, hSC, -⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ a' G.V'.J`. Use `haveI := hTG`.

Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩`. Use `haveI := hT.geo.hM'.haar`. Use `haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.V'.J`.

Use `haveI : MeasurableMul (UA σ G.V'.J) := ⟨fun x => (continuous_const.mul continuous_id).measurable, fun x => (continuous_id.mul continuous_const).measurable⟩`. Establish `hfin` using `GlobalTheory.UnitaryVol.measure_dom_lt_top F E σ B a a' G X om om' hP hT`. Establish `hmp` using `measurePreserving_mul_right_of_fundDom G.M'.μ (ratU σ G.V'.J) G.M'.dom hT.geo.hM'.dom hfin.ne g`. Establish `e1 : ∀ x, theta om' (om' (g, 1) Φ') x h = theta om' Φ' (x * g) h`. Introduce `x`.

Simplify using `only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`. Simplify using `only [Model.I, e1]`. Conclude with `GlobalTheory.DefiniteClassAvg.setIntegral_comp_mul_right_of_mp G.M'.μ (ratU σ G.V'.J) G.M'.dom hT.geo.hM'.dom (fun x => theta om' Φ' x h) (fun γ hγ x => by simpa using hinv γ hγ 1 (one_mem _) x h) g hmp`.
-/
theorem rightInv : GlobalTheory.Published.SiegelSetUnitary → ThetaBasic → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 → ∀ Φ' ∈ schA F (Fin a' × Fin (a + a')),
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), G.M'.I om' (om' (g, 1) Φ') h = G.M'.I om' Φ' h := by
  intro hP hTB F E _ _ _ _ _ σ B a a' G X om om' hT _ Φ' hΦ' g h
  have hpair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hinv := ((hTB F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hpair).1 Φ' hΦ').2.1
  obtain ⟨hTG, hLC, hSC, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ a' G.V'.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI := hT.geo.hM'.haar
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.V'.J
  haveI : MeasurableMul (UA σ G.V'.J) :=
    ⟨fun x => (continuous_const.mul continuous_id).measurable, fun x => (continuous_id.mul continuous_const).measurable⟩
  have hfin := GlobalTheory.UnitaryVol.measure_dom_lt_top F E σ B a a' G X om om' hP hT
  have hmp := measurePreserving_mul_right_of_fundDom G.M'.μ (ratU σ G.V'.J) G.M'.dom hT.geo.hM'.dom hfin.ne g
  have e1 : ∀ x, theta om' (om' (g, 1) Φ') x h = theta om' Φ' (x * g) h := by
    intro x
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e1]
  exact GlobalTheory.DefiniteClassAvg.setIntegral_comp_mul_right_of_mp G.M'.μ (ratU σ G.V'.J) G.M'.dom hT.geo.hM'.dom
    (fun x => theta om' Φ' x h) (fun γ hγ x => by simpa using hinv γ hγ 1 (one_mem _) x h) g hmp

end GlobalTheory.ThetaRightInv

end
