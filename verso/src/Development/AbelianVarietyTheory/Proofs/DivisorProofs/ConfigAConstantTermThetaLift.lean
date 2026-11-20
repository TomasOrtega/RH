import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReductionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKFubQZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, -, φ, hSB, hev, rfl⟩`. Conclude with `GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)`.
-/
theorem polData_le_schA {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`.

Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Use `haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`.

Use `haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology`. Establish `hcA : Continuous (cA σ)` using `IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap`.

Establish `hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E)))`. Establish `hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E))` using `Units.continuous_val`. Conclude with `isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))) continuous_const`. Conclude with `⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace, hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology⟩`.
-/
theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))) continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace, hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology⟩

end GlobalTheory.ThKFubQZero

namespace GlobalTheory.ThKFubQZero

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' hT Φ' hΦ' c hc μ 𝓕 hμ hF h1 h`. Use `haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩`. Use `haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩`. Take `⟨lc1, sc1⟩` from `lcsc_UA σ G.V'.J`. Take `⟨lc2, sc2⟩` from `lcsc_UA σ G.W.J`.

Use `haveI := lc1`. Use `haveI := sc1`. Use `haveI := lc2`. Use `haveI := sc2`. Establish `hP` using `GlobalTheory.ThK.Inhab.pairV' hT`.

Establish `hΦ : Φ' ∈ schA F _` using `polData_le_schA hT.geo.hM' hΦ'`. Establish `hq : G.q = 0` using `hC.q0`. Take `⟨hW, -⟩` from `GlobalTheory.T.weil_convergence_of_kernel hK F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hP (Or.inr (by simp [hq]))`. Take `⟨hconv, C, k, hbd⟩` from `hW Φ' hΦ`. Take `⟨hth, -⟩` from `GlobalTheory.T.theta_basic_properties hK.base F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hP`.

Take `⟨hcont, hinv, -⟩` from `hth Φ' hΦ`. Take `⟨R, hR⟩` from `GlobalTheory.T.unipotent_bounded_height_reduction F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ hT.base hT.geo.hW hC.hH'`. Use `haveI : (G.M'.μ).IsHaarMeasure := hT.geo.hM'.haar`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)`. Use `haveI : SigmaCompactSpace (UA σ G.V'.J) := inferInstance`.

Use `haveI : SigmaFinite G.M'.μ := inferInstance`. Use `haveI hs1 : SFinite (G.M'.μ.restrict G.M'.dom) := inferInstance`. Use `haveI hs2 : SFinite (μ.restrict 𝓕) := inferInstance`. Establish `hc' : ∀ g, c g h = ∫ u in 𝓕, theta om' Φ' g (u.1 * h) ∂μ` using `fun g => hc g μ 𝓕 hμ hF h1 h`. Repeatedly rewrite using `[hc']`.

Use `show ∫ g in G.M'.dom, ∫ u in 𝓕, theta om' Φ' g (u.1 * h) ∂μ ∂G.M'.μ = ∫ u in 𝓕, ∫ g in G.M'.dom, theta om' Φ' g (u.1 * h) ∂G.M'.μ ∂μ`. Establish `hfc : Continuous (fun p : UA σ G.V'.J × unip σ G.W H' => theta om' Φ' p.1 (p.2.1 * h))` using `hcont.comp (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).mul continuous_const))`. Establish `hfm` using `hfc.stronglyMeasurable`. Establish `hC0 : 0 ≤ C`. Establish `h0` using `(integral_nonneg (μ := G.M'.μ.restrict G.M'.dom) fun g => norm_nonneg (theta om' Φ' g 1)).trans (hbd 1)`.

Establish `hpos : (0 : ℝ) < (ht (1 : UA σ G.W.J) : ℝ) ^ k` using `pow_pos (lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_heightGL F _)) k`. Conclude with `nonneg_of_mul_nonneg_left h0 hpos`. Establish `hbound : ∀ u : unip σ G.W H', ∫ g in G.M'.dom, ‖theta om' Φ' g (u.1 * h)‖ ∂G.M'.μ ≤ C * ((R : ℝ) * ht h) ^ k`. Introduce `u`. Take `⟨γ, hγ, hγR⟩` from `hR u.1 u.2`.

Establish `e : ∀ g, theta om' Φ' g (u.1 * h) = theta om' Φ' g ((γ * u.1) * h)`. Introduce `g`. Use `hinv 1 (one_mem _) γ hγ.1 g (u.1 * h)` as an intermediate fact. Rewrite `this` using `[one_mul]`. Rewrite using `[mul_assoc, this]`.

Repeatedly rewrite using `[e]`. Use `(hbd _).trans (mul_le_mul_of_nonneg_left ?_ hC0)` and prove the remaining obligations. Use `pow_le_pow_left₀ (by positivity) ?_ k` and prove the remaining obligations. Use `heightGL_mul_le F (γ * u.1).1 h.1` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hint : Integrable (Function.uncurry fun g (u : unip σ G.W H') => theta om' Φ' g (u.1 * h)) ((G.M'.μ.restrict G.M'.dom).prod (μ.restrict 𝓕))`. Use `(integrable_prod_iff' hfm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun u => hconv (u.1 * h), ?_⟩` and prove the remaining obligations. Use `Integrable.mono' (integrable_const (C * ((R : ℝ) * ht h) ^ k)) ?_ (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Conclude with `(hfm.norm.integral_prod_left (μ := G.M'.μ.restrict G.M'.dom)).aestronglyMeasurable`. Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`.

Conclude with `hbound u`. Conclude with `integral_integral_swap hint`.
-/
theorem ctFubini : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ X om om', IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M', ∀ c : UA σ G.V'.J → UA σ G.W.J → ℂ, (∀ g, IsCT H' (theta om' Φ' g) (c g)) → IsCT H' (G.M'.I om' Φ') (fun h => ∫ g in G.M'.dom, c g h ∂G.M'.μ) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' hT Φ' hΦ' c hc μ 𝓕 hμ hF h1 h
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  obtain ⟨lc1, sc1⟩ := lcsc_UA σ G.V'.J
  obtain ⟨lc2, sc2⟩ := lcsc_UA σ G.W.J
  haveI := lc1; haveI := sc1; haveI := lc2; haveI := sc2
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hΦ : Φ' ∈ schA F _ := polData_le_schA hT.geo.hM' hΦ'
  have hq : G.q = 0 := hC.q0
  obtain ⟨hW, -⟩ := GlobalTheory.T.weil_convergence_of_kernel hK F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hP (Or.inr (by simp [hq]))
  obtain ⟨hconv, C, k, hbd⟩ := hW Φ' hΦ
  obtain ⟨hth, -⟩ := GlobalTheory.T.theta_basic_properties hK.base F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hP
  obtain ⟨hcont, hinv, -⟩ := hth Φ' hΦ
  obtain ⟨R, hR⟩ := GlobalTheory.T.unipotent_bounded_height_reduction F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ hT.base hT.geo.hW hC.hH'
  haveI : (G.M'.μ).IsHaarMeasure := hT.geo.hM'.haar
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  haveI : SigmaCompactSpace (UA σ G.V'.J) := inferInstance
  haveI : SigmaFinite G.M'.μ := inferInstance
  haveI hs1 : SFinite (G.M'.μ.restrict G.M'.dom) := inferInstance
  haveI hs2 : SFinite (μ.restrict 𝓕) := inferInstance
  have hc' : ∀ g, c g h = ∫ u in 𝓕, theta om' Φ' g (u.1 * h) ∂μ := fun g => hc g μ 𝓕 hμ hF h1 h
  simp_rw [hc']
  show ∫ g in G.M'.dom, ∫ u in 𝓕, theta om' Φ' g (u.1 * h) ∂μ ∂G.M'.μ =
    ∫ u in 𝓕, ∫ g in G.M'.dom, theta om' Φ' g (u.1 * h) ∂G.M'.μ ∂μ

  have hfc : Continuous (fun p : UA σ G.V'.J × unip σ G.W H' => theta om' Φ' p.1 (p.2.1 * h)) :=
    hcont.comp (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).mul continuous_const))
  have hfm := hfc.stronglyMeasurable

  have hC0 : 0 ≤ C := by
    have h0 := (integral_nonneg (μ := G.M'.μ.restrict G.M'.dom) fun g => norm_nonneg (theta om' Φ' g 1)).trans (hbd 1)
    have hpos : (0 : ℝ) < (ht (1 : UA σ G.W.J) : ℝ) ^ k :=
      pow_pos (lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_heightGL F _)) k
    exact nonneg_of_mul_nonneg_left h0 hpos

  have hbound : ∀ u : unip σ G.W H', ∫ g in G.M'.dom, ‖theta om' Φ' g (u.1 * h)‖ ∂G.M'.μ ≤ C * ((R : ℝ) * ht h) ^ k := by
    intro u
    obtain ⟨γ, hγ, hγR⟩ := hR u.1 u.2
    have e : ∀ g, theta om' Φ' g (u.1 * h) = theta om' Φ' g ((γ * u.1) * h) := by
      intro g
      have := hinv 1 (one_mem _) γ hγ.1 g (u.1 * h)
      rw [one_mul] at this
      rw [mul_assoc, this]
    simp_rw [e]
    refine (hbd _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have := heightGL_mul_le F (γ * u.1).1 h.1
    calc (ht ((γ * u.1) * h) : ℝ) ≤ (ht (γ * u.1) : ℝ) * ht h := by exact_mod_cast this
      _ ≤ R * ht h := mul_le_mul_of_nonneg_right (by exact_mod_cast hγR) (by positivity)
  have hint : Integrable (Function.uncurry fun g (u : unip σ G.W H') => theta om' Φ' g (u.1 * h))
      ((G.M'.μ.restrict G.M'.dom).prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff' hfm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun u => hconv (u.1 * h), ?_⟩
    refine Integrable.mono' (integrable_const (C * ((R : ℝ) * ht h) ^ k)) ?_ (Eventually.of_forall fun u => ?_)
    · exact (hfm.norm.integral_prod_left (μ := G.M'.μ.restrict G.M'.dom)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hbound u
  exact integral_integral_swap hint

end GlobalTheory.ThKFubQZero
