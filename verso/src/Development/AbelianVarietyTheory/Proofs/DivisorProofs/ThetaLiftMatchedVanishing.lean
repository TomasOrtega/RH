import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKTransSq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use extensionality with `g`. Use `show Formalism.UG.cT s (g : Matrix ι ι A) * (c • K) * (g : Matrix ι ι A) = c • K ↔ Formalism.UG.cT s (g : Matrix ι ι A) * K * (g : Matrix ι ι A) = K`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `hc.smul_left_cancel`.
-/
theorem uj_smul_eq {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι] (s : A →+* A) (K : Matrix ι ι A) {c : A}
    (hc : IsUnit c) : Formalism.UG.UJ s (c • K) = Formalism.UG.UJ s K := by
  ext g
  show Formalism.UG.cT s (g : Matrix ι ι A) * (c • K) * (g : Matrix ι ι A) = c • K ↔
    Formalism.UG.cT s (g : Matrix ι ι A) * K * (g : Matrix ι ι A) = K
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hc.smul_left_cancel

/- English proof (translation)
Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI : BorelSpace (UA σ J) := ⟨rfl⟩`. Take `⟨d, hd'⟩` from `GlobalTheory.HermLineZeros.exists_conj_ne hcm`. Establish `hss` using `GlobalTheory.HermLineZeros.conj_invol hcm`. Use `set δ : E := σ d - d with hδdef`.

Establish `hδ : δ ≠ 0` using `sub_ne_zero.2 hd'`. Establish `hσδ : σ δ = -δ` using `by rw [hδdef, map_sub, hss]; abel`. Use `set J' : Matrix (Fin n) (Fin n) E := δ • Jᵀ with hJ'`. Establish `hH : IsHermND σ J'`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [hJ', Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hσδ, hJ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hJ', Matrix.det_smul, Matrix.det_transpose]`. Conclude with `mul_ne_zero (pow_ne_zero _ hδ) hd`. Establish `hunit : IsUnit (inclR (F` using `F) (AF F) δ) := (Ne.isUnit hδ).map _`.

Establish `hJR : JR (F` using `F) (AF F) J' = (inclR (F := F) (AF F) δ) • JR (F := F) (AF F) Jᵀ := by`. Use extensionality with `i j`. Simplify using `[JR, hJ']`. Establish `hEq : HR (AF F) σ Jᵀ = HR (AF F) σ J'`. Unfold `HR`.

Rewrite using `[hJR, uj_smul_eq _ _ hunit]`. Set `e2 : HA (AF F) σ Jᵀ ≃ₜ* HA (AF F) σ J'` to `{ toMulEquiv := MulEquiv.subgroupCongr hEq continuous_toFun := continuous_subtype_val.subtype_mk _ continuous_invFun := continuous_subtype_val.subtype_mk _ }`. Use `haveI : IsTopologicalGroup (HA (AF F) σ Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ Jᵀ))`. Use `haveI : BorelSpace (HA (AF F) σ Jᵀ) := ⟨rfl⟩`. Use `haveI : IsTopologicalGroup (HA (AF F) σ J') := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J'))`.

Use `haveI : BorelSpace (HA (AF F) σ J') := ⟨rfl⟩`. Set `e` to `(GlobalTheory.ThetaRightTranslate.toHA σ J).trans e2`. Use `GlobalTheory.ThetaRightTranslate.isMulRightInvariant_of_equiv e μ ?_` and prove the remaining obligations. Use `haveI : (μ.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e`. Conclude with `GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ hss hδ hσδ hH (μ.map e)`.
-/
theorem isMulRightInvariant_skew (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  obtain ⟨d, hd'⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
  have hss := GlobalTheory.HermLineZeros.conj_invol hcm
  set δ : E := σ d - d with hδdef
  have hδ : δ ≠ 0 := sub_ne_zero.2 hd'
  have hσδ : σ δ = -δ := by rw [hδdef, map_sub, hss]; abel
  set J' : Matrix (Fin n) (Fin n) E := δ • Jᵀ with hJ'
  have hH : IsHermND σ J' := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [hJ', Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hσδ, hJ]
      ring
    · rw [hJ', Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ hδ) hd
  have hunit : IsUnit (inclR (F := F) (AF F) δ) := (Ne.isUnit hδ).map _
  have hJR : JR (F := F) (AF F) J' = (inclR (F := F) (AF F) δ) • JR (F := F) (AF F) Jᵀ := by
    ext i j; simp [JR, hJ']
  have hEq : HR (AF F) σ Jᵀ = HR (AF F) σ J' := by
    unfold HR; rw [hJR, uj_smul_eq _ _ hunit]
  let e2 : HA (AF F) σ Jᵀ ≃ₜ* HA (AF F) σ J' :=
    { toMulEquiv := MulEquiv.subgroupCongr hEq
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  haveI : IsTopologicalGroup (HA (AF F) σ Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ Jᵀ))
  haveI : BorelSpace (HA (AF F) σ Jᵀ) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF F) σ J') := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J'))
  haveI : BorelSpace (HA (AF F) σ J') := ⟨rfl⟩
  let e := (GlobalTheory.ThetaRightTranslate.toHA σ J).trans e2
  refine GlobalTheory.ThetaRightTranslate.isMulRightInvariant_of_equiv e μ ?_
  haveI : (μ.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  exact GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ hss hδ hσδ hH (μ.map e)

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h` using `GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)`. Rewrite `h` using `[Matrix.det_smul]`. Establish `h'` using `right_ne_zero_of_mul h`. Rewrite `h'` using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `fun h0 => h' (by rw [h0, map_zero])`.
-/
theorem det_ne_zero_of_isSkew (σ : E →ₐ[F] E) (B : Base F E) {n : ℕ} (X : Spc F E n) {r s : ℕ}
    (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul] at h
  have h' := right_ne_zero_of_mul h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h'
  exact fun h0 => h' (by rw [h0, map_zero])

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ hΦ h`. Establish `hT` using `hM.triple`. Take `⟨hc, hinv⟩` from `GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ hΦ`. Establish `hsq` using `(GlobalTheory.T.square_integrability hK F E σ B a a' G X om om' hT μ 𝓕 hμ h𝓕).2 Φ hΦ`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`.

Use `haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩`. Use `haveI := hμ`. Use `haveI : μ.IsMulRightInvariant := isMulRightInvariant_skew σ hT.base.cm G.W.J hT.geo.hW.skew (det_ne_zero_of_isSkew σ B G.W hT.geo.hW) μ`. Use `haveI := GlobalTheory.ThetaRightTranslate.countable_ratU σ G.W.J`. Establish `hi` using `GlobalTheory.integrableOn_fundamentalDomain_mul_right h𝓕 h (fun x => ((‖G.M'.I om' Φ x‖ ^ 2 : ℝ) : ℂ)) (fun γ hγ x => by simp only [hinv γ hγ x]) (by exact hsq.ofReal)`.

Establish `hm : AEStronglyMeasurable (fun x => G.M'.I om' Φ (x * h)) (μ.restrict 𝓕)` using `(hc.comp (continuous_mul_const h)).aestronglyMeasurable`. Rewrite using `[memLp_two_iff_integrable_sq_norm hm]`. Conclude with `hi.re.congr (ae_of_all _ fun x => RCLike.ofReal_re (K := ℂ) _)`.
-/
theorem memLp_translate : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, MeasureTheory.MemLp (fun x => G.M'.I om' Φ (x * h)) 2 (μ.restrict 𝓕) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ hΦ h
  have hT := hM.triple
  obtain ⟨hc, hinv⟩ := GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ hΦ
  have hsq := (GlobalTheory.T.square_integrability hK F E σ B a a' G X om om' hT μ 𝓕 hμ h𝓕).2 Φ hΦ
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI := hμ
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_skew σ hT.base.cm G.W.J hT.geo.hW.skew
    (det_ne_zero_of_isSkew σ B G.W hT.geo.hW) μ
  haveI := GlobalTheory.ThetaRightTranslate.countable_ratU σ G.W.J
  have hi := GlobalTheory.integrableOn_fundamentalDomain_mul_right h𝓕 h
    (fun x => ((‖G.M'.I om' Φ x‖ ^ 2 : ℝ) : ℂ)) (fun γ hγ x => by simp only [hinv γ hγ x]) (by exact hsq.ofReal)
  have hm : AEStronglyMeasurable (fun x => G.M'.I om' Φ (x * h)) (μ.restrict 𝓕) :=
    (hc.comp (continuous_mul_const h)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  exact hi.re.congr (ae_of_all _ fun x => RCLike.ofReal_re (K := ℂ) _)

end GlobalTheory.ThKTransSq
