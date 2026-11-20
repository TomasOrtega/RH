import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHaarMeasureNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentHaarModulusStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IwInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Use `haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology`. Use `haveI : T2Space (AE F E) := e.isEmbedding.t2Space`.

Use `haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology`. Conclude with `⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance⟩`.
-/
theorem ideleTop : IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ ∧
    T2Space (AE F E)ˣ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance⟩

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨t1, t2, t3, t4⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J`. Take `⟨u1, u2, u3, u4⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n₁ X₁.J`. Take `⟨v1, v2, v3, v4⟩` from `ideleTop (F := F) (E := E)`. Use `haveI := t1`. Use `haveI := t2`.

Use `haveI := t3`. Use `haveI := t4`. Use `haveI := u1`. Use `haveI := u2`. Use `haveI := u3`.

Use `haveI := u4`. Use `haveI := v1`. Use `haveI := v2`. Use `haveI := v3`. Use `haveI := v4`.

Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Use `haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩`. Use `haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩`. Take `⟨hmul, hcont, hmemQ, huniq, hQc, hNc, hNQ, hnorm⟩` from `GlobalTheory.T.levi_embedding_multiplicative F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm`. Set `mh : ((AE F E)ˣ × UA σ X₁.J) →* UA σ X.J` to `MonoidHom.mk' (fun x => m x.1 x.2) (fun x y => hmul x.1 y.1 x.2 y.2)`.

Establish `hmh : ∀ x, mh x = m x.1 x.2` using `fun _ => rfl`. Use `haveI : LocallyCompactSpace (unip σ X H) := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Set `μN : Measure (unip σ X H)` to `Measure.haar`. Set `d : (AE F E)ˣ × UA σ X₁.J → ENNReal` to `fun x => ENNReal.ofReal ((absE F E x.1 : ℝ) ^ (1 - (n : ℝ)))`. Establish `hpos : ∀ l : (AE F E)ˣ, 0 < (absE F E l : ℝ)` using `fun l => by`.

Establish `h` using `congrArg (fun t : ℝ≥0 => (t : ℝ)) (map_mul_eq_one (absE F E) (mul_inv_cancel l))`. Simplify using `only [NNReal.coe_mul, NNReal.coe_one] at h`. Break down `(NNReal.coe_nonneg (absE F E l)).lt_or_eq with h' | h'` into its components or cases. Conclude with `h'`. Rewrite `h` using `[← h', zero_mul]`.

Conclude with `absurd h zero_ne_one`. Establish `hd_cont : Continuous d` using `ENNReal.continuous_ofReal.comp ((NNReal.continuous_coe.comp ((GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).comp continuous_fst)).rpow_const fun x => Or.inl (hpos x.1).ne')`. Establish `hd_meas : Measurable d` using `hd_cont.measurable`. Establish `hd_mul : ∀ x y, d (x * y) = d x * d y` using `fun x y => by`. Simplify using `only [d, Prod.fst_mul, map_mul, NNReal.coe_mul]`.

Rewrite using `[Real.mul_rpow (hpos _).le (hpos _).le, ENNReal.ofReal_mul (Real.rpow_nonneg (hpos _).le _)]`. Establish `hd_pos : ∀ x, d x ≠ 0 ∧ d x ≠ ⊤` using `fun x => ⟨(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (hpos _) _)).ne', ENNReal.ofReal_ne_top⟩`. Establish `hcont' : Continuous mh` using `hcont`. Use `haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SigmaCompactSpace (UA σ X₁.J) := sigmaCompactSpace_of_locallyCompact_secondCountable`.

Use `haveI : SigmaCompactSpace (unip σ X H) := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ`. Use `haveI : SigmaFinite μ₁ := Measure.IsHaarMeasure.sigmaFinite μ₁`. Use `haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN`. Use `haveI : SFinite μ := inferInstance`.

Use `haveI : SFinite μ₁ := inferInstance`. Use `haveI : SFinite μN := inferInstance`. Use `haveI hprod : (μ.prod μ₁).IsHaarMeasure := Measure.prod.instIsHaarMeasure μ μ₁`. Take `⟨ν, hν, hνf⟩` from `GlobalTheory.T.quotient_haar_measure_normal (UA σ X.J) ((AE F E)ˣ × UA σ X₁.J) (GlobalTheory.IwLine.lineStab σ X.J H.x) (unip σ X H) hQc hNc hNQ hnorm mh hcont' (fun x => hmemQ x.1 x.2) (fun q hq => huniq q hq) μN (μ.prod μ₁) d hd_cont hd_mul hd_pos (fun x f hf => GlobalTheory.T. …`. Establish `hKc : IsCompact ((GlobalTheory.StabHaar.stabK (σ` using `σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by`.

Take `⟨C, hC, hsub⟩` from `GlobalTheory.T.relatively_compact_stabilizer F E σ B n X r s hB hX`. Conclude with `hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hX.lat)) hsub`. Use `haveI := GlobalTheory.T.unitary_haar_right_invariant F E σ B n X r s hB hX μG inferInstance`. Take `⟨c, hc0, hcT, hc⟩` from `GlobalTheory.T.haar_measure_closed_compact_decomp (UA σ X.J) μG (GlobalTheory.IwLine.lineStab σ X.J H.x) (GlobalTheory.StabHaar.stabK B X) hQc hKc (GlobalTheory.IwLine.iwasawa B hB hX hH) ν μK`. Use `⟨μN, c, inferInstance, hc0, hcT, fun φ hφ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hc φ hφ]`. Use `congr 1`. Use `lintegral_congr fun k => ?_` and prove the remaining obligations. Rewrite using `[hνf (fun g => φ (g * k.1)) (hφ.comp (measurable_mul_const _))]`. Rewrite using `[lintegral_prod _ ?_]`.

Both sides reduce to the same expression. Use `Measurable.aemeasurable (Measurable.lintegral_prod_right' (f := fun p : ((AE F E)ˣ × UA σ X₁.J) × unip σ X H => φ (p.2.1 * mh p.1 * k.1) * d p.1) ?_)` and prove the remaining obligations. Use `(hφ.comp ?_).mul (hd_meas.comp measurable_fst)` and prove the remaining obligations. Conclude with `((continuous_subtype_val.comp continuous_snd).mul (hcont'.comp continuous_fst) |>.mul continuous_const).measurable`.
-/
theorem intform (B : Base F E) {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {r s r₁ s₁ i₀ i₁ : ℕ} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hX₁ : X₁.IsHerm σ B r₁ s₁) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    (μG : Measure (UA σ X.J)) (μK : Measure (GlobalTheory.StabHaar.stabK (σ := σ) B X)) (μ : Measure (AE F E)ˣ)
    (μ₁ : Measure (UA σ X₁.J)) [μG.IsHaarMeasure] [μK.IsHaarMeasure] [μ.IsHaarMeasure] [μ₁.IsHaarMeasure]
    (m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J) (hm : ∀ l g₀, IsLevi H l g₀ (m l g₀)) :
    ∃ (μN : Measure (unip σ X H)) (c : ENNReal), μN.IsHaarMeasure ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ φ : UA σ X.J → ENNReal, Measurable φ →
        ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ u, φ (u.1 * m l g₀ * k.1) *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μN ∂μ₁ ∂μ ∂μK := by
  classical
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n₁ X₁.J
  obtain ⟨v1, v2, v3, v4⟩ := ideleTop (F := F) (E := E)
  haveI := t1; haveI := t2; haveI := t3; haveI := t4; haveI := u1; haveI := u2; haveI := u3; haveI := u4
  haveI := v1; haveI := v2; haveI := v3; haveI := v4
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨hmul, hcont, hmemQ, huniq, hQc, hNc, hNQ, hnorm⟩ :=
    GlobalTheory.T.levi_embedding_multiplicative F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm
  let mh : ((AE F E)ˣ × UA σ X₁.J) →* UA σ X.J :=
    MonoidHom.mk' (fun x => m x.1 x.2) (fun x y => hmul x.1 y.1 x.2 y.2)
  have hmh : ∀ x, mh x = m x.1 x.2 := fun _ => rfl
  haveI : LocallyCompactSpace (unip σ X H) := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μN : Measure (unip σ X H) := Measure.haar
  let d : (AE F E)ˣ × UA σ X₁.J → ENNReal := fun x => ENNReal.ofReal ((absE F E x.1 : ℝ) ^ (1 - (n : ℝ)))
  have hpos : ∀ l : (AE F E)ˣ, 0 < (absE F E l : ℝ) := fun l => by
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) (map_mul_eq_one (absE F E) (mul_inv_cancel l))
    simp only [NNReal.coe_mul, NNReal.coe_one] at h
    rcases (NNReal.coe_nonneg (absE F E l)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at h; exact absurd h zero_ne_one
  have hd_cont : Continuous d :=
    ENNReal.continuous_ofReal.comp ((NNReal.continuous_coe.comp
      ((GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).comp continuous_fst)).rpow_const
        fun x => Or.inl (hpos x.1).ne')
  have hd_meas : Measurable d := hd_cont.measurable
  have hd_mul : ∀ x y, d (x * y) = d x * d y := fun x y => by
    simp only [d, Prod.fst_mul, map_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (hpos _).le (hpos _).le, ENNReal.ofReal_mul (Real.rpow_nonneg (hpos _).le _)]
  have hd_pos : ∀ x, d x ≠ 0 ∧ d x ≠ ⊤ := fun x =>
    ⟨(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (hpos _) _)).ne', ENNReal.ofReal_ne_top⟩
  have hcont' : Continuous mh := hcont
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (UA σ X₁.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (unip σ X H) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SigmaFinite μ₁ := Measure.IsHaarMeasure.sigmaFinite μ₁
  haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN
  haveI : SFinite μ := inferInstance
  haveI : SFinite μ₁ := inferInstance
  haveI : SFinite μN := inferInstance
  haveI hprod : (μ.prod μ₁).IsHaarMeasure := Measure.prod.instIsHaarMeasure μ μ₁
  obtain ⟨ν, hν, hνf⟩ := GlobalTheory.T.quotient_haar_measure_normal (UA σ X.J) ((AE F E)ˣ × UA σ X₁.J) (GlobalTheory.IwLine.lineStab σ X.J H.x) (unip σ X H)
    hQc hNc hNQ hnorm mh hcont' (fun x => hmemQ x.1 x.2) (fun q hq => huniq q hq) μN (μ.prod μ₁) d hd_cont hd_mul hd_pos
    (fun x f hf => GlobalTheory.T.levi_unipotent_haar_modulus F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm μN inferInstance x.1 x.2 f hf)
  have hKc : IsCompact ((GlobalTheory.StabHaar.stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
    obtain ⟨C, hC, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B n X r s hB hX
    exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hX.lat)) hsub
  haveI := GlobalTheory.T.unitary_haar_right_invariant F E σ B n X r s hB hX μG inferInstance
  obtain ⟨c, hc0, hcT, hc⟩ := GlobalTheory.T.haar_measure_closed_compact_decomp (UA σ X.J) μG (GlobalTheory.IwLine.lineStab σ X.J H.x) (GlobalTheory.StabHaar.stabK B X) hQc hKc
    (GlobalTheory.IwLine.iwasawa B hB hX hH) ν μK
  refine ⟨μN, c, inferInstance, hc0, hcT, fun φ hφ => ?_⟩
  rw [hc φ hφ]
  congr 1
  refine lintegral_congr fun k => ?_
  rw [hνf (fun g => φ (g * k.1)) (hφ.comp (measurable_mul_const _))]
  rw [lintegral_prod _ ?_]
  · rfl
  · refine Measurable.aemeasurable (Measurable.lintegral_prod_right'
      (f := fun p : ((AE F E)ˣ × UA σ X₁.J) × unip σ X H => φ (p.2.1 * mh p.1 * k.1) * d p.1) ?_)
    refine (hφ.comp ?_).mul (hd_meas.comp measurable_fst)
    exact ((continuous_subtype_val.comp continuous_snd).mul (hcont'.comp continuous_fst) |>.mul
      continuous_const).measurable

end GlobalTheory.IwInt
