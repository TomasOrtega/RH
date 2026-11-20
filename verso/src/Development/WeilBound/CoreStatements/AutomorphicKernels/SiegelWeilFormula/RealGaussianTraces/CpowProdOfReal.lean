import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.GramPreimageBox
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.ExistsSchwartzPolyGauss
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.ExistsBumpFourier
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.EqOfBox
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def RealWhitAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ,
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ),
    IsPlaces σ ψ θ l → ∀ ε fr, IsFrames J θ ε fr → ∀ (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    SdW F E σ M J (Ainf F) (psiInf F ψ) n μ → SdHerm F E σ (Ainf F) (psiInf F ψ) n ν →
    IsSchwartzInf (phiInf θ l fr g P) ∧
  ∀ gi : HermR (Ainf F) σ n → ℂ,
    IsContDensityOn μ (gramR (Ainf F) σ J) Subtype.val ν
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} (phiInf θ l fr g P) gi →
  ∀ T : HermR (Ainf F) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W (((M : ℂ) - n) / 2) = gi T ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z) ν ∧
      W z = ∫ b, whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z b ∂ν

def fw {M n : ℕ} (ε : Fin M → Bool) (l : ℝ) (P : PX M n) (β : WR.E n) (w : ℂ) (y : WR.E n) : ℂ :=
  ((WR.dP y : ℝ) : ℂ) ^ (-w) * secN ε (2 * Real.pi * |l|) (2 * Real.pi * l) P (herm y) * WR.chr (2 * Real.pi * l) β y

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ => hr i), ih]`.
-/
theorem cpow_prod_ofReal {ι : Type} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (w : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ w = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ => hr i), ih]

/- English proof (translation)
Rewrite using `[NNReal.smul_def, Complex.real_smul]`.
-/
theorem nnreal_smul_eq {c : ℝ≥0} (z : ℂ) : c • z = (c : ℂ) * z := by
  rw [NNReal.smul_def, Complex.real_smul]

/- English proof (translation)
Use `haveI : IsTotallyReal F := hCM.1`. Use `haveI := secondCountable_tens (F := F) (E := E)`. Use `haveI := borel_tens (F := F) (E := E)`. Use `haveI := borel_herm (F := F) (E := E) σ n`. Establish `hme : MeasurableEmbedding (eC : (Fin n → Fin M → Ainf F ⊗[F] E) → (ι → Fin M → Fin n → ℂ))` using `eC.toHomeomorph.measurableEmbedding`.

Unfold `jtR`. Repeatedly rewrite using `[phi_mul_psi σ hCM ψ θ l hP J ε fr hfr g P b, ← heC]`. Rewrite using `[← hme.integral_map (fun x => ∏ i, (evX (P i) (x i) * gs (2 * Real.pi * |l i|) (x i) * Complex.exp (Complex.I * ((2 * Real.pi * l i : ℝ) : ℂ) * (herm (ybAll σ θ g b i) * gramX (ε i) (x i)).trace))), hcμ, integral_smul_nnreal_measure, nnreal_smul_eq]`. Use `congr 1`. Conclude with `integral_fintype_prod_volume_eq_prod (f := fun i x => evX (P i) x * gs (2 * Real.pi * |l i|) x * Complex.exp (Complex.I * ((2 * Real.pi * l i : ℝ) : ℂ) * (herm (ybAll σ θ g b i) * gramX (ε i) x).trace))`.
-/
theorem jt_eq (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (eC : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ))
    (heC : ⇑eC = crdAll θ fr g) (cμ : ℝ≥0) (hcμ : μ.map eC = cμ • volume) (b : HermR (Ainf F) σ n) :
    jtR (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) b =
      (cμ : ℂ) * ∏ i, secN (ε i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) (P i) (herm (ybAll σ θ g b i)) := by
  classical
  haveI : IsTotallyReal F := hCM.1
  haveI := secondCountable_tens (F := F) (E := E)
  haveI := borel_tens (F := F) (E := E)
  haveI := borel_herm (F := F) (E := E) σ n
  have hme : MeasurableEmbedding (eC : (Fin n → Fin M → Ainf F ⊗[F] E) → (ι → Fin M → Fin n → ℂ)) :=
    eC.toHomeomorph.measurableEmbedding
  unfold jtR
  simp_rw [phi_mul_psi σ hCM ψ θ l hP J ε fr hfr g P b, ← heC]
  rw [← hme.integral_map (fun x => ∏ i, (evX (P i) (x i) * gs (2 * Real.pi * |l i|) (x i) *
      Complex.exp (Complex.I * ((2 * Real.pi * l i : ℝ) : ℂ) * (herm (ybAll σ θ g b i) * gramX (ε i) (x i)).trace))),
    hcμ, integral_smul_nnreal_measure, nnreal_smul_eq]
  congr 1
  exact integral_fintype_prod_volume_eq_prod (f := fun i x => evX (P i) x * gs (2 * Real.pi * |l i|) x *
      Complex.exp (Complex.I * ((2 * Real.pi * l i : ℝ) : ℂ) * (herm (ybAll σ θ g b i) * gramX (ε i) x).trace))

/- English proof (translation)
Unfold `whI`. Rewrite using `[nuInf_eq σ hCM ψ θ l hP g b, jt_eq σ hCM ψ θ l hP J ε fr hfr g P μ eC heC cμ hcμ b, psi_neg_trPair σ hCM ψ θ l hP g T b, cpow_prod_ofReal _ _ (fun i => (WR.I.dP_pos _).le)]`. Simplify using `only [fw, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem whI_eq (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (eC : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ))
    (heC : ⇑eC = crdAll θ fr g) (cμ : ℝ≥0) (hcμ : μ.map eC = cμ • volume) (T b : HermR (Ainf F) σ n) (z : ℂ) :
    whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z b =
      (cμ : ℂ) * ∏ i, fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - ((M : ℂ) - n) / 2) (ybAll σ θ g b i) := by
  unfold whI
  rw [nuInf_eq σ hCM ψ θ l hP g b, jt_eq σ hCM ψ θ l hP J ε fr hfr g P μ eC heC cμ hcμ b,
    psi_neg_trPair σ hCM ψ θ l hP g T b,
    cpow_prod_ofReal _ _ (fun i => (WR.I.dP_pos _).le)]
  simp only [fw, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Use `haveI : IsTotallyReal F := hCM.1`. Use `haveI := secondCountable_tens (F := F) (E := E)`. Use `haveI := borel_tens (F := F) (E := E)`. Use `haveI := borel_herm (F := F) (E := E) σ n`. Establish `hme : MeasurableEmbedding (eb : HermR (Ainf F) σ n → (ι → WR.E n))` using `eb.toHomeomorph.measurableEmbedding`.

Use `set G : (ι → WR.E n) → ℂ := fun y => (cμ : ℂ) * ∏ i, fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - ((M : ℂ) - n) / 2) (y i) with hG`. Establish `hfun : whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z = G ∘ eb`. Use function extensionality and compare the values at `b`. Rewrite using `[whI_eq σ hCM ψ θ l hP J ε fr hfr g P μ eC heC cμ hcμ T b z, Function.comp_apply, hG, heb]`. Establish `hGint : Integrable G (volume : Measure (ι → WR.E n))` using `(Integrable.fintype_prod (μ := fun _ => (volume : Measure (WR.E n))) hint).const_mul _`.

Rewrite using `[hfun]`. Use `⟨hme.integrable_map_iff.1 (by rw [hcb]; exact hGint.smul_measure_nnreal), ?_⟩` and prove the remaining obligations. Rewrite using `[show (∫ b, (G ∘ eb) b ∂ν) = ∫ b, G (eb b) ∂ν from rfl, ← hme.integral_map G, hcb, integral_smul_nnreal_measure, nnreal_smul_eq, hG, integral_const_mul, integral_fintype_prod_volume_eq_prod (f := fun i y => fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - ((M : ℂ) - n) / 2) y)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_whI (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (eC : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ))
    (heC : ⇑eC = crdAll θ fr g) (cμ : ℝ≥0) (hcμ : μ.map eC = cμ • volume) (ν : Measure (HermR (Ainf F) σ n))
    (eb : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n)) (heb : ⇑eb = ybAll σ θ g) (cb : ℝ≥0) (hcb : ν.map eb = cb • volume)
    (T : HermR (Ainf F) σ n) (z : ℂ)
    (hint : ∀ i, Integrable (fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - ((M : ℂ) - n) / 2))) :
    Integrable (whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z) ν ∧
      ∫ b, whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z b ∂ν =
        (cb : ℂ) * (cμ : ℂ) * ∏ i, ∫ y, fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - ((M : ℂ) - n) / 2) y := by
  classical
  haveI : IsTotallyReal F := hCM.1
  haveI := secondCountable_tens (F := F) (E := E)
  haveI := borel_tens (F := F) (E := E)
  haveI := borel_herm (F := F) (E := E) σ n
  have hme : MeasurableEmbedding (eb : HermR (Ainf F) σ n → (ι → WR.E n)) := eb.toHomeomorph.measurableEmbedding
  set G : (ι → WR.E n) → ℂ := fun y => (cμ : ℂ) * ∏ i, fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - ((M : ℂ) - n) / 2) (y i)
    with hG
  have hfun : whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z = G ∘ eb := by
    funext b
    rw [whI_eq σ hCM ψ θ l hP J ε fr hfr g P μ eC heC cμ hcμ T b z, Function.comp_apply, hG, heb]
  have hGint : Integrable G (volume : Measure (ι → WR.E n)) :=
    (Integrable.fintype_prod (μ := fun _ => (volume : Measure (WR.E n))) hint).const_mul _
  rw [hfun]
  refine ⟨hme.integrable_map_iff.1 (by rw [hcb]; exact hGint.smul_measure_nnreal), ?_⟩
  rw [show (∫ b, (G ∘ eb) b ∂ν) = ∫ b, G (eb b) ∂ν from rfl, ← hme.integral_map G, hcb, integral_smul_nnreal_measure,
    nnreal_smul_eq, hG, integral_const_mul,
    integral_fintype_prod_volume_eq_prod (f := fun i y => fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - ((M : ℂ) - n) / 2) y)]
  ring

/- English proof (translation)
Establish `h : {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} = ⋂ i, {S : HermR (Ainf F) σ n | ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).det ≠ 0}`. Use extensionality with `S`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Rewrite using `[isUnit_iff_th σ ψ θ l hP]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_ne_fun ((continuous_subtype_val.matrix_map (hP.cont i)).matrix_det) continuous_const`.
-/
theorem isOpen_unitDet (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) (n : ℕ) :
    IsOpen {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
  have h : {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} =
      ⋂ i, {S : HermR (Ainf F) σ n | ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).det ≠ 0} := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [isUnit_iff_th σ ψ θ l hP]
    refine forall_congr' fun i => ?_
    rw [RingHom.map_det]
    rfl
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun
    ((continuous_subtype_val.matrix_map (hP.cont i)).matrix_det) continuous_const

/- English proof (translation)
Use `haveI : IsTotallyReal F := hCM.1`. Use `haveI := secondCountable_tens (F := F) (E := E)`. Use `haveI := borel_tens (F := F) (E := E)`. Use `haveI := borel_herm (F := F) (E := E) σ n`. Establish `hmeC : MeasurableEmbedding (eC : (Fin n → Fin M → Ainf F ⊗[F] E) → (ι → Fin M → Fin n → ℂ))` using `eC.toHomeomorph.measurableEmbedding`.

Establish `hmeg : MeasurableEmbedding (eg : HermR (Ainf F) σ n → (ι → WR.E n))` using `eg.toHomeomorph.measurableEmbedding`. Use `haveI hsf1 : SigmaFinite (volume : Measure (Fin M → Fin n → ℂ)) := by`. Establish `: (volume : Measure (Fin M → Fin n → ℂ)) = Measure.pi fun _ => volume` using `rfl`. Rewrite using `[this]`. Use `infer_instance`.

Use `haveI hsf2 : SigmaFinite (volume : Measure (WR.E n)) := by`. Establish `: (volume : Measure (WR.E n)) = Measure.pi fun _ => volume` using `rfl`. Rewrite using `[this]`. Use `infer_instance`. Use `set A : ι → Set (Fin M → Fin n → ℂ) := fun i => gramX (ε i) ⁻¹' (herm '' K i) with hA`.

Establish `hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' (eg ⁻¹' Set.univ.pi K)) = eC ⁻¹' Set.univ.pi A`. Rewrite using `[heg, heC]`. Conclude with `gram_preimage_box σ hCM ψ θ l hP J hJ ε fr hfr g K`. Use `set F0 : (ι → Fin M → Fin n → ℂ) → ℂ := fun x => ∏ i, (evX (P i) (x i) * gs (2 * Real.pi * |l i|) (x i)) with hF0`. Establish `hphi : phiInf θ l fr g P = F0 ∘ eC`.

Use function extensionality and compare the values at `Y`. Rewrite using `[Function.comp_apply, hF0, heC]`. Both sides reduce to the same expression. Establish `hL : ∫ Y in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' (eg ⁻¹' Set.univ.pi K)), phiInf θ l fr g P Y ∂μ = (cμ : ℂ) * ∏ i, ∫ y in K i, gg i y`. Rewrite using `[hset, hphi, show (∫ Y in eC ⁻¹' Set.univ.pi A, (F0 ∘ eC) Y ∂μ) = ∫ Y in eC ⁻¹' Set.univ.pi A, F0 (eC Y) ∂μ from rfl, ← hmeC.setIntegral_map, hcμ, Measure.restrict_smul, integral_smul_nnreal_measure, nnreal_smul_eq]`.

Use `congr 1`. Establish `hv : (volume : Measure (ι → Fin M → Fin n → ℂ)) = Measure.pi fun _ => volume` using `rfl`. Rewrite using `[hv, Measure.restrict_pi_pi, hF0, integral_fintype_prod_eq_prod (f := fun i x => evX (P i) x * gs (2 * Real.pi * |l i|) x)]`. Conclude with `Finset.prod_congr rfl fun i _ => hgg i (K i) (hK i) (hKd i)`. Establish `hR : ∫ S in eg ⁻¹' Set.univ.pi K, c * ∏ i, gg i (eg S i) ∂ν = (cg : ℂ) * (c * ∏ i, ∫ y in K i, gg i y)`.

Rewrite using `[← hmeg.setIntegral_map (fun y => c * ∏ i, gg i (y i)), hcg, Measure.restrict_smul, integral_smul_nnreal_measure, nnreal_smul_eq, integral_const_mul]`. Establish `hv : (volume : Measure (ι → WR.E n)) = Measure.pi fun _ => volume` using `rfl`. Rewrite using `[hv, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (f := fun i y => gg i y)]`. Rewrite using `[hL, hR, ← mul_assoc, hc]`.
-/
theorem dens_box (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr)
    (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (eC : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ))
    (heC : ⇑eC = crdAll θ fr g) (cμ : ℝ≥0) (hcμ : μ.map eC = cμ • volume) (ν : Measure (HermR (Ainf F) σ n))
    (eg : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n)) (heg : ⇑eg = ygAll σ θ g) (cg : ℝ≥0) (hcg : ν.map eg = cg • volume)
    (gg : ι → WR.E n → ℂ)
    (hgg : ∀ i, ∀ S : Set (WR.E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
      ∫ x in gramX (ε i) ⁻¹' (herm '' S), evX (P i) x * gs (2 * Real.pi * |l i|) x = ∫ y in S, gg i y)
    (K : ι → Set (WR.E n)) (hK : ∀ i, IsCompact (K i)) (hKd : ∀ i, K i ⊆ {y | (herm y).det ≠ 0}) (c : ℂ)
    (hc : (cg : ℂ) * c = cμ) :
    ∫ Y in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' (eg ⁻¹' Set.univ.pi K)), phiInf θ l fr g P Y ∂μ =
      ∫ S in eg ⁻¹' Set.univ.pi K, c * ∏ i, gg i (eg S i) ∂ν := by
  classical
  haveI : IsTotallyReal F := hCM.1
  haveI := secondCountable_tens (F := F) (E := E)
  haveI := borel_tens (F := F) (E := E)
  haveI := borel_herm (F := F) (E := E) σ n
  have hmeC : MeasurableEmbedding (eC : (Fin n → Fin M → Ainf F ⊗[F] E) → (ι → Fin M → Fin n → ℂ)) :=
    eC.toHomeomorph.measurableEmbedding
  have hmeg : MeasurableEmbedding (eg : HermR (Ainf F) σ n → (ι → WR.E n)) := eg.toHomeomorph.measurableEmbedding
  haveI hsf1 : SigmaFinite (volume : Measure (Fin M → Fin n → ℂ)) := by
    have : (volume : Measure (Fin M → Fin n → ℂ)) = Measure.pi fun _ => volume := rfl
    rw [this]; infer_instance
  haveI hsf2 : SigmaFinite (volume : Measure (WR.E n)) := by
    have : (volume : Measure (WR.E n)) = Measure.pi fun _ => volume := rfl
    rw [this]; infer_instance
  set A : ι → Set (Fin M → Fin n → ℂ) := fun i => gramX (ε i) ⁻¹' (herm '' K i) with hA
  have hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' (eg ⁻¹' Set.univ.pi K)) = eC ⁻¹' Set.univ.pi A := by
    rw [heg, heC]; exact gram_preimage_box σ hCM ψ θ l hP J hJ ε fr hfr g K
  set F0 : (ι → Fin M → Fin n → ℂ) → ℂ := fun x => ∏ i, (evX (P i) (x i) * gs (2 * Real.pi * |l i|) (x i)) with hF0
  have hphi : phiInf θ l fr g P = F0 ∘ eC := by
    funext Y; rw [Function.comp_apply, hF0, heC]; rfl
  have hL : ∫ Y in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' (eg ⁻¹' Set.univ.pi K)), phiInf θ l fr g P Y ∂μ =
      (cμ : ℂ) * ∏ i, ∫ y in K i, gg i y := by
    rw [hset, hphi, show (∫ Y in eC ⁻¹' Set.univ.pi A, (F0 ∘ eC) Y ∂μ) = ∫ Y in eC ⁻¹' Set.univ.pi A, F0 (eC Y) ∂μ from rfl,
      ← hmeC.setIntegral_map, hcμ, Measure.restrict_smul, integral_smul_nnreal_measure, nnreal_smul_eq]
    congr 1
    have hv : (volume : Measure (ι → Fin M → Fin n → ℂ)) = Measure.pi fun _ => volume := rfl
    rw [hv, Measure.restrict_pi_pi, hF0,
      integral_fintype_prod_eq_prod (f := fun i x => evX (P i) x * gs (2 * Real.pi * |l i|) x)]
    exact Finset.prod_congr rfl fun i _ => hgg i (K i) (hK i) (hKd i)
  have hR : ∫ S in eg ⁻¹' Set.univ.pi K, c * ∏ i, gg i (eg S i) ∂ν = (cg : ℂ) * (c * ∏ i, ∫ y in K i, gg i y) := by
    rw [← hmeg.setIntegral_map (fun y => c * ∏ i, gg i (y i)), hcg, Measure.restrict_smul, integral_smul_nnreal_measure,
      nnreal_smul_eq, integral_const_mul]
    have hv : (volume : Measure (ι → WR.E n)) = Measure.pi fun _ => volume := rfl
    rw [hv, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (f := fun i y => gg i y)]
  rw [hL, hR, ← mul_assoc, hc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n ψ hψ ι _ θ l hP ε fr hfr g P μ ν hμ hν`. Use `haveI : IsTotallyReal F := hCM.1`. Use `haveI := secondCountable_tens (F := F) (E := E)`. Use `haveI := borel_tens (F := F) (E := E)`. Use `haveI := borel_herm (F := F) (E := E) σ n`.

Take `⟨eC, heC⟩` from `exists_crdHomeo σ hCM ψ θ l hP fr g`. Take `⟨eb, heb⟩` from `exists_ybHomeo σ hCM ψ θ l hP g`. Take `⟨eg, heg⟩` from `exists_ygHomeo σ hCM ψ θ l hP g`. Use `haveI := haar_volE ι n`. Use `haveI := haar_volW ι M n`.

Use `haveI : μ.IsAddHaarMeasure := hμ.1`. Use `haveI : ν.IsAddHaarMeasure := hν.1`. Take `⟨cμ, hcμ0, hcμ⟩` from `exists_map_eq_smul (volume : Measure (ι → Fin M → Fin n → ℂ)) μ eC`. Take `⟨cb, hcb0, hcb⟩` from `exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eb`. Take `⟨cg, hcg0, hcg⟩` from `exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eg`.

Establish `hl : ∀ i, l i ≠ 0` using `hP.ne`. Establish `hnorm : ((cb : ℝ) * cg) = ∏ i, |l i| ^ (n ^ 2)`. Use `selfDual_const l hl ν (fun S T => psiInf F ψ (pairHerm (Ainf F) σ n S T)) hν eb.toHomeomorph eg.toHomeomorph (map_zero eb) (fun S T => ?_) (fun S T => by rw [pairHerm_comm]) cb cg hcb hcg` and prove the remaining obligations. Use `psi_pairHerm σ hCM ψ θ l hP g S T` as an intermediate fact. Rewrite `this` using `[← heb, ← heg]`.

Conclude with `this`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `exists_schwartz_polyGauss (fun i => 2 * Real.pi * |l i|) (fun i => by have := abs_pos.2 (hl i); positivity) P`. Establish `: phiInf θ l fr g P = fun X => f (eC X)`. Use function extensionality and compare the values at `X`.

Rewrite using `[hf, heC]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `isSchwartzInf_comp eC f`. Introduce `gi hgi T hT`.

Establish `hw : ∀ i, ∃ gg : WR.E n → ℂ, ContinuousOn gg {y | (herm y).det ≠ 0} ∧ (∀ S : Set (WR.E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} → ∫ x in gramX (ε i) ⁻¹' (herm '' S), evX (P i) x * gs (2 * Real.pi * |l i|) x = ∫ y in S, gg y) ∧ ∀ β : WR.E n, (herm β).det ≠ 0 → ∃ W : ℂ → ℂ, Dif …`. Introduce `i`. Establish `hc : 0 < 2 * Real.pi * |l i|` using `by have := abs_pos.2 (hl i); positivity`. Use `hWR M n (ε i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) hc ?_ (P i)` and prove the remaining obligations. Break down `le_or_gt 0 (l i) with h | h` into its components or cases.

Use `left`. Rewrite using `[abs_of_nonneg h]`. Use `right`. Rewrite using `[abs_of_neg h]`. Expand and normalize the polynomial expressions, which then agree.

Use `choose gg hggc hggd hggW using hw`. Establish `hβ : ∀ i, (herm (ygAll σ θ g T i)).det ≠ 0` using `det_herm_ygAll σ hCM ψ θ l hP g T hT`. Use `choose Wi hWid hWrest using fun i => hggW i (ygAll σ θ g T i) (hβ i)`. Use `choose σ₀ hσ₀ using fun i => (hWrest i).1`. Establish `hWi0` using `fun i => (hWrest i).2`.

Use `set s0 : ℂ := ((M : ℂ) - n) / 2 with hs0`. Use `set c : ℂ := (cb : ℂ) * (cμ : ℂ) * ∏ i, (((|l i|⁻¹) ^ (n ^ 2) : ℝ) : ℂ) with hcdef`. Establish `hcc : (cg : ℂ) * c = cμ`. Establish `h1 : ((cb : ℝ) * cg) * ∏ i, (|l i|⁻¹) ^ (n ^ 2) = 1`. Rewrite using `[hnorm, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, mul_inv_cancel₀ (abs_pos.2 (hl i)).ne', one_pow]`. Establish `h2 : ((((cb : ℝ) * cg) * ∏ i, (|l i|⁻¹) ^ (n ^ 2) : ℝ) : ℂ) = 1` using `by rw [h1]; simp`. Rewrite using `[hcdef]`. Move the coercions through the operations in `at h2 ⊢`.

Take the linear combination `(cμ : ℂ) * h2`. Establish `hB : IsOpen {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}` using `isOpen_unitDet σ ψ θ l hP n`. Use `haveI : T2Space (HermR (Ainf F) σ n) := eg.toHomeomorph.symm.t2Space`. Establish `hGd : ContinuousOn (fun S : HermR (Ainf F) σ n => c * ∏ i, gg i (eg S i)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}`. Use `continuousOn_const.mul (continuousOn_finset_prod _ fun i _ => ?_)` and prove the remaining obligations.

Use `(hggc i).comp ((continuous_apply i).comp eg.continuous).continuousOn fun S hS => ?_` and prove the remaining obligations. Use `show (herm (eg S i)).det ≠ 0`. Rewrite using `[heg]`. Conclude with `det_herm_ygAll σ hCM ψ θ l hP g S hS i`. Establish `hval : gi T = c * ∏ i, gg i (eg T i)`.

Use `eq_of_box ν _ hB gi _ hgi.1 hGd T hT fun U hU => ?_` and prove the remaining obligations. Establish `hU' : eg '' (U ∩ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}) ∈ nhds (eg T)` using `eg.toHomeomorph.isOpenMap.image_mem_nhds (Filter.inter_mem hU (hB.mem_nhds hT))`. Take `⟨r, hr, hball⟩` from `Metric.mem_nhds_iff.1 hU'`. Establish `hr2 : 0 < r / 2` using `by positivity`. Use `set K : ι → Set (WR.E n) := fun i => Metric.closedBall (eg T i) (r / 2) with hK`.

Establish `hpi : Set.univ.pi K = Metric.closedBall (eg T) (r / 2)` using `(closedBall_pi _ hr2.le).symm`. Establish `hsub : ∀ x, eg x ∈ Set.univ.pi K → x ∈ U ∧ IsUnit (x : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det`. Introduce `x hx`. Rewrite `hx` using `[hpi]`. Take `⟨y, hy, hxy⟩` from `hball (Metric.closedBall_subset_ball (by linarith) hx)`.

Rewrite using `[← eg.injective hxy]`. Conclude with `hy`. Establish `hKd : ∀ i, K i ⊆ {y | (herm y).det ≠ 0}`. Introduce `i y hy`. Establish `hz : eg (eg.symm (Function.update (eg T) i y)) ∈ Set.univ.pi K`.

Rewrite using `[ContinuousAddEquiv.apply_symm_apply]`. Introduce `j _`. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Simplify using `using hy`. Simplify using `only [Function.update_of_ne hj, hK]`.

Conclude with `Metric.mem_closedBall_self hr2.le`. Establish `h2` using `det_herm_ygAll σ hCM ψ θ l hP g _ (hsub _ hz).2 i`. Rewrite `h2` using `[← heg, ContinuousAddEquiv.apply_symm_apply]`. Simplify using `using h2`. Establish `hKc : ∀ i, IsCompact (K i)` using `fun i => isCompact_closedBall _ _`.

Establish `hSc : IsCompact (eg ⁻¹' Set.univ.pi K)`. Rewrite using `[hpi]`. Conclude with `eg.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)`. Establish `hSB : eg ⁻¹' Set.univ.pi K ⊆ {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}` using `fun x hx => (hsub x hx).2`. Use `⟨eg ⁻¹' Set.univ.pi K, hSc, fun x hx => (hsub x hx).1, hSB, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hpi]`. Conclude with `eg.continuous.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr2)`. Rewrite using `[← hgi.2 _ hSc hSB]`. Conclude with `dens_box σ hCM ψ θ l hP J hJ ε fr hfr g P μ eC heC cμ hcμ ν eg heg cg hcg gg hggd K hKc hKd c hcc`. Use `⟨fun z => (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0), ?_, ?_, ((M : ℝ) - n) / 2 + ∑ i, |σ₀ i|, fun z hz => ?_⟩` and prove the remaining obligations.

Use `(differentiable_const _).mul ?_` and prove the remaining obligations. Use `Differentiable.finset_prod (u := Finset.univ) (f := fun i z => Wi i (z - s0)) (fun i _ => (hWid i).comp (differentiable_id.sub_const s0))` as an intermediate fact. Rewrite `this` using `[Finset.prod_fn]`. Conclude with `this`. Use `show (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (s0 - s0) = gi T`.

Rewrite using `[hval, sub_self]`. Simplify using `only [hWi0]`. Rewrite using `[hcdef]`. Simplify using `only [mul_assoc]`. Use `congr 2`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h2 : 2 * Real.pi / |2 * (Real.pi * l i)| = |l i|⁻¹`. Rewrite using `[← mul_assoc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h2, heg]`. Establish `hzi : ∀ i, σ₀ i < (z - s0).re`. Introduce `i`. Establish `h1 : (z - s0).re = z.re - ((M : ℝ) - n) / 2`. Rewrite using `[hs0]`.

Simplify using the standard rewrite rules. Establish `h2 : σ₀ i ≤ ∑ j, |σ₀ j|` using `(le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₀ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))`. Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hint : ∀ i, Integrable (fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - s0))` using `fun i => (hσ₀ i _ (hzi i)).1`.

Take `⟨h1, h2⟩` from `integral_whI σ hCM ψ θ l hP J ε fr hfr g P μ eC heC cμ hcμ ν eb heb cb hcb T z hint`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Use `show (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0) = _`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun i _ => (hσ₀ i _ (hzi i)).2`.
-/
theorem realWhitAll_of (hWR : WR.WRSt) : RealWhitAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ hψ ι _ θ l hP ε fr hfr g P μ ν hμ hν
  classical
  haveI : IsTotallyReal F := hCM.1
  haveI := secondCountable_tens (F := F) (E := E)
  haveI := borel_tens (F := F) (E := E)
  haveI := borel_herm (F := F) (E := E) σ n
  obtain ⟨eC, heC⟩ := exists_crdHomeo σ hCM ψ θ l hP fr g
  obtain ⟨eb, heb⟩ := exists_ybHomeo σ hCM ψ θ l hP g
  obtain ⟨eg, heg⟩ := exists_ygHomeo σ hCM ψ θ l hP g
  haveI := haar_volE ι n
  haveI := haar_volW ι M n
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨cμ, hcμ0, hcμ⟩ := exists_map_eq_smul (volume : Measure (ι → Fin M → Fin n → ℂ)) μ eC
  obtain ⟨cb, hcb0, hcb⟩ := exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eb
  obtain ⟨cg, hcg0, hcg⟩ := exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eg
  have hl : ∀ i, l i ≠ 0 := hP.ne
  have hnorm : ((cb : ℝ) * cg) = ∏ i, |l i| ^ (n ^ 2) := by
    refine selfDual_const l hl ν (fun S T => psiInf F ψ (pairHerm (Ainf F) σ n S T)) hν eb.toHomeomorph
      eg.toHomeomorph (map_zero eb) (fun S T => ?_) (fun S T => by rw [pairHerm_comm]) cb cg hcb hcg
    have := psi_pairHerm σ hCM ψ θ l hP g S T
    rw [← heb, ← heg] at this
    exact this
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf⟩ := exists_schwartz_polyGauss (fun i => 2 * Real.pi * |l i|)
      (fun i => by have := abs_pos.2 (hl i); positivity) P
    have : phiInf θ l fr g P = fun X => f (eC X) := by
      funext X; rw [hf, heC]; rfl
    rw [this]; exact isSchwartzInf_comp eC f
  intro gi hgi T hT

  have hw : ∀ i, ∃ gg : WR.E n → ℂ, ContinuousOn gg {y | (herm y).det ≠ 0} ∧
      (∀ S : Set (WR.E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
        ∫ x in gramX (ε i) ⁻¹' (herm '' S), evX (P i) x * gs (2 * Real.pi * |l i|) x = ∫ y in S, gg y) ∧
      ∀ β : WR.E n, (herm β).det ≠ 0 → ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
        (∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
          Integrable (fun y => ((WR.dP y : ℝ) : ℂ) ^ (-z) * secN (ε i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) (P i) (herm y) *
            WR.chr (2 * Real.pi * l i) β y) ∧
          W z = ∫ y, ((WR.dP y : ℝ) : ℂ) ^ (-z) * secN (ε i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) (P i) (herm y) *
            WR.chr (2 * Real.pi * l i) β y) ∧
        W 0 = ((2 * Real.pi / |2 * Real.pi * l i|) ^ (n ^ 2) : ℝ) * gg β := by
    intro i
    have hc : 0 < 2 * Real.pi * |l i| := by have := abs_pos.2 (hl i); positivity
    refine hWR M n (ε i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) hc ?_ (P i)
    rcases le_or_gt 0 (l i) with h | h
    · left; rw [abs_of_nonneg h]
    · right; rw [abs_of_neg h]; ring
  choose gg hggc hggd hggW using hw
  have hβ : ∀ i, (herm (ygAll σ θ g T i)).det ≠ 0 := det_herm_ygAll σ hCM ψ θ l hP g T hT
  choose Wi hWid hWrest using fun i => hggW i (ygAll σ θ g T i) (hβ i)
  choose σ₀ hσ₀ using fun i => (hWrest i).1
  have hWi0 := fun i => (hWrest i).2
  set s0 : ℂ := ((M : ℂ) - n) / 2 with hs0
  set c : ℂ := (cb : ℂ) * (cμ : ℂ) * ∏ i, (((|l i|⁻¹) ^ (n ^ 2) : ℝ) : ℂ) with hcdef
  have hcc : (cg : ℂ) * c = cμ := by
    have h1 : ((cb : ℝ) * cg) * ∏ i, (|l i|⁻¹) ^ (n ^ 2) = 1 := by
      rw [hnorm, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← mul_pow, mul_inv_cancel₀ (abs_pos.2 (hl i)).ne', one_pow]
    have h2 : ((((cb : ℝ) * cg) * ∏ i, (|l i|⁻¹) ^ (n ^ 2) : ℝ) : ℂ) = 1 := by rw [h1]; simp
    rw [hcdef]
    push_cast at h2 ⊢
    linear_combination (cμ : ℂ) * h2
  have hB : IsOpen {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} :=
    isOpen_unitDet σ ψ θ l hP n
  haveI : T2Space (HermR (Ainf F) σ n) := eg.toHomeomorph.symm.t2Space
  have hGd : ContinuousOn (fun S : HermR (Ainf F) σ n => c * ∏ i, gg i (eg S i))
      {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
    refine continuousOn_const.mul (continuousOn_finset_prod _ fun i _ => ?_)
    refine (hggc i).comp ((continuous_apply i).comp eg.continuous).continuousOn fun S hS => ?_
    show (herm (eg S i)).det ≠ 0
    rw [heg]; exact det_herm_ygAll σ hCM ψ θ l hP g S hS i
  have hval : gi T = c * ∏ i, gg i (eg T i) := by
    refine eq_of_box ν _ hB gi _ hgi.1 hGd T hT fun U hU => ?_
    have hU' : eg '' (U ∩ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}) ∈ nhds (eg T) :=
      eg.toHomeomorph.isOpenMap.image_mem_nhds (Filter.inter_mem hU (hB.mem_nhds hT))
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU'
    have hr2 : 0 < r / 2 := by positivity
    set K : ι → Set (WR.E n) := fun i => Metric.closedBall (eg T i) (r / 2) with hK
    have hpi : Set.univ.pi K = Metric.closedBall (eg T) (r / 2) := (closedBall_pi _ hr2.le).symm
    have hsub : ∀ x, eg x ∈ Set.univ.pi K → x ∈ U ∧ IsUnit (x : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det := by
      intro x hx
      rw [hpi] at hx
      obtain ⟨y, hy, hxy⟩ := hball (Metric.closedBall_subset_ball (by linarith) hx)
      rw [← eg.injective hxy]; exact hy
    have hKd : ∀ i, K i ⊆ {y | (herm y).det ≠ 0} := by
      intro i y hy
      have hz : eg (eg.symm (Function.update (eg T) i y)) ∈ Set.univ.pi K := by
        rw [ContinuousAddEquiv.apply_symm_apply]
        intro j _
        rcases eq_or_ne j i with rfl | hj
        · simpa using hy
        · simp only [Function.update_of_ne hj, hK]; exact Metric.mem_closedBall_self hr2.le
      have h2 := det_herm_ygAll σ hCM ψ θ l hP g _ (hsub _ hz).2 i
      rw [← heg, ContinuousAddEquiv.apply_symm_apply] at h2
      simpa using h2
    have hKc : ∀ i, IsCompact (K i) := fun i => isCompact_closedBall _ _
    have hSc : IsCompact (eg ⁻¹' Set.univ.pi K) := by
      rw [hpi]; exact eg.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)
    have hSB : eg ⁻¹' Set.univ.pi K ⊆
        {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} :=
      fun x hx => (hsub x hx).2
    refine ⟨eg ⁻¹' Set.univ.pi K, hSc, fun x hx => (hsub x hx).1, hSB, ?_, ?_⟩
    · rw [hpi]
      exact eg.continuous.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr2)
    · rw [← hgi.2 _ hSc hSB]
      exact dens_box σ hCM ψ θ l hP J hJ ε fr hfr g P μ eC heC cμ hcμ ν eg heg cg hcg gg hggd K hKc hKd c hcc
  refine ⟨fun z => (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0), ?_, ?_, ((M : ℝ) - n) / 2 + ∑ i, |σ₀ i|,
    fun z hz => ?_⟩
  · refine (differentiable_const _).mul ?_
    have := Differentiable.finset_prod (u := Finset.univ) (f := fun i z => Wi i (z - s0))
      (fun i _ => (hWid i).comp (differentiable_id.sub_const s0))
    rw [Finset.prod_fn] at this
    exact this
  · show (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (s0 - s0) = gi T
    rw [hval, sub_self]
    simp only [hWi0]
    rw [hcdef]
    simp only [mul_assoc]
    congr 2
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 : 2 * Real.pi / |2 * (Real.pi * l i)| = |l i|⁻¹ := by
      rw [← mul_assoc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      field_simp
    rw [h2, heg]
  · have hzi : ∀ i, σ₀ i < (z - s0).re := by
      intro i
      have h1 : (z - s0).re = z.re - ((M : ℝ) - n) / 2 := by
        rw [hs0]; simp
      have h2 : σ₀ i ≤ ∑ j, |σ₀ j| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₀ j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i))
      rw [h1]; linarith
    have hint : ∀ i, Integrable (fw (ε i) (l i) (P i) (ygAll σ θ g T i) (z - s0)) :=
      fun i => (hσ₀ i _ (hzi i)).1
    obtain ⟨h1, h2⟩ := integral_whI σ hCM ψ θ l hP J ε fr hfr g P μ eC heC cμ hcμ ν eb heb cb hcb T z hint
    refine ⟨h1, ?_⟩
    rw [h2]
    show (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0) = _
    congr 1
    exact Finset.prod_congr rfl fun i _ => (hσ₀ i _ (hzi i)).2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ ι _ θ l hP ε fr hfr g P μ ν hμ hν`. Conclude with `realWhitAll_of hWR F E σ hCM M J hJ n ψ hψ ι θ l hP ε fr hfr g P μ ν hμ hν`.
-/
theorem realWhit_of (hWR : WR.WRSt) : RealWhit := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ ι _ θ l hP ε fr hfr g P μ ν hμ hν
  exact realWhitAll_of hWR F E σ hCM M J hJ n ψ hψ ι θ l hP ε fr hfr g P μ ν hμ hν

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ ι _ θ l hP ε fr hfr g P μ ν hμ hν`. Conclude with `realWhitAll_of hWR F E σ hCM M J hJ n ψ hψ ι θ l hP ε fr hfr g P μ ν hμ hν`.
-/
theorem realWhitEq_of (hWR : WR.WRSt) : RealWhitEq := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ ι _ θ l hP ε fr hfr g P μ ν hμ hν
  exact realWhitAll_of hWR F E σ hCM M J hJ n ψ hψ ι θ l hP ε fr hfr g P μ ν hμ hν

end PositivityTheory.SiegelWeilFormula.GReal
