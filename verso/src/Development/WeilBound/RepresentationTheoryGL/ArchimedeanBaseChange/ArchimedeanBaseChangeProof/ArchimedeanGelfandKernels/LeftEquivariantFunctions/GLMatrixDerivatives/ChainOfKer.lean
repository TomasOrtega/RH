import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.MulMemGLs

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Ker

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use `integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_` and prove the remaining obligations. Take `⟨R, hR⟩` from `hc`. Conclude with `⟨R, fun y hy h => by simp [hR y hy h]⟩`.
-/
theorem int_of_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt f) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

/- English proof (translation)
Simplify using `only [act, one_mul]`.
-/
theorem act_one [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (F : Mat n → E.V) : act μ E k F 1 = ∫ y : G n, k y.val (F y.val) ∂μ := by
  simp only [act, one_mul]

/- English proof (translation)
Use `haveI := FiniteDimensional.complete ℂ E.V`. Establish `hz` using `hKZ n μ E (fun y => k y * Γ - Γ * k y) ((hkc.clm_comp continuousOn_const).sub (continuousOn_const.clm_comp hkc)) (fun y hy k₂ => by`. Simplify using `only [hke y hy k₂, mul_assoc, ← hΓρ, sub_mul]) (fun f hf hfc => by`. Establish `hfcont : ContinuousOn f (GLs n)` using `hf.1.continuousOn`. Establish `i1` using `int_of_cpt hL μ (fun y => k y * Γ) f (hkc.clm_comp continuousOn_const) hfcont hfc`.

Establish `i2` using `int_of_cpt hL μ (fun y => Γ * k y) f (continuousOn_const.clm_comp hkc) hfcont hfc`. Simplify using `only [ContinuousLinearMap.sub_apply]`. Rewrite using `[integral_sub i1 i2]`. Establish `e1 : ∫ y : G n, (k y.val * Γ) (f y.val) ∂μ = act μ E k (fun x => Γ (f x)) 1`. Rewrite using `[act_one]`.

Both sides reduce to the same expression. Establish `e2 : ∫ y : G n, (Γ * k y.val) (f y.val) ∂μ = Γ (act μ E k f 1)`. Rewrite using `[act_one]`. Conclude with `ContinuousLinearMap.integral_comp_comm Γ (int_of_cpt hL μ k f hkc hfcont hfc)`. Rewrite using `[e1, e2, hΓ f hf, sub_self])`.

Introduce `y hy`. Use `hz y hy` as an intermediate fact. Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem gamma_of_comm (hKZ : KerZero) (hL : LgFacts) {E : KMod n} (Γ : E.V →L[ℂ] E.V)
    (hΓρ : ∀ k, Γ * E.ρ k = E.ρ k * Γ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n))
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hΓ : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1)) :
    ∀ y ∈ GLs n, Γ * k y = k y * Γ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have hz := hKZ n μ E (fun y => k y * Γ - Γ * k y) ((hkc.clm_comp continuousOn_const).sub
      (continuousOn_const.clm_comp hkc)) (fun y hy k₂ => by
        simp only [hke y hy k₂, mul_assoc, ← hΓρ, sub_mul]) (fun f hf hfc => by
      have hfcont : ContinuousOn f (GLs n) := hf.1.continuousOn
      have i1 := int_of_cpt hL μ (fun y => k y * Γ) f (hkc.clm_comp continuousOn_const) hfcont hfc
      have i2 := int_of_cpt hL μ (fun y => Γ * k y) f (continuousOn_const.clm_comp hkc) hfcont hfc
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub i1 i2]
      have e1 : ∫ y : G n, (k y.val * Γ) (f y.val) ∂μ = act μ E k (fun x => Γ (f x)) 1 := by
        rw [act_one]; rfl
      have e2 : ∫ y : G n, (Γ * k y.val) (f y.val) ∂μ = Γ (act μ E k f 1) := by
        rw [act_one]
        exact ContinuousLinearMap.integral_comp_comm Γ
          (int_of_cpt hL μ k f hkc hfcont hfc)
      rw [e1, e2, hΓ f hf, sub_self])
  intro y hy
  have := hz y hy
  exact (sub_eq_zero.1 this).symm

/- English proof (translation)
The claim follows from `(hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply (continuous_id.matrix_mul continuous_const).continuousOn`.
-/
theorem rd_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Rd X f) (GLs n) :=
  (hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_id.matrix_mul continuous_const).continuousOn

/- English proof (translation)
The claim follows from `((hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply (continuous_const.matrix_mul continuous_id).continuousOn).neg`.
-/
theorem ld_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Ld X f) (GLs n) :=
  ((hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_const.matrix_mul continuous_id).continuousOn).neg

def mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V →L[ℂ] V) : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) :=
  (ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip A

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ k y` using `(hk.differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds hy)`. Establish `e : (fun y => k y * A) = ⇑((mr A).restrictScalars ℝ) ∘ k` using `rfl`. Establish `hd2` using `(((mr A).restrictScalars ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv`. Simplify using `only [Rd]`. Rewrite using `[e]`.

Conclude with `congrArg (fun L => L (y * X)) hd2`.
-/
theorem rd_mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V))
    (hk : ContDiffOn ℝ ∞ k (GLs n)) (A : V →L[ℂ] V) (X : Mat n) (y : Mat n) (hy : y ∈ GLs n) :
    Rd X (fun y => k y * A) y = Rd X k y * A := by
  have hd : DifferentiableAt ℝ k y := (hk.differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds hy)
  have e : (fun y => k y * A) = ⇑((mr A).restrictScalars ℝ) ∘ k := rfl
  have hd2 := (((mr A).restrictScalars ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  simp only [Rd]
  rw [e]
  exact congrArg (fun L => L (y * X)) hd2

/- English proof (translation)
Use `haveI := FiniteDimensional.complete ℂ E.V`. Establish `h1 : (1 : Mat n) ∈ GLs n` using `by simp [GLs]`. Establish `hD` using `(hA hU n μ E k f hks hkc hf).2`. Establish `hfc' : ContinuousOn f (GLs n)` using `hf.continuousOn`. Establish `iL : ∀ p, Integrable (fun y : G n => Ld (hb p) k y.val (f y.val)) μ` using `fun p => int_of_cpt hL μ _ f (ld_cont k hks _) hfc' hfc`.

Establish `iK : Integrable (fun y : G n => k y.val (f y.val)) μ` using `int_of_cpt hL μ _ f hks.continuousOn hfc' hfc`. Establish `iP : ∀ p, Integrable (fun y : G n => (ε (hb p)) (Ld (hb p) k y.val (f y.val) + ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val)))) μ` using `fun p => ContinuousLinearMap.integrable_comp _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))`. Establish `ek : ∀ y : G n, kapL ε Fr k y.val (f y.val) = ∑ p, (ε (hb p)) (Ld (hb p) k y.val (f y.val) + ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val)))`. Introduce `y`. Simplify using `[kapL]`.

Repeatedly rewrite using `[ek]`. Rewrite using `[integral_finset_sum _ fun p _ => iP p]`. Simplify using `only [DC]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `e1 : ∫ a : G n, (ε (hb p)) ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ = (ε (hb p)) (∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ)` using `ContinuousLinearMap.integral_comp_comm _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))`.

Establish `e2 : ∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ = (∫ a : G n, (Ld (hb p) k a.val) (f a.val) ∂μ) + ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ` using `integral_add (iL p) (ContinuousLinearMap.integrable_comp _ iK)`. Establish `e3 : ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ = ((fderiv ℝ Fr 1) (hb p)) (∫ a : G n, (k a.val) (f a.val) ∂μ)` using `ContinuousLinearMap.integral_comp_comm _ iK`. Rewrite using `[e1, e2, e3, hD _ 1 h1, act_one]`. Simplify using `only [one_mul]`.
-/
theorem kapL_int (hA : ActDer) (hU : Unimod) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    DC ε Fr (act μ E k f) 1 = ∫ y : G n, kapL ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hD := (hA hU n μ E k f hks hkc hf).2
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have iL : ∀ p, Integrable (fun y : G n => Ld (hb p) k y.val (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f (ld_cont k hks _) hfc' hfc
  have iK : Integrable (fun y : G n => k y.val (f y.val)) μ := int_of_cpt hL μ _ f hks.continuousOn hfc' hfc
  have iP : ∀ p, Integrable (fun y : G n => (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val)))) μ := fun p =>
    ContinuousLinearMap.integrable_comp _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have ek : ∀ y : G n, kapL ε Fr k y.val (f y.val) = ∑ p, (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val))) := by
    intro y
    simp [kapL]
  simp_rw [ek]
  rw [integral_finset_sum _ fun p _ => iP p]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e1 : ∫ a : G n, (ε (hb p)) ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (ε (hb p)) (∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have e2 : ∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (∫ a : G n, (Ld (hb p) k a.val) (f a.val) ∂μ) + ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ :=
    integral_add (iL p) (ContinuousLinearMap.integrable_comp _ iK)
  have e3 : ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ =
      ((fderiv ℝ Fr 1) (hb p)) (∫ a : G n, (k a.val) (f a.val) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ iK
  rw [e1, e2, e3, hD _ 1 h1, act_one]
  simp only [one_mul]

/- English proof (translation)
Use `integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_` and prove the remaining obligations. Take `⟨R, hR⟩` from `hc`. Conclude with `⟨R, fun y hy h => by simp [hR y hy h]⟩`.
-/
theorem int_of_cptK (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt K) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

/- English proof (translation)
Use `haveI := FiniteDimensional.complete ℂ E.V`. Establish `h1 : (1 : Mat n) ∈ GLs n` using `by simp [GLs]`. Establish `hfc' : ContinuousOn f (GLs n)` using `hf.continuousOn`. Establish `hk' : ∀ p, ContDiffOn ℝ ∞ (fun y => k y * ε (hb p)) (GLs n)` using `fun p => by`. Establish `e : (fun y => k y * ε (hb p)) = ⇑((mr (ε (hb p))).restrictScalars ℝ) ∘ k` using `rfl`.

Rewrite using `[e]`. Conclude with `((mr (ε (hb p))).restrictScalars ℝ).contDiff.comp_contDiffOn hks`. Establish `hkc' : ∀ p, Cpt fun y => k y * ε (hb p)` using `fun p => by`. Take `⟨R, hR⟩` from `hkc`. Conclude with `⟨R, fun y hy h => by simp [hR y hy h]⟩`.

Establish `iA : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p)) (Rd (hb p) f y.val)) μ` using `fun p => int_of_cptK hL μ _ _ ((hk' p).continuousOn) (rd_cont f hf _) (hkc' p)`. Establish `iB : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) μ` using `fun p => int_of_cpt hL μ _ f ((hk' p).continuousOn.clm_comp continuousOn_const) hfc' hfc`. Establish `iC : ∀ p, Integrable (fun y : G n => (Rd (hb p) k y.val * ε (hb p)) (f y.val)) μ` using `fun p => int_of_cpt hL μ _ f ((rd_cont k hks _).clm_comp continuousOn_const) hfc' hfc`. Establish `eL : ∀ y : G n, k y.val (DC ε Fr f y.val) = ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val))`. Introduce `y`.

Simplify using `[DC, map_sum, map_add]`. Establish `eR : ∀ y : G n, kapR ε Fr k y.val (f y.val) = ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val))`. Introduce `y`. Simplify using `[kapR]`. Rewrite using `[act_one]`.

Repeatedly rewrite using `[eL, eR]`. Establish `sL : ∫ y : G n, ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ` using `integral_finset_sum _ fun p _ => (iA p).add (iB p)`. Establish `sR : ∫ y : G n, ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ` using `integral_finset_sum _ fun p _ => (iC p).neg.add (iB p)`. Rewrite using `[sL, sR]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Establish `a1 : ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, (k y.val * ε (hb p)) (Rd (hb p) f y.val) ∂μ) + ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ` using `integral_add (iA p) (iB p)`. Establish `a2 : ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) + (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, -((Rd (hb p) k y.val * ε (hb p)) (f y.val)) ∂μ) + ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ` using `integral_add (iC p).neg (iB p)`. Rewrite using `[a1, a2, integral_neg]`. Use `congr 1`. Establish `hibp` using `hI hU hR n μ E (fun y => k y * ε (hb p)) f (hk' p) (hkc' p) hf (hb p) 1 h1`.

Simplify using `only [one_mul] at hibp`. Rewrite using `[hibp]`. Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show (Rd (hb p) (fun y => k y * ε (hb p)) y.val) (f y.val) = (Rd (hb p) k y.val * ε (hb p)) (f y.val)`.

Rewrite using `[rd_mr k hks _ _ _ (mem_GLs_of y)]`.
-/
theorem kapR_int (hI : IBPAct) (hU : Unimod) (hR : RCalc) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    act μ E k (DC ε Fr f) 1 = ∫ y : G n, kapR ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have hk' : ∀ p, ContDiffOn ℝ ∞ (fun y => k y * ε (hb p)) (GLs n) := fun p => by
    have e : (fun y => k y * ε (hb p)) = ⇑((mr (ε (hb p))).restrictScalars ℝ) ∘ k := rfl
    rw [e]
    exact ((mr (ε (hb p))).restrictScalars ℝ).contDiff.comp_contDiffOn hks
  have hkc' : ∀ p, Cpt fun y => k y * ε (hb p) := fun p => by
    obtain ⟨R, hR⟩ := hkc
    exact ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have iA : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p)) (Rd (hb p) f y.val)) μ := fun p =>
    int_of_cptK hL μ _ _ ((hk' p).continuousOn) (rd_cont f hf _) (hkc' p)
  have iB : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((hk' p).continuousOn.clm_comp continuousOn_const) hfc' hfc
  have iC : ∀ p, Integrable (fun y : G n => (Rd (hb p) k y.val * ε (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((rd_cont k hks _).clm_comp continuousOn_const) hfc' hfc
  have eL : ∀ y : G n, k y.val (DC ε Fr f y.val) = ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    simp [DC, map_sum, map_add]
  have eR : ∀ y : G n, kapR ε Fr k y.val (f y.val) = ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    simp [kapR]
  rw [act_one]
  simp_rw [eL, eR]
  have sL : ∫ y : G n, ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finset_sum _ fun p _ => (iA p).add (iB p)
  have sR : ∫ y : G n, ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finset_sum _ fun p _ => (iC p).neg.add (iB p)
  rw [sL, sR]
  refine Finset.sum_congr rfl fun p _ => ?_
  have a1 : ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, (k y.val * ε (hb p)) (Rd (hb p) f y.val) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iA p) (iB p)
  have a2 : ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, -((Rd (hb p) k y.val * ε (hb p)) (f y.val)) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iC p).neg (iB p)
  rw [a1, a2, integral_neg]
  congr 1
  have hibp := hI hU hR n μ E (fun y => k y * ε (hb p)) f (hk' p) (hkc' p) hf (hb p) 1 h1
  simp only [one_mul] at hibp
  rw [hibp]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show (Rd (hb p) (fun y => k y * ε (hb p)) y.val) (f y.val) = (Rd (hb p) k y.val * ε (hb p)) (f y.val)
  rw [rd_mr k hks _ _ _ (mem_GLs_of y)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Ker
