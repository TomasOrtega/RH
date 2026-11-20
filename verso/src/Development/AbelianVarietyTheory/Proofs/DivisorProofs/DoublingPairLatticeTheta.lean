import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalInStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblUnitaryBox

section Alg

variable {A α β : Type} [CommRing A] [Fintype β] [DecidableEq β]

/- English proof (translation)
Rewrite using `[diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]`. Simplify using the standard rewrite rules.
-/
theorem mul_diagCols (w : Matrix α β A) : w * (diagCols β : Matrix (β ⊕ β) β A)ᵀ = Matrix.fromCols w w := by
  rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]; simp

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, h, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((t⁻¹).1)ᵀ, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]`.
-/
theorem mul_diagCols_move (w : Matrix α β A) (p : Matrix (β ⊕ β) (β ⊕ β) A) (t : GL β A)
    (h : p * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t.1) : w * ((t⁻¹).1)ᵀ * (diagCols β : Matrix (β ⊕ β) β A)ᵀ * pᵀ = w * (diagCols β : Matrix (β ⊕ β) β A)ᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((t⁻¹).1)ᵀ, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]

end Alg

section Meas

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance (priority := high) measTup : MeasurableSpace (κ → AF F) := borel _

local instance borelTup : BorelSpace (κ → AF F) := ⟨rfl⟩

/- English proof (translation)
The claim follows from `(schA_memLp_two F κ μ hμ φ hφ).integrable_norm_pow two_ne_zero`.
-/
theorem integrable_normSq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable (fun x => ‖φ x‖ ^ 2) μ :=
  (schA_memLp_two F κ μ hμ φ hφ).integrable_norm_pow two_ne_zero

/- English proof (translation)
Rewrite using `[ofReal_integral_eq_lintegral_ofReal (integrable_normSq μ hμ hφ) (Filter.Eventually.of_forall fun x => by positivity)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.
-/
theorem lintegral_eq_ofReal (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_normSq μ hμ hφ) (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

/- English proof (translation)
Establish `hc : Continuous fun x => ‖φ x‖ ^ 2` using `(GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ).norm.pow 2`. Use `(integral_pos_iff_support_of_nonneg (fun p => by positivity) (integrable_normSq μ hμ hφ)).2 ?_` and prove the remaining obligations. Use `hc.isOpen_support.measure_pos _ ⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[Function.mem_support]`. Check the signs of the components of the expression.
-/
theorem integral_normSq_pos (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ)
    {x : κ → AF F} (hx : φ x ≠ 0) : 0 < ∫ x, ‖φ x‖ ^ 2 ∂μ := by
  have hc : Continuous fun x => ‖φ x‖ ^ 2 := (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ).norm.pow 2
  refine (integral_pos_iff_support_of_nonneg (fun p => by positivity) (integrable_normSq μ hμ hφ)).2 ?_
  refine hc.isOpen_support.measure_pos _ ⟨x, ?_⟩
  rw [Function.mem_support]
  positivity

/- English proof (translation)
Establish `hn : ∀ φ ∈ schA F κ, ∫ x, ‖T φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ` using `fun φ hφ => by`. Establish `h` using `hT φ hφ`. Rewrite `h` using `[lintegral_eq_ofReal μ hμ (hp φ hφ), lintegral_eq_ofReal μ hμ hφ]`. Conclude with `(ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity) (integral_nonneg fun x => by positivity)).1 h`. Establish `hm : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∀ c : ℂ, f + c • g ∈ schA F κ` using `fun f hf g hg c => (schA F κ).add_mem hf ((schA F κ).smul_mem c hg)`.

Establish `pol : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∫ x, f x * star (g x) ∂μ = (((∫ x, ‖(f + (1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∫ x, ‖(f + (-1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) + Complex.I * ((∫ x, ‖(f + Complex.I • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) - Complex.I * ((∫ x, ‖(f + (-Complex.I) • g) x‖ ^ 2 ∂μ : …` using `fun f hf g hg => by`. Establish `hi : ∀ c : ℂ, Integrable (fun x => ((‖(f + c • g) x‖ ^ 2 : ℝ) : ℂ)) μ` using `fun c => (integrable_normSq μ hμ (hm f hf g hg c)).ofReal`. Simplify using `only [← integral_complex_ofReal]`. Rewrite using `[← integral_const_mul, ← integral_const_mul, ← integral_sub (hi _) (hi _), ← integral_add, ← integral_sub, ← integral_div]`. Use `rotate_left`.

Conclude with `((hi _).sub (hi _)).add ((hi _).const_mul _)`. Conclude with `(hi _).const_mul _`. Conclude with `(hi _).sub (hi _)`. Conclude with `(hi _).const_mul _`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_add, map_mul, map_neg, map_one, Complex.conj_I, Complex.star_def]`. Take the linear combination `((f x * (starRingEnd ℂ) (g x)) / 2 - (g x * (starRingEnd ℂ) (f x)) / 2) * Complex.I_mul_I`. Rewrite using `[pol _ (hp _ h₁) _ (hp _ h₂), pol _ h₁ _ h₂]`. Simplify using `only [← hn _ (hm _ h₁ _ h₂ _), map_add, map_smul]`.
-/
theorem integral_mul_star_eq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ φ ∈ schA F κ, T φ ∈ schA F κ)
    (hT : ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {φ₁ φ₂ : (κ → AF F) → ℂ}
    (h₁ : φ₁ ∈ schA F κ) (h₂ : φ₂ ∈ schA F κ) :
    ∫ x, T φ₁ x * star (T φ₂ x) ∂μ = ∫ x, φ₁ x * star (φ₂ x) ∂μ := by
  have hn : ∀ φ ∈ schA F κ, ∫ x, ‖T φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := fun φ hφ => by
    have h := hT φ hφ
    rw [lintegral_eq_ofReal μ hμ (hp φ hφ), lintegral_eq_ofReal μ hμ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hm : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∀ c : ℂ, f + c • g ∈ schA F κ := fun f hf g hg c =>
    (schA F κ).add_mem hf ((schA F κ).smul_mem c hg)
  have pol : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∫ x, f x * star (g x) ∂μ =
      (((∫ x, ‖(f + (1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∫ x, ‖(f + (-1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) +
        Complex.I * ((∫ x, ‖(f + Complex.I • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) -
        Complex.I * ((∫ x, ‖(f + (-Complex.I) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ)) / 4 := fun f hf g hg => by
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖(f + c • g) x‖ ^ 2 : ℝ) : ℂ)) μ := fun c =>
      (integrable_normSq μ hμ (hm f hf g hg c)).ofReal
    simp only [← integral_complex_ofReal]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi _) (hi _),
      ← integral_add, ← integral_sub, ← integral_div]
    rotate_left
    · exact ((hi _).sub (hi _)).add ((hi _).const_mul _)
    · exact (hi _).const_mul _
    · exact (hi _).sub (hi _)
    · exact (hi _).const_mul _
    congr 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_add, map_mul,
      map_neg, map_one, Complex.conj_I, Complex.star_def]
    linear_combination ((f x * (starRingEnd ℂ) (g x)) / 2 - (g x * (starRingEnd ℂ) (f x)) / 2) * Complex.I_mul_I
  rw [pol _ (hp _ h₁) _ (hp _ h₂), pol _ h₁ _ h₂]
  simp only [← hn _ (hm _ h₁ _ h₂ _), map_add, map_smul]

open GlobalTheory.GaugeEx in

/- English proof (translation)
Use `haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Establish `hdet : (LinearMap.toMatrix' g).det = 1` using `by rw [LinearMap.det_toMatrix', hg]`. Establish `hΛ : IsUnit (LinearMap.toMatrix' g).det` using `hdet ▸ isUnit_one`. Use `set L := GlobalTheory.ModuLR.mulVecCE (LinearMap.toMatrix' g) hΛ with hL`. Establish `hu : hΛ.unit = 1` using `Units.ext hdet`.

Establish `hχ : addEquivAddHaarChar L = 1`. Establish `h` using `GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele F _ hΛ`. Rewrite `h` using `[hu, map_one]`. Use `h` and compare the differences between its conclusion and the goal. Conclude with `(@BorelSpace.measurable_eq _ _ MeasurableSpace.pi Pi.borelSpace).symm`.

Establish `key` using `addEquivAddHaarChar_smul_map μ L`. Rewrite `key` using `[hχ, one_smul]`. Establish `hLg : ∀ x, L x = g x` using `fun x => by rw [hL, GlobalTheory.ModuLR.mulVecCE_apply, LinearMap.toMatrix'_mulVec]`. Establish `h` using `lintegral_map_equiv (μ := μ) (fun x => ‖f x‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv`. Establish `h2 : μ.map L.toHomeomorph.toMeasurableEquiv = μ` using `key`.

Rewrite `h` using `[h2]`. Rewrite using `[h]`. Conclude with `lintegral_congr fun x => by rw [← hLg]; rfl`.
-/
theorem lintegral_comp_of_det (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) (g : (κ → AF F) →ₗ[AF F] (κ → AF F))
    (hg : LinearMap.det g = 1) (f : (κ → AF F) → ℂ) : ∫⁻ x, ‖f (g x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  classical
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hdet : (LinearMap.toMatrix' g).det = 1 := by rw [LinearMap.det_toMatrix', hg]
  have hΛ : IsUnit (LinearMap.toMatrix' g).det := hdet ▸ isUnit_one
  set L := GlobalTheory.ModuLR.mulVecCE (LinearMap.toMatrix' g) hΛ with hL
  have hu : hΛ.unit = 1 := Units.ext hdet
  have hχ : addEquivAddHaarChar L = 1 := by
    have h := GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele F _ hΛ
    rw [hu, map_one] at h
    convert h
    exact (@BorelSpace.measurable_eq _ _ MeasurableSpace.pi Pi.borelSpace).symm
  have key := addEquivAddHaarChar_smul_map μ L
  rw [hχ, one_smul] at key
  have hLg : ∀ x, L x = g x := fun x => by rw [hL, GlobalTheory.ModuLR.mulVecCE_apply, LinearMap.toMatrix'_mulVec]
  have h := lintegral_map_equiv (μ := μ) (fun x => ‖f x‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv
  have h2 : μ.map L.toHomeomorph.toMeasurableEquiv = μ := key
  rw [h2] at h
  rw [h]
  exact lintegral_congr fun x => by rw [← hLg]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨Measure.addHaar, inferInstance⟩`.
-/
theorem exists_haar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩

end Meas

section Shape

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {M : Type} [AddCommGroup M] [Module (AF F) M]
  {Bf : M → M → AF F}

attribute [local instance] measTup borelTup

/- English proof (translation)
Simplify using `[Darboux.rho, schr, hw]`.
-/
theorem rho_zero_of_fst (ψ : AddChar (AF F) ℂ) (d : Darboux Bf κ) {w : M} (hw : (d.e w).1 = 0) (f : (κ → AF F) → ℂ) :
    d.rho ψ w f 0 = f 0 := by simp [Darboux.rho, schr, hw]

/- English proof (translation)
Simplify using `[Darboux.rho, schr, hw]`.
-/
theorem rho_zero_of_snd (ψ : AddChar (AF F) ℂ) (d : Darboux Bf κ) {w : M} (hw : (d.e w).2 = 0) (f : (κ → AF F) → ℂ) :
    d.rho ψ w f 0 = f (d.e w).1 := by simp [Darboux.rho, schr, hw]

/- English proof (translation)
Use `GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ (LinearMap.proj 0 ∘ₗ T) (hadm _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms κ)) fun y φ hφ => ?_` and prove the remaining obligations. Establish `e : (fun x => ψ (x ⬝ᵥ y) * φ x) = d.rho ψ (d.e.symm (0, y)) φ` using `by funext x; simp [schr, Darboux.rho]`. Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply]`. Rewrite using `[e, himpl _ φ hφ, rho_zero_of_fst ψ d (hY _ (by simp))]`.
-/
theorem exists_scalar {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (d : Darboux Bf κ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (a : M → M) (hadm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (himpl : ∀ w, ∀ φ ∈ schA F κ, T (d.rho ψ w φ) = d.rho ψ (a w) (T φ))
    (hY : ∀ w, (d.e w).1 = 0 → (d.e (a w)).1 = 0) : ∃ c : ℂ, ∀ φ ∈ schA F κ, T φ 0 = c * φ 0 := by
  refine GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ (LinearMap.proj 0 ∘ₗ T) (hadm _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms κ)) fun y φ hφ => ?_
  have e : (fun x => ψ (x ⬝ᵥ y) * φ x) = d.rho ψ (d.e.symm (0, y)) φ := by funext x; simp [schr, Darboux.rho]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  rw [e, himpl _ φ hφ, rho_zero_of_fst ψ d (hY _ (by simp))]

/- English proof (translation)
Rewrite using `[← rho_zero_of_snd ψ d hw' (T φ), ← himpl φ hφ, ← rho_zero_of_snd ψ d hw φ]`. Conclude with `hc _ (GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ _ φ hφ)`.
-/
theorem apply_coord {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (d : Darboux Bf κ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    {w w' : M} (himpl : ∀ φ ∈ schA F κ, T (d.rho ψ w φ) = d.rho ψ w' (T φ)) {c : ℂ}
    (hc : ∀ φ ∈ schA F κ, T φ 0 = c * φ 0) (hw : (d.e w).2 = 0) (hw' : (d.e w').2 = 0) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : T φ (d.e w').1 = c * φ (d.e w).1 := by
  rw [← rho_zero_of_snd ψ d hw' (T φ), ← himpl φ hφ, ← rho_zero_of_snd ψ d hw φ]
  exact hc _ (GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ _ φ hφ)

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩` from `h`. Establish `hYd : ∀ w (q : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)), (dd.e w).1 = 0 → (dd.e (w * q)).1 = 0`. Introduce `w q hw`. Rewrite `hw`, the goal using `[← Matrix.fromCols_toCols w]`. Rewrite `hw` using `[hdd]`.

Establish `h1 : (d.e w.toCols₁).1 = 0` using `funext fun i => congrFun hw (Sum.inl i)`. Establish `h2 : (d.e w.toCols₂).1 = 0` using `funext fun i => congrFun hw (Sum.inr i)`. Rewrite using `[← Matrix.fromBlocks_toBlocks q, Matrix.fromCols_mul_fromBlocks, hdd]`. Simplify using `[hY _ _ h1, hY _ _ h2]`. Use `choose cf hcf using fun p => exists_scalar hψ dd (omd p) (actB (cA σ) p) (hS.adm p) (hS.impl p) fun w hw => hYd w _ hw`.

Take `⟨φz, hφz, hφz0⟩` from `GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)`. Establish `hmul : ∀ p q, cf (p * q) = cf p * cf q` using `fun p q => by`. Use `mul_right_cancel₀ hφz0 ?_` and prove the remaining obligations. Rewrite using `[← hcf _ _ hφz, map_mul, Module.End.mul_apply, hcf p _ (hS.pres q _ hφz), hcf q _ hφz, mul_assoc]`. Establish `hone : cf 1 = 1` using `mul_right_cancel₀ hφz0 (by rw [← hcf _ _ hφz]; simp)`.

Establish `hne : ∀ p, cf p ≠ 0` using `fun p => left_ne_zero_of_mul_eq_one (by rw [← hmul, mul_inv_cancel, hone])`. Establish `hne' : ∀ p, ((‖cf p‖ : ℝ) : ℂ) ≠ 0` using `fun p => by simpa using hne p`. Establish `hcont_cf : Continuous cf`. Establish `hf` using `hS.cont _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφz`. Simplify using `only [LinearMap.proj_apply] at hf`.

Use `(hf.div_const (φz 0)).congr fun p => ?_` and prove the remaining obligations. Rewrite using `[hcf p _ hφz, mul_div_cancel_right₀ _ hφz0]`. Set `cM : UG (cA σ) (dbl (incM F JB)) →* ℂ` to `{ toFun := fun p => cf p / (‖cf p‖ : ℝ) map_one' := by simp [hone] map_mul' := fun p q => by rw [hmul, norm_mul]; push_cast; ring }`. Establish `hcM : Continuous cM` using `hcont_cf.div (Complex.continuous_ofReal.comp hcont_cf.norm) hne'`. Set `c` to `cM.toHomUnits`.

Establish `hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cM p` using `fun p => rfl`. Establish `hcont : Continuous c`. Use `Units.continuous_iff.2 ⟨hcM, ?_⟩` and prove the remaining obligations. Establish `: (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cM p)⁻¹` using `funext fun p => by`. Rewrite using `[Units.val_inv_eq_inv_val, hcv]`.

Rewrite using `[this]`. Conclude with `hcM.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero`. Take `⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩` from `GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ`. Take `⟨μ, hμ⟩` from `exists_haar F κ`. Take `⟨k, hk⟩` from `GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral F ψ hψ κ l hl hlinv μ hμ`.

Establish `hk0 : k ≠ 0` using `by rintro rfl; exact hl0 (by rw [hk _ hφ₀, zero_mul])`. Take `⟨φ₁, hφ₁, hφ₁0⟩` from `GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ`. Establish `hb` using `GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ φ₁ hφ₁ (star φ₁) (GlobalTheory.SchAConj.star_mem_schA F κ φ₁ hφ₁)`. Establish `hbd : ∀ z, boxFun φ₁ (star φ₁) (Sum.elim z z) = ((‖φ₁ z‖ ^ 2 : ℝ) : ℂ)` using `fun z => by`. Simplify using `only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Establish `hΔ : ∀ w : Matrix (Fin a) (Fin b) (AE F E), w * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols w w` using `fun w => mul_diagCols w`. Establish `hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 → c p = 1` using `fun p t hpt => by`. Establish `e1` using `hR l hl (fun z φ hφ => by`. Use `hlinv (d.e z).1 (d.e z).2 φ hφ using 2` and compare the differences between its conclusion and the goal. Conclude with `congrFun (GlobalTheory.WeilSchUnique.dd_rho_diag hdd ψ z) φ) p t hpt _ hb`.

Set `s : (κ → AF F) → κ → AF F` to `fun z => (d.e (d.e.symm (z, 0) * ((t⁻¹).1)ᵀ)).1`. Establish `hval : ∀ z, omd p (boxFun φ₁ (star φ₁)) (Sum.elim z z) = cf p * ((‖φ₁ (s z)‖ ^ 2 : ℝ) : ℂ)` using `fun z => by`. Establish `h0 : (d.e (d.e.symm (z, 0))).2 = 0` using `by simp`. Establish `h1` using `hX _ ((t⁻¹).1)ᵀ h0`. Establish `hact : actB (cA σ) p (d.e.symm (z, 0) * ((t⁻¹).1)ᵀ * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ) = d.e.symm (z, 0) * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ` using `mul_diagCols_move _ _ t hpt`.

Use `apply_coord hψ dd (omd p) (fun φ hφ => hS.impl p (d.e.symm (z, 0) * ((t⁻¹).1)ᵀ * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ) φ hφ) (hcf p) (by rw [hΔ, hdd, h1]; simp) (by rw [hact, hΔ, hdd, h0]; simp) hb` as an intermediate fact. Rewrite `this` using `[hact, hΔ, hΔ, hdd, hdd]`. Simplify using `only [LinearEquiv.apply_symm_apply] at this`. Rewrite using `[this, hbd]`. Rewrite `e1` using `[hk _ (hS.pres p _ hb), hk _ hb]`.

Simplify using `only [GlobalTheory.DiagSiegel.diagInt, hval, hbd] at e1`. Rewrite `e1` using `[integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]`. Establish `hN` using `integral_normSq_pos μ hμ hφ₁ hφ₁0`. Establish `hs : 0 ≤ ∫ z, ‖φ₁ (s z)‖ ^ 2 ∂μ` using `integral_nonneg fun x => by positivity`. Establish `hr : 0 < (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin a) : ℝ) / 2) : ℝ)`.

Use `Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 ?_)) _` and prove the remaining obligations. Conclude with `((adeleClass F).modu.toHomUnits _).ne_zero`. Generalize the expression as in `(((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin a) : ℝ) / 2) : ℝ) = r at e1 hr`. Generalize the expression as in `∫ z, ‖φ₁ (s z)‖ ^ 2 ∂μ = S at e1 hs`. Generalize the expression as in `∫ z, ‖φ₁ z‖ ^ 2 ∂μ = N at e1 hN`.

Establish `e2 : cf p * S = ((r * N : ℝ) : ℂ)`. Use `mul_left_cancel₀ hk0 ?_` and prove the remaining obligations. Rewrite using `[e1]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish `hS0 : S ≠ 0`. Introduce and unpack `rfl`. Rewrite `e2` using `[Complex.ofReal_zero, mul_zero]`. Conclude with `(mul_pos hr hN).ne (by exact_mod_cast e2)`. Establish `e3 : cf p = ((r * N / S : ℝ) : ℂ)`.

Rewrite using `[Complex.ofReal_div, eq_div_iff (by exact_mod_cast hS0), e2]`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hcv, Units.val_one]`. Use `show cf p / (‖cf p‖ : ℝ) = 1`. Rewrite using `[div_eq_one_iff_eq (hne' p), e3, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`.

Establish `hc1` using `GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB 1 (fun i j => by simp [hJ i j]) hdet c hcont hP`. Take `⟨gd, hgd⟩` from `GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g`. Use `⟨cf gd, ?_, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `: cM gd = 1` using `by rw [← hcv, hc1]; rfl`. Conclude with `(div_eq_one_iff_eq (hne' gd)).1 this`.

Establish `e` using `hcf gd _ (GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ φ hφ φ₁ hφ₁)`. Rewrite `e` using `[hres g gd hgd φ hφ φ₁ hφ₁]`. Use `mul_right_cancel₀ hφ₁0 ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `e`.
-/
theorem exists_pos_scalar {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (hJ : ∀ i j, σ (JB j i) = JB i j) (hdet : JB.det ≠ 0) {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) (d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d 1 om)
    (hY : ∀ w (q : Matrix (Fin b) (Fin b) (AE F E)), (d.e w).1 = 0 → (d.e (w * q)).1 = 0)
    (hX : ∀ w (q : Matrix (Fin b) (Fin b) (AE F E)), (d.e w).2 = 0 → (d.e (w * q)).2 = 0)
    (g : UG (cA σ) (incM F JB)) : ∃ c : ℂ, c = (‖c‖ : ℝ) ∧ ∀ φ ∈ schA F κ, om g φ 0 = c * φ 0 := by
  obtain ⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  have hYd : ∀ w (q : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)), (dd.e w).1 = 0 → (dd.e (w * q)).1 = 0 := by
    intro w q hw
    rw [← Matrix.fromCols_toCols w] at hw ⊢
    rw [hdd] at hw
    have h1 : (d.e w.toCols₁).1 = 0 := funext fun i => congrFun hw (Sum.inl i)
    have h2 : (d.e w.toCols₂).1 = 0 := funext fun i => congrFun hw (Sum.inr i)
    rw [← Matrix.fromBlocks_toBlocks q, Matrix.fromCols_mul_fromBlocks, hdd]
    simp [hY _ _ h1, hY _ _ h2]
  choose cf hcf using fun p => exists_scalar hψ dd (omd p) (actB (cA σ) p) (hS.adm p) (hS.impl p)
    fun w hw => hYd w _ hw
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => by
    refine mul_right_cancel₀ hφz0 ?_
    rw [← hcf _ _ hφz, map_mul, Module.End.mul_apply, hcf p _ (hS.pres q _ hφz), hcf q _ hφz, mul_assoc]
  have hone : cf 1 = 1 := mul_right_cancel₀ hφz0 (by rw [← hcf _ _ hφz]; simp)
  have hne : ∀ p, cf p ≠ 0 := fun p => left_ne_zero_of_mul_eq_one (by rw [← hmul, mul_inv_cancel, hone])
  have hne' : ∀ p, ((‖cf p‖ : ℝ) : ℂ) ≠ 0 := fun p => by simpa using hne p
  have hcont_cf : Continuous cf := by
    have hf := hS.cont _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφz
    simp only [LinearMap.proj_apply] at hf
    refine (hf.div_const (φz 0)).congr fun p => ?_
    rw [hcf p _ hφz, mul_div_cancel_right₀ _ hφz0]
  let cM : UG (cA σ) (dbl (incM F JB)) →* ℂ :=
    { toFun := fun p => cf p / (‖cf p‖ : ℝ)
      map_one' := by simp [hone]
      map_mul' := fun p q => by rw [hmul, norm_mul]; push_cast; ring }
  have hcM : Continuous cM := hcont_cf.div (Complex.continuous_ofReal.comp hcont_cf.norm) hne'
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cM p := fun p => rfl
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcM, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cM p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcM.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ
  obtain ⟨μ, hμ⟩ := exists_haar F κ
  obtain ⟨k, hk⟩ := GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral F ψ hψ κ l hl hlinv μ hμ
  have hk0 : k ≠ 0 := by rintro rfl; exact hl0 (by rw [hk _ hφ₀, zero_mul])
  obtain ⟨φ₁, hφ₁, hφ₁0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  have hb := GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ φ₁ hφ₁ (star φ₁) (GlobalTheory.SchAConj.star_mem_schA F κ φ₁ hφ₁)
  have hbd : ∀ z, boxFun φ₁ (star φ₁) (Sum.elim z z) = ((‖φ₁ z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.star_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  have hΔ : ∀ w : Matrix (Fin a) (Fin b) (AE F E), w * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols w w := fun w =>
    mul_diagCols w
  have hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have e1 := hR l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2
      exact congrFun (GlobalTheory.WeilSchUnique.dd_rho_diag hdd ψ z) φ) p t hpt _ hb
    let s : (κ → AF F) → κ → AF F := fun z => (d.e (d.e.symm (z, 0) * ((t⁻¹).1)ᵀ)).1
    have hval : ∀ z, omd p (boxFun φ₁ (star φ₁)) (Sum.elim z z) = cf p * ((‖φ₁ (s z)‖ ^ 2 : ℝ) : ℂ) := fun z => by
      have h0 : (d.e (d.e.symm (z, 0))).2 = 0 := by simp
      have h1 := hX _ ((t⁻¹).1)ᵀ h0
      have hact : actB (cA σ) p (d.e.symm (z, 0) * ((t⁻¹).1)ᵀ * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ) =
          d.e.symm (z, 0) * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ := mul_diagCols_move _ _ t hpt
      have := apply_coord hψ dd (omd p) (fun φ hφ => hS.impl p
        (d.e.symm (z, 0) * ((t⁻¹).1)ᵀ * (diagCols (Fin b) : Matrix _ _ (AE F E))ᵀ) φ hφ) (hcf p)
        (by rw [hΔ, hdd, h1]; simp) (by rw [hact, hΔ, hdd, h0]; simp) hb
      rw [hact, hΔ, hΔ, hdd, hdd] at this
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [this, hbd]
    rw [hk _ (hS.pres p _ hb), hk _ hb] at e1
    simp only [GlobalTheory.DiagSiegel.diagInt, hval, hbd] at e1
    rw [integral_const_mul, integral_complex_ofReal, integral_complex_ofReal] at e1
    have hN := integral_normSq_pos μ hμ hφ₁ hφ₁0
    have hs : 0 ≤ ∫ z, ‖φ₁ (s z)‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
    have hr : 0 < (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
        (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin a) : ℝ) / 2) : ℝ) := by
      refine Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 ?_)) _
      exact ((adeleClass F).modu.toHomUnits _).ne_zero
    generalize (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
        (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin a) : ℝ) / 2) : ℝ) = r at e1 hr
    generalize ∫ z, ‖φ₁ (s z)‖ ^ 2 ∂μ = S at e1 hs
    generalize ∫ z, ‖φ₁ z‖ ^ 2 ∂μ = N at e1 hN
    have e2 : cf p * S = ((r * N : ℝ) : ℂ) := by
      refine mul_left_cancel₀ hk0 ?_
      rw [e1]; simp; ring
    have hS0 : S ≠ 0 := by
      rintro rfl
      rw [Complex.ofReal_zero, mul_zero] at e2
      exact (mul_pos hr hN).ne (by exact_mod_cast e2)
    have e3 : cf p = ((r * N / S : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hS0), e2]
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    show cf p / (‖cf p‖ : ℝ) = 1
    rw [div_eq_one_iff_eq (hne' p), e3, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB 1 (fun i j => by simp [hJ i j]) hdet c hcont hP
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g
  refine ⟨cf gd, ?_, fun φ hφ => ?_⟩
  · have : cM gd = 1 := by rw [← hcv, hc1]; rfl
    exact (div_eq_one_iff_eq (hne' gd)).1 this
  · have e := hcf gd _ (GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ φ hφ φ₁ hφ₁)
    rw [hres g gd hgd φ hφ φ₁ hφ₁] at e
    refine mul_right_cancel₀ hφ₁0 ?_
    rw [mul_assoc]
    exact e

end Shape

section Lagr

variable {R A α β m κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype α] [DecidableEq α] [Fintype κ]
  {Bf : Matrix α β A → Matrix α β A → R} (co : Darboux Bf κ)

/- English proof (translation)
Establish `: (x * u) i = ∑ k, x i k • u k`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Rewrite using `[this]`. Conclude with `S.sum_mem fun k _ => S.smul_mem _ (hu k)`.
-/
theorem rows_mul_mem (S : Submodule A (β → A)) (x : Matrix α α A) {u : Matrix α β A} (hu : ∀ i, u i ∈ S) (i : α) :
    (x * u) i ∈ S := by
  have : (x * u) i = ∑ k, x i k • u k := by
    funext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [this]
  exact S.sum_mem fun k _ => S.smul_mem _ (hu k)

omit [DecidableEq α] in
/- English proof (translation)
Use `choose a ha b hb hab using fun i => Submodule.mem_sup.1 (h ▸ Submodule.mem_top : u i ∈ S ⊔ T)`. Conclude with `⟨Matrix.of a, Matrix.of b, ha, hb, funext fun i => (hab i).symm⟩`.
-/
theorem exists_split {S T : Submodule A (β → A)} (h : S ⊔ T = ⊤) (u : Matrix α β A) :
    ∃ a b : Matrix α β A, (∀ i, a i ∈ S) ∧ (∀ i, b i ∈ T) ∧ u = a + b := by
  choose a ha b hb hab using fun i => Submodule.mem_sup.1 (h ▸ Submodule.mem_top : u i ∈ S ⊔ T)
  exact ⟨Matrix.of a, Matrix.of b, ha, hb, funext fun i => (hab i).symm⟩

/- English proof (translation)
Take `⟨a, b, ha, hb, rfl⟩` from `exists_split h u`. Rewrite `hu` using `[map_add, Prod.fst_add, hS a ha, zero_add]`. Establish `: b = 0` using `co.e.injective (by rw [map_zero]; exact Prod.ext hu (hT b hb))`. Rewrite using `[this, add_zero]`. Conclude with `ha`.
-/
theorem rows_of_fst {S T : Submodule A (β → A)} (h : S ⊔ T = ⊤) (hS : ∀ u, (∀ i, u i ∈ S) → (co.e u).1 = 0)
    (hT : ∀ u, (∀ i, u i ∈ T) → (co.e u).2 = 0) {u : Matrix α β A} (hu : (co.e u).1 = 0) : ∀ i, u i ∈ S := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_split h u
  rw [map_add, Prod.fst_add, hS a ha, zero_add] at hu
  have : b = 0 := co.e.injective (by rw [map_zero]; exact Prod.ext hu (hT b hb))
  rw [this, add_zero]
  exact ha

/- English proof (translation)
Take `⟨a, b, ha, hb, rfl⟩` from `exists_split h u`. Rewrite `hu` using `[map_add, Prod.snd_add, hT b hb, add_zero]`. Establish `: a = 0` using `co.e.injective (by rw [map_zero]; exact Prod.ext (hS a ha) hu)`. Rewrite using `[this, zero_add]`. Conclude with `hb`.
-/
theorem rows_of_snd {S T : Submodule A (β → A)} (h : S ⊔ T = ⊤) (hS : ∀ u, (∀ i, u i ∈ S) → (co.e u).1 = 0)
    (hT : ∀ u, (∀ i, u i ∈ T) → (co.e u).2 = 0) {u : Matrix α β A} (hu : (co.e u).2 = 0) : ∀ i, u i ∈ T := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_split h u
  rw [map_add, Prod.snd_add, hT b hb, add_zero] at hu
  have : a = 0 := co.e.injective (by rw [map_zero]; exact Prod.ext (hS a ha) hu)
  rw [this, zero_add]
  exact hb

variable (R) in

def antiMap (e : m ⊕ m ≃ β) : (m → α → A) →ₗ[R] Matrix α β A where
  toFun v := Matrix.of fun i => pairVec e (fun j => v j i) (fun j => -v j i)
  map_add' v w := by
    ext i k
    obtain ⟨j | j, rfl⟩ := e.surjective k <;> simp [add_comm]
  map_smul' c v := by
    ext i k
    obtain ⟨j | j, rfl⟩ := e.surjective k <;> simp

def fstAct (x : Matrix α α A) : (κ → R) →ₗ[R] (κ → R) where
  toFun z := (co.e (x * co.e.symm (z, 0))).1
  map_add' z z' := by
    rw [show ((z + z', 0) : (κ → R) × (κ → R)) = (z, 0) + (z', 0) by simp, map_add, Matrix.mul_add, map_add, Prod.fst_add]
  map_smul' c z := by
    rw [show ((c • z, 0) : (κ → R) × (κ → R)) = c • (z, 0) by simp, map_smul, Matrix.mul_smul, map_smul]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fstAct_apply (x : Matrix α α A) (z : κ → R) : fstAct co x z = (co.e (x * co.e.symm (z, 0))).1 := rfl

/- English proof (translation)
Establish `hmem : ∀ (v : m → α → A) i, antiMap R e v i ∈ antiSub A e` using `fun v i => (mem_antiSub e).2 ⟨fun j => v j i, rfl⟩`. Set `Φ₀ : (m → α → A) →ₗ[R] (κ → R)` to `LinearMap.fst R _ _ ∘ₗ co.e.toLinearMap ∘ₗ antiMap R e`. Establish `hΦ₀ : ∀ v, co.e.symm (Φ₀ v, 0) = antiMap R e v` using `fun v => by`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `Prod.ext rfl (hT _ (hmem v)).symm`.

Establish `hbij : Function.Bijective Φ₀`. Use `⟨fun v w hvw => ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `h1 : antiMap R e v = antiMap R e w` using `by rw [← hΦ₀, ← hΦ₀, hvw]`. Use function extensionality and compare the values at `j i`. Simplify `congrFun (congrFun h1 i) (e (Sum.inl j))` using `[antiMap]`.

Use `choose y hy using fun i => (mem_antiSub e).1 (rows_of_snd co h hS hT (u := co.e.symm (z, 0)) (by simp) i)`. Establish `h1 : antiMap R e (fun j i => y i j) = co.e.symm (z, 0)` using `funext fun i => (hy i).symm`. Use `⟨fun j i => y i j, ?_⟩` and prove the remaining obligations. Use `show (co.e (antiMap R e _)).1 = z`. Rewrite using `[h1]`.

Simplify using the standard rewrite rules. Set `Φ` to `LinearEquiv.ofBijective Φ₀ hbij`. Set `L : (m → α → A) →ₗ[A] (m → α → A)` to `LinearMap.pi fun j => (Matrix.toLin' x).comp (LinearMap.proj j)`. Establish `hL : fstAct co x = Φ.toLinearMap ∘ₗ L.restrictScalars R ∘ₗ Φ.symm.toLinearMap`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations.

Take `⟨v, rfl⟩` from `Φ.surjective z`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Use `show (co.e (x * co.e.symm (Φ₀ v, 0))).1 = (co.e (antiMap R e (L v))).1`. Rewrite using `[hΦ₀]`. Use `congr 2`.

Use extensionality with `i k`. Apply the tactic sequence `obtain ⟨j | j, rfl⟩ := e.surjective k <;> simp [antiMap, L, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[hL, LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_pi]`. Simplify using the standard rewrite rules.
-/
theorem det_fstAct [Fintype m] [DecidableEq m] [Module.Free R A] [Module.Finite R A] (e : m ⊕ m ≃ β) (h : diagSub A e ⊔ antiSub A e = ⊤)
    (hS : ∀ u, (∀ i, u i ∈ diagSub A e) → (co.e u).1 = 0) (hT : ∀ u, (∀ i, u i ∈ antiSub A e) → (co.e u).2 = 0)
    (x : Matrix α α A) : LinearMap.det (fstAct co x) = Algebra.norm R (x.det ^ Fintype.card m) := by
  have hmem : ∀ (v : m → α → A) i, antiMap R e v i ∈ antiSub A e := fun v i =>
    (mem_antiSub e).2 ⟨fun j => v j i, rfl⟩
  let Φ₀ : (m → α → A) →ₗ[R] (κ → R) := LinearMap.fst R _ _ ∘ₗ co.e.toLinearMap ∘ₗ antiMap R e
  have hΦ₀ : ∀ v, co.e.symm (Φ₀ v, 0) = antiMap R e v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    exact Prod.ext rfl (hT _ (hmem v)).symm
  have hbij : Function.Bijective Φ₀ := by
    refine ⟨fun v w hvw => ?_, fun z => ?_⟩
    · have h1 : antiMap R e v = antiMap R e w := by rw [← hΦ₀, ← hΦ₀, hvw]
      funext j i
      simpa [antiMap] using congrFun (congrFun h1 i) (e (Sum.inl j))
    · choose y hy using fun i => (mem_antiSub e).1 (rows_of_snd co h hS hT (u := co.e.symm (z, 0)) (by simp) i)
      have h1 : antiMap R e (fun j i => y i j) = co.e.symm (z, 0) := funext fun i => (hy i).symm
      refine ⟨fun j i => y i j, ?_⟩
      show (co.e (antiMap R e _)).1 = z
      rw [h1]; simp
  let Φ := LinearEquiv.ofBijective Φ₀ hbij
  let L : (m → α → A) →ₗ[A] (m → α → A) := LinearMap.pi fun j => (Matrix.toLin' x).comp (LinearMap.proj j)
  have hL : fstAct co x = Φ.toLinearMap ∘ₗ L.restrictScalars R ∘ₗ Φ.symm.toLinearMap := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨v, rfl⟩ := Φ.surjective z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show (co.e (x * co.e.symm (Φ₀ v, 0))).1 = (co.e (antiMap R e (L v))).1
    rw [hΦ₀]
    congr 2
    ext i k
    obtain ⟨j | j, rfl⟩ := e.surjective k <;> simp [antiMap, L, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hL, LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_pi]
  simp

end Lagr

section Value

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] measTup borelTup

/- English proof (translation)
Use `letI : Invertible (2 : AE F E) := (Invertible.map (algebraMap (AF F) (AE F E)) 2).copy 2 (map_ofNat _ 2).symm`. Establish `hsup` using `(isCompl_diagSub_antiSub (A := AE F E) (finSumFinEquiv (m := d) (n := d))).sup_eq_top`. Establish `h1 : ∀ (q : Matrix (Fin n) (Fin n) (AE F E)) u, (co.e u).1 = 0 → (co.e (q * u)).1 = 0` using `fun q u hu => hS _ (rows_mul_mem _ q (rows_of_fst co hsup hS hT hu))`. Establish `h2 : ∀ (q : Matrix (Fin n) (Fin n) (AE F E)) u, (co.e u).2 = 0 → (co.e (q * u)).2 = 0` using `fun q u hu => hT _ (rows_mul_mem _ q (rows_of_snd co hsup hS hT hu))`. Establish `hU` using `IsUWeilPair.isUSplitting h`.

Take `⟨-, ⟨d', hd', hA⟩, -⟩` from `h`. Establish `ht : ∀ w, d'.e w = co.e wᵀ` using `fun w => by rw [← hd', Matrix.transpose_transpose]`. Take `⟨c, hc, hcφ⟩` from `exists_pos_scalar hσ J₂ JX hJ hdet hψ d' _ hA (fun w q hw => by rw [ht] at hw ⊢; rw [Matrix.transpose_mul]; exact h1 _ _ hw) (fun w q hw => by rw [ht] at hw ⊢; rw [Matrix.transpose_mul]; exact h2 _ _ hw) x`. Establish `hcφ' : ∀ φ ∈ schA F κ, om (x, 1) φ 0 = c * φ 0` using `hcφ`. Use `haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis (GlobalTheory.ModuLR.tensBasis F E)`.

Use `haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis (GlobalTheory.ModuLR.tensBasis F E)`. Establish `hg : LinearMap.det (fstAct co (mat x)) = 1`. Establish `hN : Algebra.norm (AF F) (mat x).det = 1` using `congrArg Units.val (GlobalTheory.SiegelValGood.norm_det_eq_one hσ hdet x)`. Rewrite using `[det_fstAct co finSumFinEquiv hsup hS hT, map_pow, hN, one_pow]`. Take `⟨μ, hμ⟩` from `exists_haar F κ`.

Take `⟨φ₁, hφ₁, hφ₁0⟩` from `GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ`. Establish `hval : ∀ z, om (x, 1) φ₁ (fstAct co (mat x) z) = (c • φ₁) z` using `fun z => by`. Establish `hact : actAB (cA σ) ((x, 1) : UA σ JX × UA σ J₂) (co.e.symm (z, 0)) = mat x * co.e.symm (z, 0)`. Simplify using `[actAB, mat]`. Use `apply_coord hψ co (om (x, 1)) (fun φ hφ => hU.impl (x, 1) (co.e.symm (z, 0)) φ hφ) hcφ' (by simp) (by rw [hact]; exact h2 _ _ (by simp)) hφ₁` as an intermediate fact.

Rewrite `this` using `[hact]`. Simplify `this` using `[fstAct_apply]`. Establish `hn : ‖c‖ = 1`. Use `norm_eq_one_of_lintegral_eq (μ := μ) (f := φ₁) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← hU.unit μ hμ (x, 1) φ₁ hφ₁, ← lintegral_comp_of_det μ hμ _ hg (om (x, 1) φ₁)]`.

Simplify using `only [hval]`. Rewrite using `[lintegral_eq_ofReal μ hμ hφ₁]`. Conclude with `(ENNReal.ofReal_pos.2 (integral_normSq_pos μ hμ hφ₁ hφ₁0)).ne'`. Rewrite using `[lintegral_eq_ofReal μ hμ hφ₁]`. Conclude with `ENNReal.ofReal_ne_top`.

Introduce `φ hφ`. Rewrite using `[hcφ' φ hφ, hc, hn, Complex.ofReal_one, one_mul]`.
-/
theorem apply_zero_eq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E)
    (J₂ : Matrix (Fin (d + d)) (Fin (d + d)) E) (hJ : ∀ i j, σ (JX j i) = JX i j) (hdet : JX.det ≠ 0)
    {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F J₂)) κ)
    (hS : ∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0)
    (hT : ∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) {χ : Chr F E}
    {om : UA σ JX × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)}
    (h : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F J₂) co χ 1 om) (x : UA σ JX) :
    ∀ φ ∈ schA F κ, om (x, 1) φ 0 = φ 0 := by
  classical
  letI : Invertible (2 : AE F E) := (Invertible.map (algebraMap (AF F) (AE F E)) 2).copy 2 (map_ofNat _ 2).symm
  have hsup := (isCompl_diagSub_antiSub (A := AE F E) (finSumFinEquiv (m := d) (n := d))).sup_eq_top
  have h1 : ∀ (q : Matrix (Fin n) (Fin n) (AE F E)) u, (co.e u).1 = 0 → (co.e (q * u)).1 = 0 := fun q u hu =>
    hS _ (rows_mul_mem _ q (rows_of_fst co hsup hS hT hu))
  have h2 : ∀ (q : Matrix (Fin n) (Fin n) (AE F E)) u, (co.e u).2 = 0 → (co.e (q * u)).2 = 0 := fun q u hu =>
    hT _ (rows_mul_mem _ q (rows_of_snd co hsup hS hT hu))
  have hU := IsUWeilPair.isUSplitting h
  obtain ⟨-, ⟨d', hd', hA⟩, -⟩ := h
  have ht : ∀ w, d'.e w = co.e wᵀ := fun w => by rw [← hd', Matrix.transpose_transpose]
  obtain ⟨c, hc, hcφ⟩ := exists_pos_scalar hσ J₂ JX hJ hdet hψ d' _ hA
    (fun w q hw => by rw [ht] at hw ⊢; rw [Matrix.transpose_mul]; exact h1 _ _ hw)
    (fun w q hw => by rw [ht] at hw ⊢; rw [Matrix.transpose_mul]; exact h2 _ _ hw) x
  have hcφ' : ∀ φ ∈ schA F κ, om (x, 1) φ 0 = c * φ 0 := hcφ
  haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  have hg : LinearMap.det (fstAct co (mat x)) = 1 := by
    have hN : Algebra.norm (AF F) (mat x).det = 1 := congrArg Units.val (GlobalTheory.SiegelValGood.norm_det_eq_one hσ hdet x)
    rw [det_fstAct co finSumFinEquiv hsup hS hT, map_pow, hN, one_pow]
  obtain ⟨μ, hμ⟩ := exists_haar F κ
  obtain ⟨φ₁, hφ₁, hφ₁0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  have hval : ∀ z, om (x, 1) φ₁ (fstAct co (mat x) z) = (c • φ₁) z := fun z => by
    have hact : actAB (cA σ) ((x, 1) : UA σ JX × UA σ J₂) (co.e.symm (z, 0)) = mat x * co.e.symm (z, 0) := by
      simp [actAB, mat]
    have := apply_coord hψ co (om (x, 1)) (fun φ hφ => hU.impl (x, 1) (co.e.symm (z, 0)) φ hφ) hcφ' (by simp)
      (by rw [hact]; exact h2 _ _ (by simp)) hφ₁
    rw [hact] at this
    simpa [fstAct_apply] using this
  have hn : ‖c‖ = 1 := by
    refine norm_eq_one_of_lintegral_eq (μ := μ) (f := φ₁) ?_ ?_ ?_
    · rw [← hU.unit μ hμ (x, 1) φ₁ hφ₁, ← lintegral_comp_of_det μ hμ _ hg (om (x, 1) φ₁)]
      simp only [hval]
    · rw [lintegral_eq_ofReal μ hμ hφ₁]
      exact (ENNReal.ofReal_pos.2 (integral_normSq_pos μ hμ hφ₁ hφ₁0)).ne'
    · rw [lintegral_eq_ofReal μ hμ hφ₁]
      exact ENNReal.ofReal_ne_top
  intro φ hφ
  rw [hcφ' φ hφ, hc, hn, Complex.ofReal_one, one_mul]

end Value

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ _ _ _ _ _ co _ hS hT om₂ hom₂ e hbij hadm hint x Φ₁ h₁ Φ₂ h₂`. Use `letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _`. Establish `hψ` using `hP.base.std`. Establish `hU` using `IsUWeilPair.isUSplitting hP.weil`. Establish `hU₂` using `IsUWeilPair.isUSplitting hom₂`.

Establish `hdet : Xs.J.det ≠ 0` using `(GlobalTheory.isUnit_det_of_isHerm F E σ B n Xs r s' hP.herm).ne_zero`. Establish `hz` using `apply_zero_eq hP.base.cm Xs.J W₂.J hP.herm.herm hdet hψ co hS hT hom₂ x`. Establish `hbox : ∀ f ∈ schA F (Fin n × Fin d), ∀ g ∈ schA F (Fin n × Fin d), boxC f g ∈ schA F _` using `fun f hf g hg => GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F _ _ f hf (star g) (GlobalTheory.SchAConj.star_mem_schA F _ g hg)`. Establish `hrho : ∀ w, ∀ f ∈ schA F (Fin n × Fin d), M.co.rho B.ψ w f ∈ schA F _` using `fun w f hf => GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hψ _ _ f hf`. Establish `hsb : ∀ u, ∀ f ∈ schA F (Fin n × Fin d), ∀ g ∈ schA F (Fin n × Fin d), co.rho B.ψ u (e (boxC f g)) = e (boxC (M.co.rho B.ψ (topC u) f) (M.co.rho B.ψ (botC u) g))` using `fun u f hf g hg => by`.

Rewrite using `[← hint u _ (hbox f hf g hg)]`. Conclude with `congrArg e (GlobalTheory.DblBoxRho.schr_boxFun B.ψ (GlobalTheory.HeisLineTheta.norm_psi hψ) _ _ f g)`. Take `⟨μ, hμ⟩` from `exists_haar F (Fin n × Fin d)`. Take `⟨k, hk⟩` from `GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral F B.ψ hψ (Fin n × Fin d) (LinearMap.proj 0 ∘ₗ e) (hadm _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms _)) (fun a b Ψ hΨ => by`. Set `w` to `M.co.e.symm (a, b)`.

Set `u : Matrix (Fin n) (Fin (d + d)) (AE F E)` to `Matrix.of fun i => pairVec finSumFinEquiv (w i) (w i)`. Establish `ht : topC u = w` using `by ext i j; simp only [topC, u, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply, id, pairVec_inl]`. Establish `hb : botC u = w` using `by ext i j; simp only [botC, u, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply, id, pairVec_inr]`. Establish `hd : dblE M.co u = (Sum.elim a a, Sum.elim b (-b))` using `by simp [dblE, ht, hb, w]`. Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply]`.

Rewrite using `[← hd, hint u Ψ hΨ, rho_zero_of_fst _ co (hS u fun i => (mem_diagSub _).2 ⟨w i, rfl⟩)]) μ hμ`. Establish `hk' : ∀ f ∈ schA F (Fin n × Fin d), ∀ g ∈ schA F (Fin n × Fin d), e (boxC f g) 0 = k * ∫ z, f z * star (g z) ∂μ` using `fun f hf g hg => hk _ (hbox f hf g hg)`. Establish `hxx : mat x * mat x⁻¹ = 1` using `Units.mul_inv _`. Use function extensionality and compare the values at `z`. Set `u` to `co.e.symm (z, 0)`.

Establish `hu : (co.e u).2 = 0` using `by simp [u]`. Establish `hzu : z = (co.e u).1` using `by simp [u]`. Establish `a₂ : actAB (cA σ) ((x, 1) : UA σ Xs.J × UA σ W₂.J) (mat x⁻¹ * u) = u` using `by show mat x * (mat x⁻¹ * u) * (1 : Matrix _ _ (AE F E))ᵀ = u`. Rewrite using `[Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hxx, Matrix.one_mul]`. Establish `a₁ : ∀ w : Matrix (Fin n) (Fin d) (AE F E), actAB (cA σ) ((x, 1) : UA σ Xs.J × UA σ W.J) (mat x⁻¹ * w) = w` using `fun w => by show mat x * (mat x⁻¹ * w) * (1 : Matrix _ _ (AE F E))ᵀ = w`.

Rewrite using `[Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hxx, Matrix.one_mul]`. Establish `ht : topC (mat x⁻¹ * u) = mat x⁻¹ * topC u` using `rfl`. Establish `hb : botC (mat x⁻¹ * u) = mat x⁻¹ * botC u` using `rfl`. Establish `hm` using `hbij.mapsTo (hbox _ h₁ _ h₂)`. Establish `i₂` using `hU₂.impl (x, 1) (mat x⁻¹ * u) _ hm`.

Establish `i₁` using `hU.impl (x, 1) (mat x⁻¹ * topC u) _ h₁`. Establish `i₁'` using `hU.impl (x, 1) (mat x⁻¹ * botC u) _ h₂`. Rewrite `i₂` using `[a₂, hsb _ _ h₁ _ h₂, ht, hb]`. Rewrite `i₁`, `i₁'` using `[a₁]`. Rewrite using `[hzu, ← rho_zero_of_snd B.ψ co hu (om₂ _ _), ← rho_zero_of_snd B.ψ co hu (e _), ← i₂, hsb _ _ (hU.pres _ _ h₁) _ (hU.pres _ _ h₂), ← i₁, ← i₁', hz _ (hbij.mapsTo (hbox _ (hrho _ _ h₁) _ (hrho _ _ h₂))), hk' _ (hrho _ _ h₁) _ (hrho _ _ h₂), hk' _ (hU.pres _ _ (hrho _ _ h₁)) _ (hU. …`.
-/
theorem om_boxC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    ∀ x : UA σ Xs.J, ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      om₂ (x, 1) (e (boxC Φ₁ Φ₂)) = e (boxC (om (x, 1) Φ₁) (om (x, 1) Φ₂)) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ _ _ _ _ _ co _ hS hT om₂ hom₂ e hbij hadm hint x Φ₁ h₁ Φ₂ h₂
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  have hψ := hP.base.std
  have hU := IsUWeilPair.isUSplitting hP.weil
  have hU₂ := IsUWeilPair.isUSplitting hom₂
  have hdet : Xs.J.det ≠ 0 := (GlobalTheory.isUnit_det_of_isHerm F E σ B n Xs r s' hP.herm).ne_zero
  have hz := apply_zero_eq hP.base.cm Xs.J W₂.J hP.herm.herm hdet hψ co hS hT hom₂ x
  have hbox : ∀ f ∈ schA F (Fin n × Fin d), ∀ g ∈ schA F (Fin n × Fin d), boxC f g ∈ schA F _ := fun f hf g hg =>
    GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F _ _ f hf (star g) (GlobalTheory.SchAConj.star_mem_schA F _ g hg)
  have hrho : ∀ w, ∀ f ∈ schA F (Fin n × Fin d), M.co.rho B.ψ w f ∈ schA F _ := fun w f hf =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hψ _ _ f hf
  have hsb : ∀ u, ∀ f ∈ schA F (Fin n × Fin d), ∀ g ∈ schA F (Fin n × Fin d),
      co.rho B.ψ u (e (boxC f g)) = e (boxC (M.co.rho B.ψ (topC u) f) (M.co.rho B.ψ (botC u) g)) := fun u f hf g hg => by
    rw [← hint u _ (hbox f hf g hg)]
    exact congrArg e (GlobalTheory.DblBoxRho.schr_boxFun B.ψ (GlobalTheory.HeisLineTheta.norm_psi hψ) _ _ f g)
  obtain ⟨μ, hμ⟩ := exists_haar F (Fin n × Fin d)
  obtain ⟨k, hk⟩ := GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral F B.ψ hψ (Fin n × Fin d) (LinearMap.proj 0 ∘ₗ e)
    (hadm _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms _)) (fun a b Ψ hΨ => by
      let w := M.co.e.symm (a, b)
      let u : Matrix (Fin n) (Fin (d + d)) (AE F E) := Matrix.of fun i => pairVec finSumFinEquiv (w i) (w i)
      have ht : topC u = w := by ext i j; simp only [topC, u, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply, id, pairVec_inl]
      have hb : botC u = w := by ext i j; simp only [botC, u, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply, id, pairVec_inr]
      have hd : dblE M.co u = (Sum.elim a a, Sum.elim b (-b)) := by simp [dblE, ht, hb, w]
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [← hd, hint u Ψ hΨ, rho_zero_of_fst _ co (hS u fun i => (mem_diagSub _).2 ⟨w i, rfl⟩)]) μ hμ
  have hk' : ∀ f ∈ schA F (Fin n × Fin d), ∀ g ∈ schA F (Fin n × Fin d),
      e (boxC f g) 0 = k * ∫ z, f z * star (g z) ∂μ := fun f hf g hg => hk _ (hbox f hf g hg)
  have hxx : mat x * mat x⁻¹ = 1 := Units.mul_inv _
  funext z
  let u := co.e.symm (z, 0)
  have hu : (co.e u).2 = 0 := by simp [u]
  have hzu : z = (co.e u).1 := by simp [u]
  have a₂ : actAB (cA σ) ((x, 1) : UA σ Xs.J × UA σ W₂.J) (mat x⁻¹ * u) = u := by
    show mat x * (mat x⁻¹ * u) * (1 : Matrix _ _ (AE F E))ᵀ = u
    rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hxx, Matrix.one_mul]
  have a₁ : ∀ w : Matrix (Fin n) (Fin d) (AE F E),
      actAB (cA σ) ((x, 1) : UA σ Xs.J × UA σ W.J) (mat x⁻¹ * w) = w := fun w => by
    show mat x * (mat x⁻¹ * w) * (1 : Matrix _ _ (AE F E))ᵀ = w
    rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hxx, Matrix.one_mul]
  have ht : topC (mat x⁻¹ * u) = mat x⁻¹ * topC u := rfl
  have hb : botC (mat x⁻¹ * u) = mat x⁻¹ * botC u := rfl
  have hm := hbij.mapsTo (hbox _ h₁ _ h₂)
  have i₂ := hU₂.impl (x, 1) (mat x⁻¹ * u) _ hm
  have i₁ := hU.impl (x, 1) (mat x⁻¹ * topC u) _ h₁
  have i₁' := hU.impl (x, 1) (mat x⁻¹ * botC u) _ h₂
  rw [a₂, hsb _ _ h₁ _ h₂, ht, hb] at i₂
  rw [a₁] at i₁ i₁'
  rw [hzu, ← rho_zero_of_snd B.ψ co hu (om₂ _ _), ← rho_zero_of_snd B.ψ co hu (e _), ← i₂,
    hsb _ _ (hU.pres _ _ h₁) _ (hU.pres _ _ h₂), ← i₁, ← i₁',
    hz _ (hbij.mapsTo (hbox _ (hrho _ _ h₁) _ (hrho _ _ h₂))), hk' _ (hrho _ _ h₁) _ (hrho _ _ h₂),
    hk' _ (hU.pres _ _ (hrho _ _ h₁)) _ (hU.pres _ _ (hrho _ _ h₂)),
    integral_mul_star_eq μ hμ (om (x, 1)) (hU.pres _) (hU.unit μ hμ _) (hrho _ _ h₁) (hrho _ _ h₂)]

end GlobalTheory.DblUnitaryBox

end
