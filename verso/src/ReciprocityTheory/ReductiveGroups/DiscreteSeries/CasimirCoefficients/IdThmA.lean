import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

namespace IdA

/- English proof (translation)
Establish `e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0}`. Use extensionality with `z`. Simplify using `[OmegaSet]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_ne_fun (contDiff_lead (m := 0) _).continuous continuous_const`.
-/
lemma isOpen_omega : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (contDiff_lead (m := 0) _).continuous continuous_const

/- English proof (translation)
Introduce `_ hz` and use `(contDiffAt_phiM μ hz (m := 2)).contDiffWithinAt`.
-/
lemma contDiffOn_phiM_two (μ : Fin n → ℤ) : ContDiffOn ℂ 2 (PhiM μ) (OmegaSet n) :=
  fun _ hz => (contDiffAt_phiM μ hz (m := 2)).contDiffWithinAt

/- English proof (translation)
The claim follows from `(contDiffOn_phiM_two μ).continuousOn_fderiv_of_isOpen isOpen_omega (by norm_num)`.
-/
lemma continuousOn_fderiv_phiM_alt (μ : Fin n → ℤ) : ContinuousOn (fderiv ℂ (PhiM μ)) (OmegaSet n) :=
  (contDiffOn_phiM_two μ).continuousOn_fderiv_of_isOpen isOpen_omega (by norm_num)

/- English proof (translation)
The claim follows from `((contDiffOn_phiM_two μ).fderiv_of_isOpen isOpen_omega (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen isOpen_omega le_rfl`.
-/
lemma continuousOn_second_fderiv_phiM (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (fderiv ℂ (PhiM μ))) (OmegaSet n) :=
  ((contDiffOn_phiM_two μ).fderiv_of_isOpen isOpen_omega (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
    isOpen_omega le_rfl

/- English proof (translation)
The claim follows from `(continuous_toM ε).comp continuous_subtype_val`.
-/
lemma continuous_toMK : Continuous fun k : KG ε => toMK k :=
  (continuous_toM ε).comp continuous_subtype_val

/- English proof (translation)
The claim follows from `continuous_toMK.comp continuous_inv`.
-/
lemma continuous_toMK_inv : Continuous fun k : KG ε => toMK k⁻¹ :=
  continuous_toMK.comp continuous_inv

/- English proof (translation)
Establish `h : Continuous fun k : KG ε => T.op k` using `continuous_subtype_val.comp T.cont`. Conclude with `(h.mul continuous_const).mul (h.comp continuous_inv)`.
-/
lemma continuous_P (T : KType ε Λ) : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := by
  have h : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  exact (h.mul continuous_const).mul (h.comp continuous_inv)

/- English proof (translation)
The claim follows from `((continuous_toMK_inv.comp continuous_snd).matrix_mul (continuous_const.add (continuous_fst.smul continuous_const))).matrix_mul (continuous_toMK.comp continuous_snd)`.
-/
lemma continuous_cline (a b : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun p : ℂ × KG ε => toMK p.2⁻¹ * (a + p.1 • b) * toMK p.2 :=
  ((continuous_toMK_inv.comp continuous_snd).matrix_mul
    (continuous_const.add (continuous_fst.smul continuous_const))).matrix_mul
    (continuous_toMK.comp continuous_snd)

/- English proof (translation)
Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
lemma cline_eq (k : KG ε) (a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    toMK k⁻¹ * (a + s • b) * toMK k = toMK k⁻¹ * a * toMK k + s • (toMK k⁻¹ * b * toMK k) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `h` using `((hasDerivAt_id s).smul_const (toMK k⁻¹ * b * toMK k)).const_add (toMK k⁻¹ * a * toMK k)`. Simplify using `only [id, one_smul] at h`. Conclude with `h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => cline_eq k a b s)`.
-/
lemma hasDerivAt_cline (k : KG ε) (a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => toMK k⁻¹ * (a + s • b) * toMK k) (toMK k⁻¹ * b * toMK k) s := by
  have h := ((hasDerivAt_id s).smul_const (toMK k⁻¹ * b * toMK k)).const_add (toMK k⁻¹ * a * toMK k)
  simp only [id, one_smul] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => cline_eq k a b s)

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts (muK ε)` using `by unfold muK; infer_instance`. Establish `: IsFiniteMeasure (muK ε)` using `inferInstance`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp hS s0 hs0`. Establish `hcl : Metric.closedBall s0 (r / 2) ⊆ S` using `(Metric.closedBall_subset_ball (half_lt_self hr)).trans hball`. Establish `hK : IsCompact (Metric.closedBall s0 (r / 2) ×ˢ (Set.univ : Set (KG ε)))` using `(isCompact_closedBall s0 _).prod isCompact_univ`.

Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hcl le_rfl))`. Establish `hin : ∀ s ∈ Metric.ball s0 (r / 2), s ∈ S` using `fun s hs => hcl (Metric.ball_subset_closedBall hs)`. Establish `hc : ∀ s ∈ S, Continuous (F s)` using `fun s hs => hF.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩`. Establish `hc' : Continuous (F' s0)` using `hF'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs0, trivial⟩`. Establish `hi : Integrable (F s0) (muK ε)` using `integrableOn_univ.mp ((hc s0 hs0).continuousOn.integrableOn_compact isCompact_univ)`.

Conclude with `(hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C) (Metric.ball_mem_nhds s0 (half_pos hr)) (Filter.eventually_of_mem (Metric.ball_mem_nhds s0 (half_pos hr)) fun s hs => (hc s (hin s hs)).aestronglyMeasurable) hi hc'.aestronglyMeasurable (Filter.Eventually.of_ …`.
-/
lemma hasDerivAt_intK [CompactSpace (KG ε)] (T : KType ε Λ) (F F' : ℂ → KG ε → (T.V →L[ℂ] T.V))
    {S : Set ℂ} (hS : IsOpen S)
    (hF : ContinuousOn (fun p : ℂ × KG ε => F p.1 p.2) (S ×ˢ Set.univ))
    (hF' : ContinuousOn (fun p : ℂ × KG ε => F' p.1 p.2) (S ×ˢ Set.univ))
    (hd : ∀ s ∈ S, ∀ k, HasDerivAt (fun s => F s k) (F' s k) s) {s0 : ℂ} (hs0 : s0 ∈ S) :
    HasDerivAt (fun s => ∫ k, F s k ∂(muK ε)) (∫ k, F' s0 k ∂(muK ε)) s0 := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS s0 hs0
  have hcl : Metric.closedBall s0 (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact (Metric.closedBall s0 (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall s0 _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hcl le_rfl))
  have hin : ∀ s ∈ Metric.ball s0 (r / 2), s ∈ S := fun s hs => hcl (Metric.ball_subset_closedBall hs)
  have hc : ∀ s ∈ S, Continuous (F s) := fun s hs =>
    hF.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩
  have hc' : Continuous (F' s0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs0, trivial⟩
  have hi : Integrable (F s0) (muK ε) :=
    integrableOn_univ.mp ((hc s0 hs0).continuousOn.integrableOn_compact isCompact_univ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds s0 (half_pos hr))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds s0 (half_pos hr))
      fun s hs => (hc s (hin s hs)).aestronglyMeasurable)
    hi hc'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k s hs => hC (s, k) ⟨Metric.ball_subset_closedBall hs, trivial⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k s hs => hd s (hin s hs) k)).2

def dPhi2 (μ : Fin n → ℤ) (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  fderiv ℂ (PhiM μ) p.1 p.2

/- English proof (translation)
Establish `hf : ContDiffAt ℂ 2 (Function.uncurry fun (_ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin n) (Fin n) ℂ) => PhiM μ y) (p, p.1)` using `(contDiffAt_phiM μ hp (m := 2)).comp (p, p.1) contDiffAt_snd`. Conclude with `(hf.fderiv contDiffAt_fst (by norm_num)).clm_apply contDiffAt_snd`.
-/
lemma contDiffAt_dPhi2 (μ : Fin n → ℤ) {p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ}
    (hp : p.1 ∈ OmegaSet n) : ContDiffAt ℂ 1 (dPhi2 μ) p := by
  have hf : ContDiffAt ℂ 2 (Function.uncurry fun (_ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
      (y : Matrix (Fin n) (Fin n) ℂ) => PhiM μ y) (p, p.1) :=
    (contDiffAt_phiM μ hp (m := 2)).comp (p, p.1) contDiffAt_snd
  exact (hf.fderiv contDiffAt_fst (by norm_num)).clm_apply contDiffAt_snd

/- English proof (translation)
Introduce `p hp` and use `(contDiffAt_dPhi2 μ hp.1).continuousAt.continuousWithinAt`.
-/
lemma continuousOn_dPhi2 (μ : Fin n → ℤ) : ContinuousOn (dPhi2 μ) (OmegaSet n ×ˢ Set.univ) :=
  fun p hp => (contDiffAt_dPhi2 μ hp.1).continuousAt.continuousWithinAt

/- English proof (translation)
The claim follows from `ContDiffOn.continuousOn_fderiv_of_isOpen (fun p hp => (contDiffAt_dPhi2 μ hp.1).contDiffWithinAt) (isOpen_omega.prod isOpen_univ) le_rfl`.
-/
lemma continuousOn_fderiv_dPhi2 (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (dPhi2 μ)) (OmegaSet n ×ˢ Set.univ) :=
  ContDiffOn.continuousOn_fderiv_of_isOpen (fun p hp => (contDiffAt_dPhi2 μ hp.1).contDiffWithinAt)
    (isOpen_omega.prod isOpen_univ) le_rfl

end IdA

/- English proof (translation)
Use `compactSpace_KG ε` as an intermediate fact. Establish `hS : IsOpen ((fun s : ℂ => a₀ + s • a₁) ⁻¹' U)` using `hUo.preimage (continuous_const.add (continuous_id.smul continuous_const))`. Establish `hγ : Continuous fun p : ℂ × KG ε => (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2)` using `(IdA.continuous_cline a₀ a₁).prodMk (IdA.continuous_cline b₀ b₁)`. Establish `hmaps : Set.MapsTo (fun p : ℂ × KG ε => (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2)) (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) (OmegaSet n ×ˢ Set.univ)` using `fun p hp => ⟨hU _ hp.1 p.2, trivial⟩`. Establish `hP : ContinuousOn (fun p : ℂ × KG ε => T.op p.2 * projW T * T.op p.2⁻¹) (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ)` using `((IdA.continuous_P T).comp continuous_snd).continuousOn`.

Establish `hd1 : Continuous fun p : ℂ × KG ε => (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2)` using `(((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul (IdA.continuous_toMK.comp continuous_snd)).prodMk (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul (IdA.continuous_toMK.comp continuous_snd))`. Establish `hF : ContinuousOn (fun p : ℂ × KG ε => IdA.dPhi2 μ (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹)) (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ)` using `((IdA.continuousOn_dPhi2 μ).comp hγ.continuousOn hmaps).smul hP`. Establish `hF' : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (IdA.dPhi2 μ) (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹)) (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ S …` using `(((IdA.continuousOn_fderiv_dPhi2 μ).comp hγ.continuousOn hmaps).clm_apply hd1.continuousOn).smul hP`. Establish `hd : ∀ s ∈ (fun s : ℂ => a₀ + s • a₁) ⁻¹' U, ∀ k : KG ε, HasDerivAt (fun s => IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k) • (T.op k * projW T * T.op k⁻¹)) (fderiv ℂ (IdA.dPhi2 μ) (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * …`. Introduce `s hs k`.

Establish `hq` using `(IdA.hasDerivAt_cline k a₀ a₁ s).prodMk (IdA.hasDerivAt_cline k b₀ b₁ s)`. Establish `hD` using `((IdA.contDiffAt_dPhi2 μ (p := (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k)) (hU _ hs k)).differentiableAt one_ne_zero).hasFDerivAt`. Conclude with `(hD.comp_hasDerivAt s hq).smul_const (T.op k * projW T * T.op k⁻¹)`. Conclude with `(IdA.hasDerivAt_intK T _ _ hS hF hF' hd hs₀).differentiableAt`.
-/
theorem line_int_differentiableAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hUo : IsOpen U) (hU : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n)
    (a₀ a₁ b₀ b₁ : Matrix (Fin n) (Fin n) ℂ) {s₀ : ℂ} (hs₀ : a₀ + s₀ • a₁ ∈ U) :
    DifferentiableAt ℂ (fun s : ℂ => ∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) s₀ := by
  have := compactSpace_KG ε
  have hS : IsOpen ((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) :=
    hUo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hγ : Continuous fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) :=
    (IdA.continuous_cline a₀ a₁).prodMk (IdA.continuous_cline b₀ b₁)
  have hmaps : Set.MapsTo (fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) (OmegaSet n ×ˢ Set.univ) :=
    fun p hp => ⟨hU _ hp.1 p.2, trivial⟩
  have hP : ContinuousOn (fun p : ℂ × KG ε => T.op p.2 * projW T * T.op p.2⁻¹)
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuous_P T).comp continuous_snd).continuousOn
  have hd1 : Continuous fun p : ℂ × KG ε => (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) :=
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd)).prodMk
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd))
  have hF : ContinuousOn (fun p : ℂ × KG ε => IdA.dPhi2 μ (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2,
      toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuousOn_dPhi2 μ).comp hγ.continuousOn hmaps).smul hP
  have hF' : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (IdA.dPhi2 μ)
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2)
      (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    (((IdA.continuousOn_fderiv_dPhi2 μ).comp hγ.continuousOn hmaps).clm_apply hd1.continuousOn).smul hP
  have hd : ∀ s ∈ (fun s : ℂ => a₀ + s • a₁) ⁻¹' U, ∀ k : KG ε, HasDerivAt
      (fun s => IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k) •
        (T.op k * projW T * T.op k⁻¹))
      (fderiv ℂ (IdA.dPhi2 μ) (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k)
        (toMK k⁻¹ * a₁ * toMK k, toMK k⁻¹ * b₁ * toMK k) • (T.op k * projW T * T.op k⁻¹)) s := by
    intro s hs k
    have hq := (IdA.hasDerivAt_cline k a₀ a₁ s).prodMk (IdA.hasDerivAt_cline k b₀ b₁ s)
    have hD := ((IdA.contDiffAt_dPhi2 μ (p := (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k)) (hU _ hs k)).differentiableAt one_ne_zero).hasFDerivAt
    exact (hD.comp_hasDerivAt s hq).smul_const (T.op k * projW T * T.op k⁻¹)
  exact (IdA.hasDerivAt_intK T _ _ hS hF hF' hd hs₀).differentiableAt

end ReciprocityTheory.ChartRestriction.DS.S7
