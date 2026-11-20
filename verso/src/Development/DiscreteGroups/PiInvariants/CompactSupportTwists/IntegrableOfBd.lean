import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IntegralMulRightFd
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut

noncomputable section

set_option linter.all false

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.ExpDeriv

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

def PairBd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (ψ φ : Sm E n) (u : ℝ → ℂ) (Ω : Set (GA E n)), IsCuspForm ψ → (∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) →
  IsAutForm φ → Continuous u → HasCompactSupport u → IsCompact Ω →
  ∃ C : ℝ, (∀ x : H E n 0, ∀ y ∈ Ω, ∀ y' ∈ Ω, ‖ψ.1 (x.1 * y) * u (ldet x) * φ.1 (x.1 * y')‖ ≤ C) ∧
    D.ν {x | u (ldet x) ≠ 0} < ⊤

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sInf E : Cinf E → Ad E)` using `(continuous_infEq E).prodMk continuous_const`. Conclude with `continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)`.
-/
theorem cont_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) (Cinf E)) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) (Cinf E)) := Matrix.linftyOpNormedAlgebra`. Use `haveI : CompleteSpace (Matrix (Fin n) (Fin n) (Cinf E)) := FiniteDimensional.complete ℝ _`. Establish `hc : Continuous fun t : ℝ => (NormedSpace.exp (t • Matrix.of X) : Matrix (Fin n) (Fin n) (Cinf E))` using `continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.of X) t).continuousAt`. Establish `e : ∀ t, ((expGL X t)⁻¹ : GL (Fin n) (Cinf E)) = expGL X (-t)` using `fun t => inv_eq_of_mul_eq_one_right (by rw [← expGL_add, add_neg_cancel, expGL_zero])`.

Use `Units.continuous_iff.2 ⟨hc, ?_⟩` and prove the remaining obligations. Simplify using `only [e]`. Conclude with `hc.comp continuous_neg`.
-/
theorem cont_expGL (X : Lie E n) : Continuous (expGL X) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hc : Continuous fun t : ℝ => (NormedSpace.exp (t • Matrix.of X) : Matrix (Fin n) (Fin n) (Cinf E)) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.of X) t).continuousAt
  have e : ∀ t, ((expGL X t)⁻¹ : GL (Fin n) (Cinf E)) = expGL X (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← expGL_add, add_neg_cancel, expGL_zero])
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  simp only [e]
  exact hc.comp continuous_neg

/- English proof (translation)
Set `f : ℝ → ℝ` to `fun t => logAbs (infGL E n (expGL X t)).val.det`. Establish `hadd : ∀ s t, f (s + t) = f s + f t` using `fun s t => by show logAbs (infGL E n (expGL X (s + t))).val.det = _`. Rewrite using `[expGL_add, map_mul]`. Conclude with `logAbs_det_mul _ _`. Establish `hcont : Continuous f` using `continuous_logAbs_det.comp (cont_infGL.comp (cont_expGL X))`.

Set `F : ℝ →+ ℝ` to `AddMonoidHom.mk' f hadd`. Establish `hF : Continuous (F : ℝ → ℝ)` using `hcont`. Establish `h1 : ∀ t, f t = t * f 1` using `fun t => by`. Use `map_real_smul F hF t 1` as an intermediate fact. Simplify `this` using `[F]`.

Use `⟨f 1, fun x t => ?_⟩` and prove the remaining obligations. Rewrite using `[ldet_mul_right]`. Conclude with `congrArg _ (h1 t)`.
-/
theorem ldet_expGL (X : Lie E n) : ∃ c : ℝ, ∀ (x : H E n 0) (t : ℝ),
    ldet (x * ((infGL E n (expGL X t), 1) : H E n 0)) = ldet x + t * c := by
  let f : ℝ → ℝ := fun t => logAbs (infGL E n (expGL X t)).val.det
  have hadd : ∀ s t, f (s + t) = f s + f t := fun s t => by
    show logAbs (infGL E n (expGL X (s + t))).val.det = _
    rw [expGL_add, map_mul]
    exact logAbs_det_mul _ _
  have hcont : Continuous f := continuous_logAbs_det.comp (cont_infGL.comp (cont_expGL X))
  let F : ℝ →+ ℝ := AddMonoidHom.mk' f hadd
  have hF : Continuous (F : ℝ → ℝ) := hcont
  have h1 : ∀ t, f t = t * f 1 := fun t => by
    have := map_real_smul F hF t 1
    simpa [F] using this
  refine ⟨f 1, fun x t => ?_⟩
  rw [ldet_mul_right]
  exact congrArg _ (h1 t)

/- English proof (translation)
Distinguish the cases in `h : s + t * c ∈ tsupport v`. Establish `h1` using `hR h`. Rewrite `h1` using `[Metric.mem_closedBall, Real.dist_eq, sub_zero]`. Establish `h2 : |t * c| ≤ |c|` using `by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht`. Take `⟨a1, a2⟩` from `abs_le.1 h1`.

Take `⟨b1, b2⟩` from `abs_le.1 h2`. Establish `h3 : |s| ≤ R' + |c|` using `abs_le.2 ⟨by linarith, by linarith⟩`. Rewrite using `[min_eq_left (by linarith), max_eq_right zero_le_one, mul_one]`. Conclude with `(hM _).trans hMM`. Establish `h0 : v (s + t * c) = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `h (subset_tsupport _ (Function.mem_support.2 hne))`. Rewrite using `[h0, norm_zero]`. Conclude with `mul_nonneg hM0 (le_max_left _ _)`.
-/
theorem major_one (v : ℝ → ℂ) {M R : ℝ} (hM : ∀ x, ‖v x‖ ≤ M) (hR : tsupport v ⊆ Metric.closedBall 0 R) (c : ℝ)
    {R' M' : ℝ} (hRR : R ≤ R') (hMM : M ≤ M') (hM0 : 0 ≤ M') (s t : ℝ) (ht : |t| ≤ 1) :
    ‖v (s + t * c)‖ ≤ M' * max 0 (min 1 (R' + |c| + 1 - |s|)) := by
  by_cases h : s + t * c ∈ tsupport v
  · have h1 := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    have h2 : |t * c| ≤ |c| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht
    obtain ⟨a1, a2⟩ := abs_le.1 h1
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    have h3 : |s| ≤ R' + |c| := abs_le.2 ⟨by linarith, by linarith⟩
    rw [min_eq_left (by linarith), max_eq_right zero_le_one, mul_one]
    exact (hM _).trans hMM
  · have h0 : v (s + t * c) = 0 := by
      by_contra hne
      exact h (subset_tsupport _ (Function.mem_support.2 hne))
    rw [h0, norm_zero]
    exact mul_nonneg hM0 (le_max_left _ _)

/- English proof (translation)
Take `⟨M₁, hM₁⟩` from `h₁.bounded_above_of_compact_support s₁`. Take `⟨M₂, hM₂⟩` from `h₂.bounded_above_of_compact_support s₂`. Take `⟨R₁, hR₁⟩` from `s₁.isCompact.isBounded.subset_closedBall (0 : ℝ)`. Take `⟨R₂, hR₂⟩` from `s₂.isCompact.isBounded.subset_closedBall (0 : ℝ)`. Use `set R := max R₁ R₂`.

Use `set M := max M₁ 0 + max M₂ 0`. Establish `hM0 : 0 ≤ M` using `add_nonneg (le_max_right _ _) (le_max_right _ _)`. Use `⟨fun s => M * max 0 (min 1 (R + |c| + 1 - |s|)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_const.mul (continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs)))`. Use `HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + |c| + 1)) fun s hs => ?_` and prove the remaining obligations.

Rewrite `hs` using `[Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le]`. Establish `: min 1 (R + |c| + 1 - |s|) ≤ 0` using `(min_le_right _ _).trans (by linarith)`. Simplify using `only [max_eq_left this, mul_zero]`. Conclude with `fun s => mul_nonneg hM0 (le_max_left _ _)`. Introduce `s t ht`.

Conclude with `⟨major_one v₁ hM₁ hR₁ c (le_max_left _ _) ((le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))) hM0 s t ht, major_one v₂ hM₂ hR₂ c (le_max_right _ _) ((le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))) hM0 s t ht⟩`.
-/
theorem exists_major (v₁ v₂ : ℝ → ℂ) (h₁ : Continuous v₁) (h₂ : Continuous v₂) (s₁ : HasCompactSupport v₁)
    (s₂ : HasCompactSupport v₂) (c : ℝ) : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
      ∀ s t, |t| ≤ 1 → ‖v₁ (s + t * c)‖ ≤ w s ∧ ‖v₂ (s + t * c)‖ ≤ w s := by
  obtain ⟨M₁, hM₁⟩ := h₁.bounded_above_of_compact_support s₁
  obtain ⟨M₂, hM₂⟩ := h₂.bounded_above_of_compact_support s₂
  obtain ⟨R₁, hR₁⟩ := s₁.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨R₂, hR₂⟩ := s₂.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set R := max R₁ R₂
  set M := max M₁ 0 + max M₂ 0
  have hM0 : 0 ≤ M := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun s => M * max 0 (min 1 (R + |c| + 1 - |s|)), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul (continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs)))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + |c| + 1)) fun s hs => ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hs
    have : min 1 (R + |c| + 1 - |s|) ≤ 0 := (min_le_right _ _).trans (by linarith)
    simp only [max_eq_left this, mul_zero]
  · exact fun s => mul_nonneg hM0 (le_max_left _ _)
  · intro s t ht
    exact ⟨major_one v₁ hM₁ hR₁ c (le_max_left _ _) ((le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _)))
        hM0 s t ht,
      major_one v₂ hM₂ hR₂ c (le_max_right _ _) ((le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _)))
        hM0 s t ht⟩

/- English proof (translation)
Establish `e : ‖a * ((s : ℝ) : ℂ) * b‖ = ‖a‖ * s * ‖b‖`. Rewrite using `[norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]`. Establish `h1 : ‖star (a * v) * b‖ ≤ k * (‖a‖ * s * ‖b‖)`. Rewrite using `[norm_mul, norm_star, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨h1.trans (mul_le_mul_of_nonneg_left (by rw [← e]; exact h) hk), fun h0 => ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[h0]`. Simplify using `only [mul_zero, zero_mul] at h1`. Conclude with `norm_le_zero_iff.1 h1`.
-/
theorem pt_bd {a b v : ℂ} {s k C : ℝ} (hs : 0 ≤ s) (hk : 0 ≤ k) (hv : ‖v‖ ≤ k * s)
    (h : ‖a * ((s : ℝ) : ℂ) * b‖ ≤ C) : ‖star (a * v) * b‖ ≤ k * C ∧ (s = 0 → star (a * v) * b = 0) := by
  have e : ‖a * ((s : ℝ) : ℂ) * b‖ = ‖a‖ * s * ‖b‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h1 : ‖star (a * v) * b‖ ≤ k * (‖a‖ * s * ‖b‖) := by
    rw [norm_mul, norm_star, norm_mul]
    calc ‖a‖ * ‖v‖ * ‖b‖ ≤ ‖a‖ * (k * s) * ‖b‖ := by gcongr
      _ = k * (‖a‖ * s * ‖b‖) := by ring
  refine ⟨h1.trans (mul_le_mul_of_nonneg_left (by rw [← e]; exact h) hk), fun h0 => ?_⟩
  rw [h0] at h1
  simp only [mul_zero, zero_mul] at h1
  exact norm_le_zero_iff.1 h1

/- English proof (translation)
Establish `: BorelSpace (H E n 0)` using `⟨rfl⟩`. Establish `hT : D.ν (toMeasurable D.ν S) < ⊤` using `by rw [measure_toMeasurable]; exact hS`. Use `haveI : IsFiniteMeasure (D.ν.restrict (toMeasurable D.ν S)) := ⟨by rw [Measure.restrict_apply_univ]; exact hT⟩`. Establish `hi : Integrable ((toMeasurable D.ν S).indicator fun _ => C) D.ν` using `IntegrableOn.integrable_indicator (integrable_const C) (measurableSet_toMeasurable _ _)`. Use `Integrable.mono' hi hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ toMeasurable D.ν S`. Simplify using `only [Set.indicator, hx, if_true]`. Conclude with `(h x).1`. Establish `hx' : x ∉ S` using `fun h' => hx (subset_toMeasurable _ _ h')`. Simplify using `only [Set.indicator, hx, if_false, (h x).2 hx', norm_zero, le_refl]`.
-/
theorem integrable_of_bd (D : Dom E n 0) {f : H E n 0 → ℂ} (hf : Continuous f) {S : Set (H E n 0)}
    (hS : D.ν S < ⊤) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C ∧ (x ∉ S → f x = 0)) : Integrable f D.ν := by
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have hT : D.ν (toMeasurable D.ν S) < ⊤ := by rw [measure_toMeasurable]; exact hS
  haveI : IsFiniteMeasure (D.ν.restrict (toMeasurable D.ν S)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hT⟩
  have hi : Integrable ((toMeasurable D.ν S).indicator fun _ => C) D.ν :=
    IntegrableOn.integrable_indicator (integrable_const C) (measurableSet_toMeasurable _ _)
  refine Integrable.mono' hi hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ toMeasurable D.ν S
  · simp only [Set.indicator, hx, if_true]; exact (h x).1
  · have hx' : x ∉ S := fun h' => hx (subset_toMeasurable _ _ h')
    simp only [Set.indicator, hx, if_false, (h x).2 hx', norm_zero, le_refl]

/- English proof (translation)
Introduce `E _ _ _ n hn D π hθ φ hφ hO X ψ hψ u hu hsu`. Establish `: BorelSpace (H E n 0)` using `⟨rfl⟩`. Establish `hXψ : act (Op.lie X) ψ ∈ π.V` using `π.stable _ ψ hψ`. Establish `hXφ : IsAutForm (act (Op.lie X) φ)` using `PositivityTheory.Rg.Rs.PrAut.isAutForm_act hF _ hφ`. Establish `hψc : Continuous ψ.1` using `continuous_of_mem π hψ`.

Establish `hXψc : Continuous (act (Op.lie X) ψ).1` using `continuous_of_mem π hXψ`. Establish `hφc : Continuous φ.1` using `ContAut.continuous_of_isOpen_stab E n φ hφ.level`. Establish `hXφc : Continuous (act (Op.lie X) φ).1` using `ContAut.continuous_of_isOpen_stab E n _ hXφ.level`. Take `⟨c, hc⟩` from `ldet_expGL (E := E) (n := n) X`. Establish `hec : Continuous fun t => infGL E n (expGL X t)` using `cont_infGL.comp (cont_expGL X)`.

Use `set e : ℝ → GA E n := fun t => infGL E n (expGL X t) with he`. Establish `he0 : e 0 = 1` using `by simp only [he, expGL_zero, map_one]`. Use `set Ω : Set (GA E n) := e '' Set.Icc (-1) 1 with hΩd`. Establish `hΩ : IsCompact Ω` using `isCompact_Icc.image hec`. Establish `hmem : ∀ t : ℝ, |t| ≤ 1 → e t ∈ Ω` using `fun t ht => ⟨t, abs_le.1 ht, rfl⟩`.

Establish `huc : Continuous u` using `hu.continuous`. Establish `hu'c : Continuous (deriv u)` using `hu.continuous_deriv (by exact_mod_cast le_top)`. Take `⟨w, hwc, hws, hwn, hw⟩` from `exists_major u (deriv u) huc hu'c hsu hsu.deriv c`. Use `set ũ : ℝ → ℂ := fun s => ((w s : ℝ) : ℂ) with hũ`. Establish `hũc : Continuous ũ` using `Complex.continuous_ofReal.comp hwc`.

Establish `hũs : HasCompactSupport ũ` using `hws.comp_left Complex.ofReal_zero`. Take `⟨C0, hC0, hS0⟩` from `hB E n hn D ψ φ ũ Ω (π.cusp ψ hψ) (hθ.1 ψ hψ) hφ hũc hũs hΩ`. Take `⟨C1, hC1, -⟩` from `hB E n hn D _ φ ũ Ω (π.cusp _ hXψ) (hθ.1 _ hXψ) hφ hũc hũs hΩ`. Take `⟨C2, hC2, -⟩` from `hB E n hn D ψ _ ũ Ω (π.cusp ψ hψ) (hθ.1 ψ hψ) hXφ hũc hũs hΩ`. Use `set S : Set (H E n 0) := {x | w (ldet x) ≠ 0} with hSd`.

Establish `hS : D.ν S < ⊤` using `(measure_mono fun x hx => (Complex.ofReal_ne_zero.2 hx : ũ (ldet x) ≠ 0)).trans_lt hS0`. Establish `hv1 : ∀ x : H E n 0, ∀ t : ℝ, |t| ≤ 1 → ‖u (ldet x + t * c)‖ ≤ 1 * w (ldet x)` using `fun x t ht => by`. Rewrite using `[one_mul]`. Conclude with `(hw _ t ht).1`. Establish `hv2 : ∀ x : H E n 0, ∀ t : ℝ, |t| ≤ 1 → ‖deriv u (ldet x + t * c) * c‖ ≤ |c| * w (ldet x)` using `fun x t ht => by`.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left (hw _ t ht).2 (abs_nonneg _)`. Set `F : ℝ → H E n 0 → ℂ` to `fun t x => star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * φ.1 (x.1 * e t)`. Set `F' : ℝ → H E n 0 → ℂ` to `fun t x => star ((act (Op.lie X) ψ).1 (x.1 * e t) * u (ldet x + t * c) + ψ.1 (x.1 * e t) * (deriv u (ldet x + t * c) * c)) * φ.1 (x.1 * e t) + star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * (act (Op.lie X) φ).1 (x.1 * e t)`. Establish `hm : ∀ t, Continuous fun x : H E n 0 => x.1 * e t` using `fun t => continuous_fst.mul continuous_const`.

Establish `hl : ∀ t : ℝ, Continuous fun x : H E n 0 => ldet x + t * c` using `fun t => continuous_ldet.add continuous_const`. Establish `hFc : ∀ t, Continuous (F t)` using `fun t => ((hψc.comp (hm t)).mul (huc.comp (hl t))).star.mul (hφc.comp (hm t))`. Establish `hF'c : Continuous (F' 0)` using `(((hXψc.comp (hm 0)).mul (huc.comp (hl 0))).add ((hψc.comp (hm 0)).mul ((hu'c.comp (hl 0)).mul continuous_const))).star.mul (hφc.comp (hm 0)) |>.add (((hψc.comp (hm 0)).mul (huc.comp (hl 0))).star.mul (hXφc.comp (hm 0)))`. Establish `hPinv : ∀ (γ : ratH E n 0) (y : H E n 0), (fun y : H E n 0 => starRingEnd ℂ (ψ.1 y.1 * u (ldet y)) * φ.1 y.1) ((γ : H E n 0) * y) = (fun y : H E n 0 => starRingEnd ℂ (ψ.1 y.1 * u (ldet y)) * φ.1 y.1) y`. Introduce `γ y`.

Take `⟨γ₁, h1⟩` from `fst_ratH γ`. Establish `e1 : ((γ : H E n 0) * y).1 = ratGL E n γ₁ * y.1` using `by rw [Prod.fst_mul, h1]`. Use `show starRingEnd ℂ (ψ.1 ((γ : H E n 0) * y).1 * u (ldet ((γ : H E n 0) * y))) * φ.1 ((γ : H E n 0) * y).1 = _`. Rewrite using `[e1, ldet_ratH_mul, (π.cusp ψ hψ).1.left, hφ.left]`. Establish `hI : ∀ t, ∫ x, F t x ∂D.ν = prg D ψ u φ` using `fun t => by`.

Establish `key` using `integral_mul_right_fd D ((e t, 1) : H E n 0) (fun y : H E n 0 => starRingEnd ℂ (ψ.1 y.1 * u (ldet y)) * φ.1 y.1) hPinv`. Use `Eq.trans ?_ key` and prove the remaining obligations. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `show star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * φ.1 (x.1 * e t) = starRingEnd ℂ (ψ.1 (x * ((e t, 1) : H E n 0)).1 * u (ldet (x * ((e t, 1) : H E n 0)))) * φ.1 (x * ((e t, 1) : H E n 0)).1`. Rewrite using `[hc x t]`.

Both sides reduce to the same expression. Establish `h1 : HasDerivAt (fun t => ∫ x, F t x ∂D.ν) 0 0`. Establish `e2 : (fun t => ∫ x, F t x ∂D.ν) = fun _ => prg D ψ u φ` using `funext hI`. Rewrite using `[e2]`. Conclude with `hasDerivAt_const _ _`.

Establish `hder : ∀ (x : H E n 0) (t : ℝ), HasDerivAt (fun t => F t x) (F' t x) t`. Introduce `x t`. Establish `d1` using `hasDerivAt_along X ψ x.1 t`. Establish `d2 : HasDerivAt (fun s => u (ldet x + s * c)) (deriv u (ldet x + t * c) * c) t`. Establish `hd : HasDerivAt u (deriv u (ldet x + t * c)) (ldet x + t * c)` using `((hu.differentiable (by simp)) _).hasDerivAt`.

Establish `hl' : HasDerivAt (fun s => ldet x + s * c) c t` using `(hasDerivAt_mul_const c).const_add (ldet x)`. Use `hd.scomp t hl'` as an intermediate fact. Rewrite `this` using `[Complex.real_smul, mul_comm]`. Then use the resulting hypothesis. Establish `d3` using `hasDerivAt_along X φ x.1 t`. Conclude with `((d1.mul d2).star).mul d3`.

Establish `hb : ∀ (x : H E n 0) (t : ℝ), |t| ≤ 1 → ‖F' t x‖ ≤ C1 + |c| * C0 + C2 ∧ (x ∉ S → F' t x = 0)`. Introduce `x t ht`. Establish `q1` using `pt_bd (hwn (ldet x)) zero_le_one (hv1 x t ht) (hC1 x (e t) (hmem t ht) (e t) (hmem t ht))`. Establish `q2` using `pt_bd (hwn (ldet x)) (abs_nonneg c) (hv2 x t ht) (hC0 x (e t) (hmem t ht) (e t) (hmem t ht))`. Establish `q3` using `pt_bd (hwn (ldet x)) zero_le_one (hv1 x t ht) (hC2 x (e t) (hmem t ht) (e t) (hmem t ht))`.

Establish `hs : F' t x = star ((act (Op.lie X) ψ).1 (x.1 * e t) * u (ldet x + t * c)) * φ.1 (x.1 * e t) + star (ψ.1 (x.1 * e t) * (deriv u (ldet x + t * c) * c)) * φ.1 (x.1 * e t) + star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * (act (Op.lie X) φ).1 (x.1 * e t)` using `by show star (_ + _) * _ + _ = _`. Rewrite using `[star_add, add_mul]`. Use `⟨?_, fun hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Use `add_le_add ((norm_add_le _ _).trans (add_le_add ?_ q2.1)) ?_` and prove the remaining obligations. Simplify using `using q1.1`. Simplify using `using q3.1`. Establish `h0 : w (ldet x) = 0` using `by by_contra h'; exact hx h'`. Rewrite using `[hs, q1.2 h0, q2.2 h0, q3.2 h0, add_zero, add_zero]`.

Establish `hbd : ∀ x : H E n 0, ‖F 0 x‖ ≤ C0 ∧ (x ∉ S → F 0 x = 0)`. Introduce `x`. Establish `q` using `pt_bd (hwn (ldet x)) zero_le_one (hv1 x 0 (by simp)) (hC0 x (e 0) (hmem 0 (by simp)) (e 0) (hmem 0 (by simp)))`. Conclude with `⟨le_of_le_of_eq q.1 (one_mul _), fun hx => q.2 (by by_contra h'; exact hx h')⟩`. Establish `hCt : 0 ≤ C1 + |c| * C0 + C2` using `(norm_nonneg _).trans (hb 1 0 (by simp)).1`.

Establish `hT : D.ν (toMeasurable D.ν S) < ⊤` using `by rw [measure_toMeasurable]; exact hS`. Use `haveI : IsFiniteMeasure (D.ν.restrict (toMeasurable D.ν S)) := ⟨by rw [Measure.restrict_apply_univ]; exact hT⟩`. Establish `hbi : Integrable ((toMeasurable D.ν S).indicator fun _ => C1 + |c| * C0 + C2) D.ν` using `IntegrableOn.integrable_indicator (integrable_const _) (measurableSet_toMeasurable _ _)`. Establish `h2` using `(hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := D.ν) (F := F) (F' := F') (x₀ := 0) (bound := (toMeasurable D.ν S).indicator fun _ => C1 + |c| * C0 + C2) (Metric.ball_mem_nhds 0 one_pos) (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable) (integrable_of_bd D (hFc …`. Establish `ht' : |t| ≤ 1`.

Rewrite `ht` using `[Metric.mem_ball, Real.dist_eq, sub_zero]`. Conclude with `ht.le`. Distinguish the cases in `hx : x ∈ toMeasurable D.ν S`. Simplify using `only [Set.indicator, hx, if_true]`. Conclude with `(hb x t ht').1`.

Establish `hx' : x ∉ S` using `fun h' => hx (subset_toMeasurable _ _ h')`. Simplify using `only [Set.indicator, hx, if_false, (hb x t ht').2 hx', norm_zero, le_refl])`. Use `hbi (Eventually.of_forall fun x t _ => hder x t)).2`. Establish `h0 : ∫ x, F' 0 x ∂D.ν = 0` using `h2.unique h1`. Establish `hx0 : ∀ x : H E n 0, x.1 * e 0 = x.1` using `fun x => by rw [he0, mul_one]`.

Set `g₁ : H E n 0 → ℂ` to `fun x => starRingEnd ℂ ((act (Op.lie X) ψ).1 x.1 * u (ldet x)) * φ.1 x.1`. Set `g₂ : H E n 0 → ℂ` to `fun x => starRingEnd ℂ (ψ.1 x.1 * (fun s => deriv u s * c) (ldet x)) * φ.1 x.1`. Set `g₃ : H E n 0 → ℂ` to `fun x => starRingEnd ℂ (ψ.1 x.1 * u (ldet x)) * (act (Op.lie X) φ).1 x.1`. Establish `hsplit : F' 0 = fun x => g₁ x + g₂ x + g₃ x`. Use function extensionality and compare the values at `x`.

Use `show star (_ + _) * _ + _ = _`. Simplify using `only [hx0, zero_mul, add_zero, star_add, add_mul, starRingEnd_apply, g₁, g₂, g₃]`. Establish `hg : ∀ x : H E n 0, ‖g₁ x‖ ≤ C1 ∧ ‖g₂ x‖ ≤ |c| * C0 ∧ ‖g₃ x‖ ≤ C2 ∧ (x ∉ S → g₁ x = 0 ∧ g₂ x = 0 ∧ g₃ x = 0)`. Introduce `x`. Establish `m0 : e 0 ∈ Ω` using `hmem 0 (by simp)`.

Establish `z1` using `hC1 x (e 0) m0 (e 0) m0`. Establish `z0` using `hC0 x (e 0) m0 (e 0) m0`. Establish `z2` using `hC2 x (e 0) m0 (e 0) m0`. Rewrite `z1`, `z0`, `z2` using `[hx0]`. Establish `w1` using `hv1 x 0 (by simp)`.

Establish `w2` using `hv2 x 0 (by simp)`. Simplify using `only [zero_mul, add_zero] at w1 w2`. Establish `q1` using `pt_bd (hwn (ldet x)) zero_le_one w1 z1`. Establish `q2` using `pt_bd (hwn (ldet x)) (abs_nonneg c) w2 z0`. Establish `q3` using `pt_bd (hwn (ldet x)) zero_le_one w1 z2`.

Establish `hw0 : x ∉ S → w (ldet x) = 0` using `fun hx => by by_contra h'; exact hx h'`. Use `⟨by simpa [g₁] using q1.1, by simpa [g₂] using q2.1, by simpa [g₃] using q3.1, fun hx => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Simplify `q1.2 (hw0 hx)` using `[g₁]`. Simplify `q2.2 (hw0 hx)` using `[g₂]`. Simplify `q3.2 (hw0 hx)` using `[g₃]`.

Establish `hm0 : Continuous fun x : H E n 0 => x.1` using `continuous_fst`. Establish `hl0 : Continuous fun x : H E n 0 => ldet x` using `continuous_ldet`. Establish `i1 : Integrable g₁ D.ν` using `integrable_of_bd D (((hXψc.comp hm0).mul (huc.comp hl0)).star.mul (hφc.comp hm0)) hS fun x => ⟨(hg x).1, fun hx => ((hg x).2.2.2 hx).1⟩`. Establish `i2 : Integrable g₂ D.ν` using `integrable_of_bd D (((hψc.comp hm0).mul ((hu'c.comp hl0).mul continuous_const)).star.mul (hφc.comp hm0)) hS fun x => ⟨(hg x).2.1, fun hx => ((hg x).2.2.2 hx).2.1⟩`. Establish `i3 : Integrable g₃ D.ν` using `integrable_of_bd D (((hψc.comp hm0).mul (huc.comp hl0)).star.mul (hXφc.comp hm0)) hS fun x => ⟨(hg x).2.2.1, fun hx => ((hg x).2.2.2 hx).2.2⟩`.

Establish `o1 : ∫ x, g₁ x ∂D.ν = 0` using `hO _ hXψ u hu hsu`. Establish `o2 : ∫ x, g₂ x ∂D.ν = 0` using `hO ψ hψ (fun s => deriv u s * c) ((hu.iterate_deriv 1).mul contDiff_const) (hsu.deriv.mul_right)`. Establish `a1 : ∫ x, (g₁ x + g₂ x + g₃ x) ∂D.ν = ∫ x, (g₁ x + g₂ x) ∂D.ν + ∫ x, g₃ x ∂D.ν` using `integral_add (i1.add i2) i3`. Establish `a2 : ∫ x, (g₁ x + g₂ x) ∂D.ν = ∫ x, g₁ x ∂D.ν + ∫ x, g₂ x ∂D.ν` using `integral_add i1 i2`. Rewrite `h0` using `[hsplit]`.

Establish `h0' : ∫ x, (g₁ x + g₂ x + g₃ x) ∂D.ν = 0` using `h0`. Rewrite `h0'` using `[a1, a2, o1, o2, zero_add, zero_add]`. Conclude with `h0'`.
-/
theorem orthLie_of (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hB : PairBd) : OrthLie := by
  intro E _ _ _ n hn D π hθ φ hφ hO X ψ hψ u hu hsu
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have hXψ : act (Op.lie X) ψ ∈ π.V := π.stable _ ψ hψ
  have hXφ : IsAutForm (act (Op.lie X) φ) := PositivityTheory.Rg.Rs.PrAut.isAutForm_act hF _ hφ
  have hψc : Continuous ψ.1 := continuous_of_mem π hψ
  have hXψc : Continuous (act (Op.lie X) ψ).1 := continuous_of_mem π hXψ
  have hφc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E n φ hφ.level
  have hXφc : Continuous (act (Op.lie X) φ).1 := ContAut.continuous_of_isOpen_stab E n _ hXφ.level
  obtain ⟨c, hc⟩ := ldet_expGL (E := E) (n := n) X
  have hec : Continuous fun t => infGL E n (expGL X t) := cont_infGL.comp (cont_expGL X)
  set e : ℝ → GA E n := fun t => infGL E n (expGL X t) with he
  have he0 : e 0 = 1 := by simp only [he, expGL_zero, map_one]
  set Ω : Set (GA E n) := e '' Set.Icc (-1) 1 with hΩd
  have hΩ : IsCompact Ω := isCompact_Icc.image hec
  have hmem : ∀ t : ℝ, |t| ≤ 1 → e t ∈ Ω := fun t ht => ⟨t, abs_le.1 ht, rfl⟩
  have huc : Continuous u := hu.continuous
  have hu'c : Continuous (deriv u) := hu.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨w, hwc, hws, hwn, hw⟩ := exists_major u (deriv u) huc hu'c hsu hsu.deriv c
  set ũ : ℝ → ℂ := fun s => ((w s : ℝ) : ℂ) with hũ
  have hũc : Continuous ũ := Complex.continuous_ofReal.comp hwc
  have hũs : HasCompactSupport ũ := hws.comp_left Complex.ofReal_zero
  obtain ⟨C0, hC0, hS0⟩ := hB E n hn D ψ φ ũ Ω (π.cusp ψ hψ) (hθ.1 ψ hψ) hφ hũc hũs hΩ
  obtain ⟨C1, hC1, -⟩ := hB E n hn D _ φ ũ Ω (π.cusp _ hXψ) (hθ.1 _ hXψ) hφ hũc hũs hΩ
  obtain ⟨C2, hC2, -⟩ := hB E n hn D ψ _ ũ Ω (π.cusp ψ hψ) (hθ.1 ψ hψ) hXφ hũc hũs hΩ
  set S : Set (H E n 0) := {x | w (ldet x) ≠ 0} with hSd
  have hS : D.ν S < ⊤ := (measure_mono fun x hx => (Complex.ofReal_ne_zero.2 hx : ũ (ldet x) ≠ 0)).trans_lt hS0

  have hv1 : ∀ x : H E n 0, ∀ t : ℝ, |t| ≤ 1 → ‖u (ldet x + t * c)‖ ≤ 1 * w (ldet x) := fun x t ht => by
    rw [one_mul]; exact (hw _ t ht).1
  have hv2 : ∀ x : H E n 0, ∀ t : ℝ, |t| ≤ 1 → ‖deriv u (ldet x + t * c) * c‖ ≤ |c| * w (ldet x) :=
    fun x t ht => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_left (hw _ t ht).2 (abs_nonneg _)
  let F : ℝ → H E n 0 → ℂ := fun t x => star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * φ.1 (x.1 * e t)
  let F' : ℝ → H E n 0 → ℂ := fun t x =>
    star ((act (Op.lie X) ψ).1 (x.1 * e t) * u (ldet x + t * c) + ψ.1 (x.1 * e t) * (deriv u (ldet x + t * c) * c)) *
        φ.1 (x.1 * e t) +
      star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * (act (Op.lie X) φ).1 (x.1 * e t)
  have hm : ∀ t, Continuous fun x : H E n 0 => x.1 * e t := fun t => continuous_fst.mul continuous_const
  have hl : ∀ t : ℝ, Continuous fun x : H E n 0 => ldet x + t * c := fun t => continuous_ldet.add continuous_const
  have hFc : ∀ t, Continuous (F t) := fun t =>
    ((hψc.comp (hm t)).mul (huc.comp (hl t))).star.mul (hφc.comp (hm t))
  have hF'c : Continuous (F' 0) :=
    (((hXψc.comp (hm 0)).mul (huc.comp (hl 0))).add ((hψc.comp (hm 0)).mul ((hu'c.comp (hl 0)).mul
      continuous_const))).star.mul (hφc.comp (hm 0)) |>.add (((hψc.comp (hm 0)).mul (huc.comp (hl 0))).star.mul
        (hXφc.comp (hm 0)))

  have hPinv : ∀ (γ : ratH E n 0) (y : H E n 0), (fun y : H E n 0 => starRingEnd ℂ (ψ.1 y.1 * u (ldet y)) * φ.1 y.1)
      ((γ : H E n 0) * y) = (fun y : H E n 0 => starRingEnd ℂ (ψ.1 y.1 * u (ldet y)) * φ.1 y.1) y := by
    intro γ y
    obtain ⟨γ₁, h1⟩ := fst_ratH γ
    have e1 : ((γ : H E n 0) * y).1 = ratGL E n γ₁ * y.1 := by rw [Prod.fst_mul, h1]
    show starRingEnd ℂ (ψ.1 ((γ : H E n 0) * y).1 * u (ldet ((γ : H E n 0) * y))) * φ.1 ((γ : H E n 0) * y).1 = _
    rw [e1, ldet_ratH_mul, (π.cusp ψ hψ).1.left, hφ.left]
  have hI : ∀ t, ∫ x, F t x ∂D.ν = prg D ψ u φ := fun t => by
    have key := integral_mul_right_fd D ((e t, 1) : H E n 0)
      (fun y : H E n 0 => starRingEnd ℂ (ψ.1 y.1 * u (ldet y)) * φ.1 y.1) hPinv
    refine Eq.trans ?_ key
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * φ.1 (x.1 * e t) =
      starRingEnd ℂ (ψ.1 (x * ((e t, 1) : H E n 0)).1 * u (ldet (x * ((e t, 1) : H E n 0)))) *
        φ.1 (x * ((e t, 1) : H E n 0)).1
    rw [hc x t]
    rfl
  have h1 : HasDerivAt (fun t => ∫ x, F t x ∂D.ν) 0 0 := by
    have e2 : (fun t => ∫ x, F t x ∂D.ν) = fun _ => prg D ψ u φ := funext hI
    rw [e2]
    exact hasDerivAt_const _ _

  have hder : ∀ (x : H E n 0) (t : ℝ), HasDerivAt (fun t => F t x) (F' t x) t := by
    intro x t
    have d1 := hasDerivAt_along X ψ x.1 t
    have d2 : HasDerivAt (fun s => u (ldet x + s * c)) (deriv u (ldet x + t * c) * c) t := by
      have hd : HasDerivAt u (deriv u (ldet x + t * c)) (ldet x + t * c) :=
        ((hu.differentiable (by simp)) _).hasDerivAt
      have hl' : HasDerivAt (fun s => ldet x + s * c) c t := (hasDerivAt_mul_const c).const_add (ldet x)
      have := hd.scomp t hl'
      rwa [Complex.real_smul, mul_comm] at this
    have d3 := hasDerivAt_along X φ x.1 t
    exact ((d1.mul d2).star).mul d3

  have hb : ∀ (x : H E n 0) (t : ℝ), |t| ≤ 1 →
      ‖F' t x‖ ≤ C1 + |c| * C0 + C2 ∧ (x ∉ S → F' t x = 0) := by
    intro x t ht
    have q1 := pt_bd (hwn (ldet x)) zero_le_one (hv1 x t ht) (hC1 x (e t) (hmem t ht) (e t) (hmem t ht))
    have q2 := pt_bd (hwn (ldet x)) (abs_nonneg c) (hv2 x t ht) (hC0 x (e t) (hmem t ht) (e t) (hmem t ht))
    have q3 := pt_bd (hwn (ldet x)) zero_le_one (hv1 x t ht) (hC2 x (e t) (hmem t ht) (e t) (hmem t ht))
    have hs : F' t x = star ((act (Op.lie X) ψ).1 (x.1 * e t) * u (ldet x + t * c)) * φ.1 (x.1 * e t) +
        star (ψ.1 (x.1 * e t) * (deriv u (ldet x + t * c) * c)) * φ.1 (x.1 * e t) +
        star (ψ.1 (x.1 * e t) * u (ldet x + t * c)) * (act (Op.lie X) φ).1 (x.1 * e t) := by
      show star (_ + _) * _ + _ = _
      rw [star_add, add_mul]
    refine ⟨?_, fun hx => ?_⟩
    · rw [hs]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ q2.1)) ?_
      · simpa using q1.1
      · simpa using q3.1
    · have h0 : w (ldet x) = 0 := by by_contra h'; exact hx h'
      rw [hs, q1.2 h0, q2.2 h0, q3.2 h0, add_zero, add_zero]
  have hbd : ∀ x : H E n 0, ‖F 0 x‖ ≤ C0 ∧ (x ∉ S → F 0 x = 0) := by
    intro x
    have q := pt_bd (hwn (ldet x)) zero_le_one (hv1 x 0 (by simp)) (hC0 x (e 0) (hmem 0 (by simp)) (e 0) (hmem 0 (by simp)))
    exact ⟨le_of_le_of_eq q.1 (one_mul _), fun hx => q.2 (by by_contra h'; exact hx h')⟩
  have hCt : 0 ≤ C1 + |c| * C0 + C2 := (norm_nonneg _).trans (hb 1 0 (by simp)).1
  have hT : D.ν (toMeasurable D.ν S) < ⊤ := by rw [measure_toMeasurable]; exact hS
  haveI : IsFiniteMeasure (D.ν.restrict (toMeasurable D.ν S)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hT⟩
  have hbi : Integrable ((toMeasurable D.ν S).indicator fun _ => C1 + |c| * C0 + C2) D.ν :=
    IntegrableOn.integrable_indicator (integrable_const _) (measurableSet_toMeasurable _ _)
  have h2 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := D.ν) (F := F) (F' := F') (x₀ := 0)
    (bound := (toMeasurable D.ν S).indicator fun _ => C1 + |c| * C0 + C2) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    (integrable_of_bd D (hFc 0) hS hbd) hF'c.aestronglyMeasurable
    (Eventually.of_forall fun x t ht => by
      have ht' : |t| ≤ 1 := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; exact ht.le
      by_cases hx : x ∈ toMeasurable D.ν S
      · simp only [Set.indicator, hx, if_true]; exact (hb x t ht').1
      · have hx' : x ∉ S := fun h' => hx (subset_toMeasurable _ _ h')
        simp only [Set.indicator, hx, if_false, (hb x t ht').2 hx', norm_zero, le_refl])
    hbi (Eventually.of_forall fun x t _ => hder x t)).2
  have h0 : ∫ x, F' 0 x ∂D.ν = 0 := h2.unique h1

  have hx0 : ∀ x : H E n 0, x.1 * e 0 = x.1 := fun x => by rw [he0, mul_one]
  let g₁ : H E n 0 → ℂ := fun x => starRingEnd ℂ ((act (Op.lie X) ψ).1 x.1 * u (ldet x)) * φ.1 x.1
  let g₂ : H E n 0 → ℂ := fun x => starRingEnd ℂ (ψ.1 x.1 * (fun s => deriv u s * c) (ldet x)) * φ.1 x.1
  let g₃ : H E n 0 → ℂ := fun x => starRingEnd ℂ (ψ.1 x.1 * u (ldet x)) * (act (Op.lie X) φ).1 x.1
  have hsplit : F' 0 = fun x => g₁ x + g₂ x + g₃ x := by
    funext x
    show star (_ + _) * _ + _ = _
    simp only [hx0, zero_mul, add_zero, star_add, add_mul, starRingEnd_apply, g₁, g₂, g₃]
  have hg : ∀ x : H E n 0, ‖g₁ x‖ ≤ C1 ∧ ‖g₂ x‖ ≤ |c| * C0 ∧ ‖g₃ x‖ ≤ C2 ∧
      (x ∉ S → g₁ x = 0 ∧ g₂ x = 0 ∧ g₃ x = 0) := by
    intro x
    have m0 : e 0 ∈ Ω := hmem 0 (by simp)
    have z1 := hC1 x (e 0) m0 (e 0) m0
    have z0 := hC0 x (e 0) m0 (e 0) m0
    have z2 := hC2 x (e 0) m0 (e 0) m0
    rw [hx0] at z1 z0 z2
    have w1 := hv1 x 0 (by simp)
    have w2 := hv2 x 0 (by simp)
    simp only [zero_mul, add_zero] at w1 w2
    have q1 := pt_bd (hwn (ldet x)) zero_le_one w1 z1
    have q2 := pt_bd (hwn (ldet x)) (abs_nonneg c) w2 z0
    have q3 := pt_bd (hwn (ldet x)) zero_le_one w1 z2
    have hw0 : x ∉ S → w (ldet x) = 0 := fun hx => by by_contra h'; exact hx h'
    refine ⟨by simpa [g₁] using q1.1, by simpa [g₂] using q2.1, by simpa [g₃] using q3.1, fun hx => ⟨?_, ?_, ?_⟩⟩
    · simpa [g₁] using q1.2 (hw0 hx)
    · simpa [g₂] using q2.2 (hw0 hx)
    · simpa [g₃] using q3.2 (hw0 hx)
  have hm0 : Continuous fun x : H E n 0 => x.1 := continuous_fst
  have hl0 : Continuous fun x : H E n 0 => ldet x := continuous_ldet
  have i1 : Integrable g₁ D.ν := integrable_of_bd D
    (((hXψc.comp hm0).mul (huc.comp hl0)).star.mul (hφc.comp hm0)) hS fun x => ⟨(hg x).1, fun hx => ((hg x).2.2.2 hx).1⟩
  have i2 : Integrable g₂ D.ν := integrable_of_bd D
    (((hψc.comp hm0).mul ((hu'c.comp hl0).mul continuous_const)).star.mul (hφc.comp hm0)) hS
    fun x => ⟨(hg x).2.1, fun hx => ((hg x).2.2.2 hx).2.1⟩
  have i3 : Integrable g₃ D.ν := integrable_of_bd D
    (((hψc.comp hm0).mul (huc.comp hl0)).star.mul (hXφc.comp hm0)) hS
    fun x => ⟨(hg x).2.2.1, fun hx => ((hg x).2.2.2 hx).2.2⟩
  have o1 : ∫ x, g₁ x ∂D.ν = 0 := hO _ hXψ u hu hsu
  have o2 : ∫ x, g₂ x ∂D.ν = 0 := hO ψ hψ (fun s => deriv u s * c)
    ((hu.iterate_deriv 1).mul contDiff_const) (hsu.deriv.mul_right)
  have a1 : ∫ x, (g₁ x + g₂ x + g₃ x) ∂D.ν = ∫ x, (g₁ x + g₂ x) ∂D.ν + ∫ x, g₃ x ∂D.ν := integral_add (i1.add i2) i3
  have a2 : ∫ x, (g₁ x + g₂ x) ∂D.ν = ∫ x, g₁ x ∂D.ν + ∫ x, g₂ x ∂D.ν := integral_add i1 i2
  rw [hsplit] at h0
  have h0' : ∫ x, (g₁ x + g₂ x + g₃ x) ∂D.ν = 0 := h0
  rw [a1, a2, o1, o2, zero_add, zero_add] at h0'
  exact h0'

/- English proof (translation)
The claim follows from `rOrthAct (orthLie_of hF hB)`.
-/
theorem orthAct_of (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hB : PairBd) : OrthAct :=
  rOrthAct (orthLie_of hF hB)

end DiscreteGroups.T1.G

end
