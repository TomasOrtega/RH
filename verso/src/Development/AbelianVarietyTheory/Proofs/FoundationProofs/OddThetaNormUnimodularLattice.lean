import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AreaBoundedOfDiscrEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators UpperHalfPlane Real Pointwise
open MeasureTheory

noncomputable section

namespace GlobalTheory.OddThetaNorm

/- English proof (translation)
Rewrite using `[setAverage_eq, setAverage_eq, Measure.real, Measure.real, hs.measure_eq ht, hs.setIntegral_eq ht fun g x => by`. Rewrite using `[AddSubgroup.vadd_def, vadd_eq_add, add_comm, hf _ g.2]]`.
-/
theorem setAverage_eq_of_fundamental {Λ : AddSubgroup ℂ} [Countable Λ] {s t : Set ℂ}
    (hs : IsAddFundamentalDomain Λ s volume) (ht : IsAddFundamentalDomain Λ t volume)
    {f : ℂ → ℝ} (hf : ∀ ω ∈ Λ, ∀ z, f (z + ω) = f z) : ⨍ z in s, f z = ⨍ z in t, f z := by
  rw [setAverage_eq, setAverage_eq, Measure.real, Measure.real, hs.measure_eq ht,
    hs.setIntegral_eq ht fun g x => by
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hf _ g.2]]

/- English proof (translation)
Rewrite using `[setAverage_eq_of_fundamental hs (hs.vadd_of_comm t) hf, setAverage_eq, setAverage_eq, Measure.real, Measure.real, measure_vadd]`. Use `congr 1`. Use `(measurePreserving_add_left volume t).setIntegral_image_emb (measurableEmbedding_addLeft t) f s` as an intermediate fact. Simplify using `only [add_comm _ t]`. Conclude with `this.symm`.
-/
theorem setAverage_add {Λ : AddSubgroup ℂ} [Countable Λ] {s : Set ℂ}
    (hs : IsAddFundamentalDomain Λ s volume)
    {f : ℂ → ℝ} (hf : ∀ ω ∈ Λ, ∀ z, f (z + ω) = f z) (t : ℂ) :
    ⨍ z in s, f (z + t) = ⨍ z in s, f z := by
  rw [setAverage_eq_of_fundamental hs (hs.vadd_of_comm t) hf, setAverage_eq, setAverage_eq,
    Measure.real, Measure.real, measure_vadd]
  congr 1
  have := (measurePreserving_add_left volume t).setIntegral_image_emb
    (measurableEmbedding_addLeft t) f s
  simp only [add_comm _ t]
  exact this.symm

/- English proof (translation)
Set `e : (ι → ℝ) ≃L[ℝ] ℂ` to `b.equivFun.symm.toContinuousLinearEquiv`. Establish `he : ∀ p, e p = ∑ i, p i • b i` using `fun p => b.equivFun_symm_apply p`. Establish `hme : MeasurableEmbedding e` using `e.toHomeomorph.measurableEmbedding`. Establish `hpre : e ⁻¹' ZSpan.fundamentalDomain b = Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1)`. Use extensionality with `p`.

Establish `: ∀ i, b.repr (e p) i = p i` using `fun i => congrFun (b.equivFun.apply_symm_apply p) i`. Simplify using `[ZSpan.mem_fundamentalDomain, this]`. Use `set μ : Measure ℂ := Measure.map e volume with hμ`. Establish `hv` using `Measure.isAddLeftInvariant_eq_smul (volume : Measure ℂ) μ`. Establish `hc` using `(Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure ℂ) μ).ne'`.

Use `set c := Measure.addHaarScalarFactor (volume : Measure ℂ) μ`. Establish `h1 : μ (ZSpan.fundamentalDomain b) = 1`. Rewrite using `[hμ, hme.map_apply, hpre, volume_pi_pi]`. Simplify using the standard rewrite rules. Rewrite using `[setAverage_eq, hv, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.real, Measure.smul_apply, h1, hμ, hme.setIntegral_map, hpre]`.

Simplify using `only [he]`. Establish `: (c : ℝ) ≠ 0` using `by exact_mod_cast hc`. Simplify using `[NNReal.smul_def, this]`.
-/
theorem setAverage_fundamentalDomain {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ ℂ) (f : ℂ → ℝ) :
    ⨍ z in ZSpan.fundamentalDomain b, f z =
      ∫ p in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1), f (∑ i, p i • b i) := by
  let e : (ι → ℝ) ≃L[ℝ] ℂ := b.equivFun.symm.toContinuousLinearEquiv
  have he : ∀ p, e p = ∑ i, p i • b i := fun p => b.equivFun_symm_apply p
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpre : e ⁻¹' ZSpan.fundamentalDomain b = Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1) := by
    ext p
    have : ∀ i, b.repr (e p) i = p i := fun i => congrFun (b.equivFun.apply_symm_apply p) i
    simp [ZSpan.mem_fundamentalDomain, this]
  set μ : Measure ℂ := Measure.map e volume with hμ
  have hv := Measure.isAddLeftInvariant_eq_smul (volume : Measure ℂ) μ
  have hc := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure ℂ) μ).ne'
  set c := Measure.addHaarScalarFactor (volume : Measure ℂ) μ
  have h1 : μ (ZSpan.fundamentalDomain b) = 1 := by
    rw [hμ, hme.map_apply, hpre, volume_pi_pi]
    simp
  rw [setAverage_eq, hv, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.real,
    Measure.smul_apply, h1, hμ, hme.setIntegral_map, hpre]
  simp only [he]
  have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  simp [NNReal.smul_def, this]

/- English proof (translation)
Rewrite using `[jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ), ← tsum_mul_left]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]`. Use `Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.coe_addRight]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacobiTheta₂_add_lattice (z τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ (z + (m * τ + k)) τ =
      Complex.exp (-π * Complex.I * (m ^ 2 * τ + 2 * m * z)) * jacobiTheta₂ z τ := by
  rw [jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩
  simp only [Equiv.coe_addRight]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[U1, norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]`. Use `congr 2`. Rewrite using `[show (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) by push_cast; rfl, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re]`. Simplify using `[Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslation_weighted_normSq_mul (Λ : AddSubgroup ℂ) (t : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    ‖U1 Λ t g z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ) =
      ‖g (z + t)‖ ^ 2 * Real.exp (-π * ‖z + t‖ ^ 2 / area Λ) := by
  rw [U1, norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  rw [show (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) by push_cast; rfl, Complex.sub_re,
    Complex.div_ofReal_re, Complex.div_ofReal_re]
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

def oddTheta (τ u : ℂ) : ℂ :=
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (g := 1) !![τ] ![1 / 2] ![1 / 2] ![u]

/- English proof (translation)
Establish `: oddTheta τ = fun z => Complex.exp (π * Complex.I * (τ / 4 + z + 1 / 2)) * jacobiTheta₂ (z + (τ + 1) / 2) τ` using `funext fun z => JacobiDeriv.thetaChar_half_half τ z`. Rewrite using `[this]`. Use `Differentiable.mul (by fun_prop) fun z => ?_` and prove the remaining obligations. Conclude with `((hasDerivAt_jacobiTheta₂_fst (z + (τ + 1) / 2) τ.im_pos).comp_add_const z _).differentiableAt`.
-/
theorem differentiable_oddTheta (τ : ℍ) : Differentiable ℂ (oddTheta τ) := by
  have : oddTheta τ = fun z => Complex.exp (π * Complex.I * (τ / 4 + z + 1 / 2)) *
      jacobiTheta₂ (z + (τ + 1) / 2) τ := funext fun z => JacobiDeriv.thetaChar_half_half τ z
  rw [this]
  refine Differentiable.mul (by fun_prop) fun z => ?_
  exact ((hasDerivAt_jacobiTheta₂_fst (z + (τ + 1) / 2) τ.im_pos).comp_add_const z _).differentiableAt

/- English proof (translation)
Rewrite using `[oddTheta, JacobiDeriv.thetaChar_half_half, zero_add, JacobiDeriv.jacobiTheta₂_half_period, mul_zero]`.
-/
theorem oddTheta_zero (τ : ℂ) : oddTheta τ 0 = 0 := by
  rw [oddTheta, JacobiDeriv.thetaChar_half_half, zero_add, JacobiDeriv.jacobiTheta₂_half_period,
    mul_zero]

/- English proof (translation)
Rewrite using `[oddTheta, oddTheta, JacobiDeriv.thetaChar_half_half, JacobiDeriv.thetaChar_half_half, add_right_comm u, jacobiTheta₂_add_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem oddTheta_add_lattice (u τ : ℂ) (m k : ℤ) :
    oddTheta τ (u + (m * τ + k)) =
      Complex.exp (π * Complex.I * (k - m - m ^ 2 * τ - 2 * m * u)) * oddTheta τ u := by
  rw [oddTheta, oddTheta, JacobiDeriv.thetaChar_half_half, JacobiDeriv.thetaChar_half_half,
    add_right_comm u, jacobiTheta₂_add_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  ring

def canTheta (a : ℂ) (τ : ℍ) (z : ℂ) : ℂ :=
  Complex.exp (π * (z / a) ^ 2 / (2 * τ.im)) * oddTheta τ (z / a)

/- English proof (translation)
Use `differentiable_oddTheta τ` as an intermediate fact. Unfold `canTheta`. Use `fun_prop`.
-/
theorem differentiable_canTheta (a : ℂ) (τ : ℍ) : Differentiable ℂ (canTheta a τ) := by
  have := differentiable_oddTheta τ
  unfold canTheta
  fun_prop

/- English proof (translation)
Establish `h1 : HasDerivAt (fun z => oddTheta τ (z / a)) (deriv (oddTheta τ) 0 / a) 0`. Use `(differentiable_oddTheta τ (0 / a)).hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).div_const a)` as an intermediate fact. Rewrite `this` using `[zero_div, mul_one_div]`. Conclude with `this`. Establish `h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (π * (z / a) ^ 2 / (2 * τ.im))) 0` using `by fun_prop`.

Establish `h3` using `(h2.hasDerivAt.mul h1).deriv`. Simplify using `only [zero_div, oddTheta_zero, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.exp_zero, one_mul] at h3`. Conclude with `h3`.
-/
theorem deriv_canTheta (a : ℂ) (τ : ℍ) : deriv (canTheta a τ) 0 = deriv (oddTheta τ) 0 / a := by
  have h1 : HasDerivAt (fun z => oddTheta τ (z / a)) (deriv (oddTheta τ) 0 / a) 0 := by
    have := (differentiable_oddTheta τ (0 / a)).hasDerivAt.comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).div_const a)
    rw [zero_div, mul_one_div] at this
    exact this
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (π * (z / a) ^ 2 / (2 * τ.im))) 0 := by
    fun_prop
  have h3 := (h2.hasDerivAt.mul h1).deriv
  simp only [zero_div, oddTheta_zero, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Complex.exp_zero, one_mul] at h3
  exact h3

/- English proof (translation)
Rewrite using `[mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]`. Use `split_ifs with h`. Conclude with `h.neg_one_zpow`. Conclude with `(Int.not_even_iff_odd.1 h).neg_one_zpow`.
-/
theorem exp_pi_I_int (j : ℤ) : Complex.exp (π * Complex.I * j) = if Even j then 1 else -1 := by
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h).neg_one_zpow

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

/- English proof (translation)
Establish `: Even (k - m + m * k) ↔ Even m ∧ Even k`. Simplify using `only [parity_simps]`. The claim follows by propositional logic. Rewrite using `[this, h]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, q, e⟩`. Establish `e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ)`. Use `mul_left_cancel₀ ha ?_` and prove the remaining obligations. Use `push_cast`. Take the linear combination `-2 * e`.

Establish `h1` using `congrArg Complex.im e1`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1`. Rewrite `e1` using `[h1, add_right_inj, Int.cast_inj]`. Conclude with `⟨⟨p, h1⟩, ⟨q, e1⟩⟩`. Introduce and unpack `⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩`.

Conclude with `⟨p, q, by push_cast; ring⟩`.
-/
theorem half_mem_iff (m k : ℤ) : a * (m * (τ : ℂ) + k) / 2 ∈ Λ ↔ Even (k - m + m * k) := by
  have : Even (k - m + m * k) ↔ Even m ∧ Even k := by
    simp only [parity_simps]; tauto
  rw [this, h]
  constructor
  · rintro ⟨p, q, e⟩
    have e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ) := by
      refine mul_left_cancel₀ ha ?_
      push_cast
      linear_combination -2 * e
    have h1 := congrArg Complex.im e1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1
    rw [h1, add_right_inj, Int.cast_inj] at e1
    exact ⟨⟨p, h1⟩, ⟨q, e1⟩⟩
  · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
    exact ⟨p, q, by push_cast; ring⟩

/- English proof (translation)
Introduce `ω hω z`. Take `⟨m, k, rfl⟩` from `(h ω).1 hω`. Simplify using `only [half_mem_iff ha h]`. Rewrite using `[← exp_pi_I_int, U1, canTheta, canTheta, LatticeAreaBound.area_eq ha h, show (z + a * (m * (τ : ℂ) + k)) / a = z / a + (m * (τ : ℂ) + k) by field_simp, oddTheta_add_lattice, ← mul_assoc (Complex.exp _), mul_right_comm, ← Complex.exp_add, ← Complex.exp_add, ← mul_assoc (Complex.ex …`. Use `congr 2`.

Establish `hy : ((τ.im : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast τ.im_ne_zero`. Establish `hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Expand and normalize the polynomial expressions, which then agree. Establish `ha' : (starRingEnd ℂ) a ≠ 0` using `by simpa using ha`.

Establish `hn : ((‖a‖ ^ 2 * τ.im : ℝ) : ℂ) = a * (starRingEnd ℂ) a * τ.im`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hn]`.

Simplify using `only [map_mul, map_add, map_intCast, hc]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslation_canonicalOddTheta_lattice : ∀ ω ∈ Λ, ∀ z,
    U1 Λ ω (canTheta a τ) z = (if ω / 2 ∈ Λ then 1 else -1) * canTheta a τ z := by
  intro ω hω z
  obtain ⟨m, k, rfl⟩ := (h ω).1 hω
  simp only [half_mem_iff ha h]
  rw [← exp_pi_I_int, U1, canTheta, canTheta, LatticeAreaBound.area_eq ha h,
    show (z + a * (m * (τ : ℂ) + k)) / a = z / a + (m * (τ : ℂ) + k) by field_simp,
    oddTheta_add_lattice, ← mul_assoc (Complex.exp _), mul_right_comm, ← Complex.exp_add,
    ← Complex.exp_add, ← mul_assoc (Complex.exp _), ← Complex.exp_add]
  congr 2
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  have hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * Complex.I := by
    apply Complex.ext <;> simp
    ring
  have ha' : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  have hn : ((‖a‖ ^ 2 * τ.im : ℝ) : ℂ) = a * (starRingEnd ℂ) a * τ.im := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [hn]
  simp only [map_mul, map_add, map_intCast, hc]
  push_cast
  field_simp
  ring

/- English proof (translation)
Use `Function.Surjective.countable (f := fun p : ℤ × ℤ => (⟨a * (p.1 * (τ : ℂ) + p.2), (h _).2 ⟨_, _, rfl⟩⟩ : Λ)) ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`. Take `⟨m, n, rfl⟩` from `(h x).1 hx`. Conclude with `⟨(m, n), rfl⟩`.
-/
theorem countable_lattice : Countable Λ := by
  refine Function.Surjective.countable
    (f := fun p : ℤ × ℤ => (⟨a * (p.1 * (τ : ℂ) + p.2), (h _).2 ⟨_, _, rfl⟩⟩ : Λ)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨m, n, rfl⟩ := (h x).1 hx
  exact ⟨(m, n), rfl⟩

/- English proof (translation)
Establish `hli : LinearIndependent ℝ (Sum.elim (fun _ => a) (fun _ => a * τ) : Fin 1 ⊕ Fin 1 → ℂ)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Simplify using `only [Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr, Complex.real_smul] at hg`. Establish `e : (g (.inl 0) : ℂ) + g (.inr 0) * τ = 0` using `mul_left_cancel₀ ha (by linear_combination hg)`.

Establish `h1` using `congrArg Complex.im e`. Simplify using `[τ.im_ne_zero] at h1`. Simplify using `[h1] at e`. Apply the tactic sequence `rintro (i | i) <;> rwa [Subsingleton.elim i 0]`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp)`.

Establish `hb : ⇑b = Sum.elim (fun _ => a) (fun _ => a * τ)` using `coe_basisOfLinearIndependentOfCardEqFinrank _ _`. Use `⟨b, fun i => by simp [hb], fun i => by simp [hb], ?_⟩` and prove the remaining obligations. Establish `: Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup`. Use extensionality with `x`. Rewrite using `[h, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun, hb]`.

Simplify using `only [Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr, zsmul_eq_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨Sum.elim (fun _ => n) (fun _ => m), by simp; ring⟩`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `⟨c (.inr 0), c (.inl 0), by ring⟩`. Rewrite using `[this]`. Conclude with `ZSpan.isAddFundamentalDomain' b volume`.
-/
theorem exists_basis : ∃ b : Module.Basis (Fin 1 ⊕ Fin 1) ℝ ℂ,
    (∀ i, b (.inl i) = a) ∧ (∀ i, b (.inr i) = a * τ) ∧
      IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain b) volume := by
  have hli : LinearIndependent ℝ (Sum.elim (fun _ => a) (fun _ => a * τ) : Fin 1 ⊕ Fin 1 → ℂ) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr,
      Complex.real_smul] at hg
    have e : (g (.inl 0) : ℂ) + g (.inr 0) * τ = 0 :=
      mul_left_cancel₀ ha (by linear_combination hg)
    have h1 := congrArg Complex.im e
    simp [τ.im_ne_zero] at h1
    simp [h1] at e
    rintro (i | i) <;> rwa [Subsingleton.elim i 0]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = Sum.elim (fun _ => a) (fun _ => a * τ) :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  refine ⟨b, fun i => by simp [hb], fun i => by simp [hb], ?_⟩
  have : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    ext x
    rw [h, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun, hb]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr, zsmul_eq_mul]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨Sum.elim (fun _ => n) (fun _ => m), by simp; ring⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c (.inr 0), c (.inl 0), by ring⟩
  rw [this]
  exact ZSpan.isAddFundamentalDomain' b volume

/- English proof (translation)
Take `⟨b, -, -, hb⟩` from `exists_basis ha h`. Conclude with `Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨_, hb⟩`.
-/
theorem epsilon_fundamental : IsAddFundamentalDomain Λ
    (Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) volume := by
  obtain ⟨b, -, -, hb⟩ := exists_basis ha h
  exact Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨_, hb⟩

omit ha h in
/- English proof (translation)
Introduce `ω hω z`. Rewrite using `[← thetaTranslation_weighted_normSq_mul, hg ω hω, norm_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem weight_invariant {g : ℂ → ℂ}
    (hg : ∀ ω ∈ Λ, ∀ z, U1 Λ ω g z = (if ω / 2 ∈ Λ then 1 else -1) * g z) :
    ∀ ω ∈ Λ, ∀ z, ‖g (z + ω)‖ ^ 2 * Real.exp (-π * ‖z + ω‖ ^ 2 / area Λ) =
      ‖g z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ) := by
  intro ω hω z
  rw [← thetaTranslation_weighted_normSq_mul, hg ω hω, norm_mul]
  split_ifs <;> simp

omit ha h in
/- English proof (translation)
Simplify using `only [nrm1Sq, norm_mul, mul_pow, mul_assoc, setAverage_eq, integral_const_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem odd_theta_norm_smul (c : ℂ) (g : ℂ → ℂ) :
    nrm1Sq Λ (fun z => c * g z) = ‖c‖ ^ 2 * nrm1Sq Λ g := by
  simp only [nrm1Sq, norm_mul, mul_pow, mul_assoc, setAverage_eq, integral_const_mul, smul_eq_mul]
  ring

/- English proof (translation)
Use `haveI := countable_lattice ha h`. Simplify using `only [nrm1Sq, thetaTranslation_weighted_normSq_mul]`. Conclude with `setAverage_add (epsilon_fundamental ha h) (f := fun z => ‖g z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ)) (weight_invariant hg) t`.
-/
theorem odd_theta_norm_translate {g : ℂ → ℂ}
    (hg : ∀ ω ∈ Λ, ∀ z, U1 Λ ω g z = (if ω / 2 ∈ Λ then 1 else -1) * g z) (t : ℂ) :
    nrm1Sq Λ (U1 Λ t g) = nrm1Sq Λ g := by
  haveI := countable_lattice ha h
  simp only [nrm1Sq, thetaTranslation_weighted_normSq_mul]
  exact setAverage_add (epsilon_fundamental ha h)
    (f := fun z => ‖g z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ)) (weight_invariant hg) t

/- English proof (translation)
Use `haveI := countable_lattice ha h`. Take `⟨b, h1, h2, hb⟩` from `exists_basis ha h`. Establish `key` using `ThetaNorm.integral_norm_sq_thetaChar 1 !![(τ : ℂ)] ![1 / 2] ![1 / 2] (by ext i j; fin_cases i; fin_cases j; rfl) (by`. Establish `: (!![(τ : ℂ)]).map Complex.im = Matrix.diagonal fun _ => τ.im`. Use extensionality with `i j`.

Use `fin_cases i`. Use `fin_cases j`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Matrix.PosDef.diagonal fun _ => τ.im_pos)`.

Rewrite using `[nrm1Sq]`. Use `(setAverage_eq_of_fundamental (epsilon_fundamental ha h) hb (f := fun z => ‖canTheta a τ z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ)) (weight_invariant (thetaTranslation_canonicalOddTheta_lattice ha h))).trans ?_` and prove the remaining obligations. Rewrite using `[setAverage_fundamentalDomain]`. Use `Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)) (key.trans (by simp))` and prove the remaining obligations. Establish `e : ∑ i, p i • b i = a * (p (.inl 0) + p (.inr 0) * τ)`.

Simplify using `only [Fintype.sum_sum_type, Fin.sum_univ_one, h1, h2, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (fun i => (((![1 / 2] : Fin 1 → ℝ) i : ℝ) : ℂ)) = ![1 / 2]`. Use extensionality with `i`. Use `fin_cases i`.

Simplify using the standard rewrite rules. Establish `e3 : ((fun i => (p (.inl i) : ℂ)) + (!![(τ : ℂ)]).mulVec fun i => (p (.inr i) : ℂ)) = ![(p (.inl 0) : ℂ) + p (.inr 0) * τ]`. Use extensionality with `i`. Use `fin_cases i`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`.

Simplify using `only [e, e2, e3, canTheta, mul_div_cancel_left₀ _ ha, oddTheta, LatticeAreaBound.area_eq ha h]`. Rewrite using `[norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add, mul_comm]`. Use `congr 2`. Establish `hy` using `τ.im_ne_zero`. Establish `hn` using `norm_ne_zero_iff.2 ha`.

Rewrite using `[show (2 * (τ.im : ℂ)) = ((2 * τ.im : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re, norm_mul, mul_pow, Complex.sq_norm (_ + _)]`. Simplify using `[Complex.normSq_apply, Matrix.mulVec, dotProduct, sq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem odd_theta_norm_canonical : nrm1Sq Λ (canTheta a τ) = (Real.sqrt (2 * τ.im))⁻¹ := by
  haveI := countable_lattice ha h
  obtain ⟨b, h1, h2, hb⟩ := exists_basis ha h
  have key := ThetaNorm.integral_norm_sq_thetaChar 1 !![(τ : ℂ)] ![1 / 2] ![1 / 2]
    (by ext i j; fin_cases i; fin_cases j; rfl)
    (by
      have : (!![(τ : ℂ)]).map Complex.im = Matrix.diagonal fun _ => τ.im := by
        ext i j; fin_cases i; fin_cases j; rfl
      rw [this]
      exact Matrix.PosDef.diagonal fun _ => τ.im_pos)
  rw [nrm1Sq]
  refine (setAverage_eq_of_fundamental (epsilon_fundamental ha h) hb
    (f := fun z => ‖canTheta a τ z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ))
    (weight_invariant (thetaTranslation_canonicalOddTheta_lattice ha h))).trans ?_
  rw [setAverage_fundamentalDomain]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_))
    (key.trans (by simp))
  have e : ∑ i, p i • b i = a * (p (.inl 0) + p (.inr 0) * τ) := by
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, h1, h2, Complex.real_smul]
    ring
  have e2 : (fun i => (((![1 / 2] : Fin 1 → ℝ) i : ℝ) : ℂ)) = ![1 / 2] := by
    ext i; fin_cases i; simp
  have e3 : ((fun i => (p (.inl i) : ℂ)) + (!![(τ : ℂ)]).mulVec fun i => (p (.inr i) : ℂ)) =
      ![(p (.inl 0) : ℂ) + p (.inr 0) * τ] := by
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct, mul_comm]
  simp only [e, e2, e3, canTheta, mul_div_cancel_left₀ _ ha, oddTheta,
    LatticeAreaBound.area_eq ha h]
  rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add,
    mul_comm]
  congr 2
  have hy := τ.im_ne_zero
  have hn := norm_ne_zero_iff.2 ha
  rw [show (2 * (τ.im : ℂ)) = ((2 * τ.im : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re,
    norm_mul, mul_pow, Complex.sq_norm (_ + _)]
  simp [Complex.normSq_apply, Matrix.mulVec, dotProduct, sq]
  field_simp
  ring

end

/- English proof (translation)
Introduce `Λ hΛ hd`. Take `⟨⟨-, -, -, hU⟩, -, huniq, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ hΛ`. Take `⟨w₁, w₂, hi, hΛ⟩` from `hΛ`. Set `L : PeriodPair` to `⟨w₁, w₂, hi⟩`. Establish `hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice` using `fun z => by`.

Rewrite using `[hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`. Simplify using `[L]`. Take `⟨a, τ, ha, h'⟩` from `exists_lattice_eq_mul_tau L`. Establish `h` using `fun x => (hL x).trans (h' x)`. Establish `hy` using `τ.im_pos`.

Establish `hn` using `norm_pos_iff.2 ha`. Establish `hπ` using `Real.pi_pos`. Use `⟨?_, fun t _ => ?_⟩` and prove the remaining obligations. Rewrite `hd` using `[LatticeAreaBound.discr_eq L _ hL, ← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h']`. Establish `hπ' : ‖(2 * π : ℂ)‖ = 2 * π` using `by simp [hπ.le]`.

Establish `e` using `congrArg norm hd`. Rewrite `e` using `[norm_mul, norm_pow, norm_div, hπ', norm_one, div_pow, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)]`. Establish `j` using `congrArg norm (JacobiDeriv.deriv_thetaChar_pow_eight τ)`. Rewrite `j` using `[norm_mul, norm_pow, norm_pow, hπ']`. Express the relevant statement in the definitionally equal form `‖deriv (oddTheta τ) 0‖ ^ 8 = _ at j`.

Establish `hG : canTheta a τ = fun z => deriv (canTheta a τ) 0 * sgStar Λ z`. Use function extensionality and compare the values at `(huniq _ (differentiable_canTheta a τ) (thetaTranslation_canonicalOddTheta_lattice ha h))`. Establish `k` using `odd_theta_norm_canonical ha h`. Rewrite `k` using `[hG, odd_theta_norm_smul, deriv_canTheta, norm_div]`. Use `set d := ‖deriv (oddTheta τ) 0‖`.

Establish `hd4 : d ^ 4 * (2 * π) ^ 2 = ‖a‖ ^ 6`. Use `(pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations. Take the linear combination `(2 * π) ^ 4 * j + e`. Establish `k2 : ((d / ‖a‖) ^ 2 * nrm1Sq Λ (sgStar Λ)) ^ 2 = (2 * τ.im)⁻¹`. Rewrite using `[k, inv_pow, Real.sq_sqrt (by positivity)]`.

Rewrite using `[LatticeAreaBound.area_eq ha h]`. Generalize the expression as in `nrm1Sq Λ (sgStar Λ) = N at k2 ⊢`. Clear denominators, using `at k2 ⊢` for the nonvanishing conditions. Use `mul_left_cancel₀ (pow_pos hn 4).ne' ?_` and prove the remaining obligations. Take the linear combination `2 * π ^ 2 * k2 - N ^ 2 * τ.im * hd4`.

Establish `: GL3Theta.th0 Λ t = fun z => (U1 Λ t (sgStar Λ) 0)⁻¹ * U1 Λ t (sgStar Λ) z`. Use function extensionality and compare the values at `fun z => div_eq_inv_mul _ _`. Rewrite using `[this, odd_theta_norm_smul, odd_theta_norm_translate ha h hU, norm_inv, inv_pow, div_eq_inv_mul]`.
-/
theorem odd_theta_norm_sigma_star : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → nrm1Sq Λ (sgStar Λ) ^ 2 = 2 * Real.pi ^ 2 / area Λ ∧ ∀ t, U1 Λ t (sgStar Λ) 0 ≠ 0 → nrm1Sq Λ (GL3Theta.th0 Λ t) = nrm1Sq Λ (sgStar Λ) / ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 := by
  intro Λ hΛ hd
  obtain ⟨⟨-, -, -, hU⟩, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨w₁, w₂, hi, hΛ⟩ := hΛ
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨a, τ, ha, h'⟩ := exists_lattice_eq_mul_tau L
  have h := fun x => (hL x).trans (h' x)
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have hπ := Real.pi_pos
  refine ⟨?_, fun t _ => ?_⟩
  · rw [LatticeAreaBound.discr_eq L _ hL, ← latticeCurve_Δ,
      latticeCurve_Δ_eq_discriminant ha h'] at hd
    have hπ' : ‖(2 * π : ℂ)‖ = 2 * π := by simp [hπ.le]
    have e := congrArg norm hd
    rw [norm_mul, norm_pow, norm_div, hπ', norm_one, div_pow, div_mul_eq_mul_div,
      div_eq_one_iff_eq (by positivity)] at e
    have j := congrArg norm (JacobiDeriv.deriv_thetaChar_pow_eight τ)
    rw [norm_mul, norm_pow, norm_pow, hπ'] at j
    change ‖deriv (oddTheta τ) 0‖ ^ 8 = _ at j
    have hG : canTheta a τ = fun z => deriv (canTheta a τ) 0 * sgStar Λ z :=
      funext (huniq _ (differentiable_canTheta a τ) (thetaTranslation_canonicalOddTheta_lattice ha h))
    have k := odd_theta_norm_canonical ha h
    rw [hG, odd_theta_norm_smul, deriv_canTheta, norm_div] at k
    set d := ‖deriv (oddTheta τ) 0‖
    have hd4 : d ^ 4 * (2 * π) ^ 2 = ‖a‖ ^ 6 := by
      refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
      linear_combination (2 * π) ^ 4 * j + e
    have k2 : ((d / ‖a‖) ^ 2 * nrm1Sq Λ (sgStar Λ)) ^ 2 = (2 * τ.im)⁻¹ := by
      rw [k, inv_pow, Real.sq_sqrt (by positivity)]
    rw [LatticeAreaBound.area_eq ha h]
    generalize nrm1Sq Λ (sgStar Λ) = N at k2 ⊢
    field_simp at k2 ⊢
    refine mul_left_cancel₀ (pow_pos hn 4).ne' ?_
    linear_combination 2 * π ^ 2 * k2 - N ^ 2 * τ.im * hd4
  · have : GL3Theta.th0 Λ t = fun z => (U1 Λ t (sgStar Λ) 0)⁻¹ * U1 Λ t (sgStar Λ) z :=
      funext fun z => div_eq_inv_mul _ _
    rw [this, odd_theta_norm_smul, odd_theta_norm_translate ha h hU, norm_inv, inv_pow, div_eq_inv_mul]

end GlobalTheory.OddThetaNorm
