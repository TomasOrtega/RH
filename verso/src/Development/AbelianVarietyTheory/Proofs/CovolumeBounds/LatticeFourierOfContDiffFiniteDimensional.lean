import Mathlib

open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff

noncomputable section

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))

def latticeCell (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] : Set E :=
  ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)

def latticeFourierCoeff (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : E → V) (ν : E) : V :=
  (ZLattice.covolume L)⁻¹ • ∫ b in latticeCell L, e[-⟪ν, b⟫] • A b

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L

/- English proof (translation)
The claim follows from `ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ`.
-/
theorem isAddFundamentalDomain_latticeCell (μ : Measure E) :
    IsAddFundamentalDomain L (latticeCell L) μ :=
  ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ

omit [MeasurableSpace E] [BorelSpace E] in
/- English proof (translation)
The claim follows from `ZSpan.fundamentalDomain_isBounded _`.
-/
theorem isBounded_latticeCell : Bornology.IsBounded (latticeCell L) :=
  ZSpan.fundamentalDomain_isBounded _

/- English proof (translation)
The claim follows from `ZSpan.fundamentalDomain_measurableSet _`.
-/
theorem measurableSet_latticeCell : MeasurableSet (latticeCell L) :=
  ZSpan.fundamentalDomain_measurableSet _

/- English proof (translation)
The claim follows from `(isBounded_latticeCell L).measure_lt_top`.
-/
theorem volume_latticeCell_lt_top : volume (latticeCell L) < ⊤ :=
  (isBounded_latticeCell L).measure_lt_top

/- English proof (translation)
The claim follows from `ZLattice.covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain_latticeCell L _)`.
-/
theorem covolume_eq_volume_latticeCell : ZLattice.covolume L = volume.real (latticeCell L) :=
  ZLattice.covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain_latticeCell L _)

/- English proof (translation)
The claim follows from `(hf.continuousOn.integrableOn_compact (isBounded_latticeCell L).isCompact_closure).mono_set subset_closure`.
-/
theorem integrableOn_latticeCell_of_continuous {W : Type*} [NormedAddCommGroup W] {f : E → W}
    (hf : Continuous f) : IntegrableOn f (latticeCell L) :=
  (hf.continuousOn.integrableOn_compact (isBounded_latticeCell L).isCompact_closure).mono_set
    subset_closure

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
/- English proof (translation)
Simplify using `[LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one]`.
-/
theorem mem_innerDual_iff {ν : E} : ν ∈ L* ↔ ∀ x ∈ L, ∃ n : ℤ, (n : ℝ) = ⟪ν, x⟫ := by
  simp [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one]

/- English proof (translation)
Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cexp_two_pi_I_add (s t : ℝ) : e[s + t] = e[s] * e[t] := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[← Complex.exp_int_mul_two_pi_mul_I n]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cexp_two_pi_I_intCast (n : ℤ) : e[(n : ℝ)] = 1 := by
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[← Complex.exp_pi_mul_I]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cexp_two_pi_I_half : e[1 / 2] = -1 := by
  rw [← Complex.exp_pi_mul_I]
  congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[← Complex.norm_exp_ofReal_mul_I (2 * π * t)]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_cexp_two_pi_I (t : ℝ) : ‖e[t]‖ = 1 := by
  rw [← Complex.norm_exp_ofReal_mul_I (2 * π * t)]
  congr 2; push_cast; ring

variable {L}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
/- English proof (translation)
Take `⟨n, hn⟩` from `(mem_innerDual_iff L).1 hν x hx`. Rewrite using `[inner_add_right, cexp_two_pi_I_add, ← hn, cexp_two_pi_I_intCast, mul_one]`.
-/
theorem cexp_inner_add_lattice {ν : E} (hν : ν ∈ L*) {x : E} (hx : x ∈ L) (b : E) :
    e[⟪ν, b + x⟫] = e[⟪ν, b⟫] := by
  obtain ⟨n, hn⟩ := (mem_innerDual_iff L).1 hν x hx
  rw [inner_add_right, cexp_two_pi_I_add, ← hn, cexp_two_pi_I_intCast, mul_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
/- English proof (translation)
Rewrite using `[← inner_neg_left, ← inner_neg_left, cexp_inner_add_lattice (neg_mem hν) hx]`.
-/
theorem cexp_neg_inner_add_lattice {ν : E} (hν : ν ∈ L*) {x : E} (hx : x ∈ L) (b : E) :
    e[-⟪ν, b + x⟫] = e[-⟪ν, b⟫] := by
  rw [← inner_neg_left, ← inner_neg_left, cexp_inner_add_lattice (neg_mem hν) hx]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/- English proof (translation)
Use `fun_prop`.
-/
theorem continuous_cexp_neg_inner_smul {A : E → V} (hA : Continuous A) (ν : E) :
    Continuous fun b : E ↦ e[-⟪ν, b⟫] • A b := by
  fun_prop

/- English proof (translation)
Establish `: MeasurableVAdd L E` using `(inferInstance : MeasurableVAdd L.toAddSubgroup E)`. Establish `: VAddInvariantMeasure L E volume` using `(inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)`. Unfold `latticeFourierCoeff`. Use `congr 1`. Use `(isAddFundamentalDomain_latticeCell L _).setIntegral_eq hF fun x b ↦ ?_` and prove the remaining obligations.

Establish `: x +ᵥ b = b + (x : E)` using `add_comm _ _`. Rewrite using `[this, cexp_neg_inner_add_lattice hν x.2, hA x x.2]`.
-/
theorem latticeFourierCoeff_eq_setIntegral {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {ν : E} (hν : ν ∈ L*) {F : Set E} (hF : IsAddFundamentalDomain L F volume) :
    latticeFourierCoeff L A ν =
      (ZLattice.covolume L)⁻¹ • ∫ b in F, e[-⟪ν, b⟫] • A b := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  unfold latticeFourierCoeff
  congr 1
  refine (isAddFundamentalDomain_latticeCell L _).setIntegral_eq hF fun x b ↦ ?_
  have : x +ᵥ b = b + (x : E) := add_comm _ _
  rw [this, cexp_neg_inner_add_lattice hν x.2, hA x x.2]

/- English proof (translation)
Establish `hpos` using `ZLattice.covolume_pos L volume`. Unfold `latticeFourierCoeff`. Rewrite using `[norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos, covolume_eq_volume_latticeCell, mul_comm _ S]`. Use `norm_setIntegral_le_of_norm_le_const (volume_latticeCell_lt_top L) fun b _ ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_cexp_two_pi_I, one_mul]`.

Conclude with `hS b`.
-/
theorem norm_latticeFourierCoeff_le {A : E → V} {S : ℝ} (hS : ∀ b, ‖A b‖ ≤ S) (ν : E) :
    ‖latticeFourierCoeff L A ν‖ ≤ S := by
  have hpos := ZLattice.covolume_pos L volume
  unfold latticeFourierCoeff
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos,
    covolume_eq_volume_latticeCell, mul_comm _ S]
  refine norm_setIntegral_le_of_norm_le_const (volume_latticeCell_lt_top L) fun b _ ↦ ?_
  rw [norm_smul, norm_cexp_two_pi_I, one_mul]
  exact hS b

/- English proof (translation)
Establish `: MeasurableVAdd L E` using `(inferInstance : MeasurableVAdd L.toAddSubgroup E)`. Establish `: VAddCommClass E L E` using `⟨fun a x b ↦ add_left_comm a (x : E) b⟩`. Establish `hF : IsAddFundamentalDomain L (c +ᵥ latticeCell L) volume` using `(isAddFundamentalDomain_latticeCell L _).vadd_of_comm c`. Rewrite using `[latticeFourierCoeff_eq_setIntegral hA hν hF, smul_comm, ← integral_smul, latticeFourierCoeff]`. Use `congr 1`.

Rewrite using `[show c +ᵥ latticeCell L = (fun x ↦ c + x) '' latticeCell L from rfl, (measurePreserving_add_left volume c).setIntegral_image_emb (measurableEmbedding_addLeft c)]`. Use `integral_congr_ae (.of_forall fun b ↦ ?_)` and prove the remaining obligations. Simplify using `only [smul_smul, ← cexp_two_pi_I_add, inner_add_right, add_comm c b]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latticeFourierCoeff_comp_add {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {ν : E} (hν : ν ∈ L*) (c : E) :
    latticeFourierCoeff L (fun b ↦ A (b + c)) ν =
      e[⟪ν, c⟫] • latticeFourierCoeff L A ν := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddCommClass E L E := ⟨fun a x b ↦ add_left_comm a (x : E) b⟩
  have hF : IsAddFundamentalDomain L (c +ᵥ latticeCell L) volume :=
    (isAddFundamentalDomain_latticeCell L _).vadd_of_comm c
  rw [latticeFourierCoeff_eq_setIntegral hA hν hF, smul_comm, ← integral_smul,
    latticeFourierCoeff]
  congr 1
  rw [show c +ᵥ latticeCell L = (fun x ↦ c + x) '' latticeCell L from rfl,
    (measurePreserving_add_left volume c).setIntegral_image_emb
    (measurableEmbedding_addLeft c)]
  refine integral_congr_ae (.of_forall fun b ↦ ?_)
  simp only [smul_smul, ← cexp_two_pi_I_add, inner_add_right, add_comm c b]
  congr 4; ring

/- English proof (translation)
Simplify using `only [latticeFourierCoeff, smul_add]`. Rewrite using `[integral_add (integrableOn_latticeCell_of_continuous L (continuous_cexp_neg_inner_smul hA ν)) (integrableOn_latticeCell_of_continuous L (continuous_cexp_neg_inner_smul hB ν)), smul_add]`.
-/
theorem latticeFourierCoeff_add {A B : E → V} (hA : Continuous A) (hB : Continuous B) (ν : E) :
    latticeFourierCoeff L (fun b ↦ A b + B b) ν =
      latticeFourierCoeff L A ν + latticeFourierCoeff L B ν := by
  simp only [latticeFourierCoeff, smul_add]
  rw [integral_add (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hA ν)) (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hB ν)), smul_add]

/- English proof (translation)
Simplify using `only [latticeFourierCoeff, smul_sub]`. Rewrite using `[integral_sub (integrableOn_latticeCell_of_continuous L (continuous_cexp_neg_inner_smul hA ν)) (integrableOn_latticeCell_of_continuous L (continuous_cexp_neg_inner_smul hB ν)), smul_sub]`.
-/
theorem latticeFourierCoeff_sub {A B : E → V} (hA : Continuous A) (hB : Continuous B) (ν : E) :
    latticeFourierCoeff L (fun b ↦ A b - B b) ν =
      latticeFourierCoeff L A ν - latticeFourierCoeff L B ν := by
  simp only [latticeFourierCoeff, smul_sub]
  rw [integral_sub (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hA ν)) (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hB ν)), smul_sub]

/- English proof (translation)
Simplify using `only [latticeFourierCoeff, smul_comm _ a, integral_smul]`.
-/
theorem latticeFourierCoeff_smul (a : ℂ) (A : E → V) (ν : E) :
    latticeFourierCoeff L (fun b ↦ a • A b) ν = a • latticeFourierCoeff L A ν := by
  simp only [latticeFourierCoeff, smul_comm _ a, integral_smul]

/- English proof (translation)
Simplify using `only [latticeFourierCoeff, ← map_smul]`. Rewrite using `[T.integral_comp_comm (integrableOn_latticeCell_of_continuous L (continuous_cexp_neg_inner_smul hA ν)), T.map_smul_of_tower]`.
-/
theorem latticeFourierCoeff_clm [CompleteSpace V] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [CompleteSpace W] (T : V →L[ℂ] W) {A : E → V} (hA : Continuous A) (ν : E) :
    latticeFourierCoeff L (fun b ↦ T (A b)) ν = T (latticeFourierCoeff L A ν) := by
  simp only [latticeFourierCoeff, ← map_smul]
  rw [T.integral_comp_comm (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hA ν)), T.map_smul_of_tower]

/- English proof (translation)
Proceed by induction on `k generalizing A with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h1 : ∀ x ∈ L, Function.Periodic (fwdDiff c A) x` using `fun x hx b ↦ by`. Simplify using `only [fwdDiff, add_right_comm b x c, hA x hx b, hA x hx (b + c)]`.

Establish `h2 : Continuous (fwdDiff c A)` using `by unfold fwdDiff; fun_prop`. Rewrite using `[Function.iterate_succ_apply, ih h1 h2, pow_succ, mul_smul]`. Use `congr 1`. Unfold `fwdDiff`. Rewrite using `[latticeFourierCoeff_sub (by fun_prop) hc, latticeFourierCoeff_comp_add hA hν, sub_smul, one_smul]`.
-/
theorem latticeFourierCoeff_fwdDiff_iter {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    (hc : Continuous A) {ν : E} (hν : ν ∈ L*) (c : E) (k : ℕ) :
    latticeFourierCoeff L ((fwdDiff c)^[k] A) ν =
      (e[⟪ν, c⟫] - 1) ^ k • latticeFourierCoeff L A ν := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ x ∈ L, Function.Periodic (fwdDiff c A) x := fun x hx b ↦ by
      simp only [fwdDiff, add_right_comm b x c, hA x hx b, hA x hx (b + c)]
    have h2 : Continuous (fwdDiff c A) := by unfold fwdDiff; fun_prop
    rw [Function.iterate_succ_apply, ih h1 h2, pow_succ, mul_smul]
    congr 1
    unfold fwdDiff
    rw [latticeFourierCoeff_sub (by fun_prop) hc, latticeFourierCoeff_comp_add hA hν, sub_smul,
      one_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

/- English proof (translation)
Proceed by induction on `k generalizing A M with`. Consider the case `zero => simpa using hM x`. Consider the case `succ k ih`. Establish `hA' : ContDiff ℝ k A` using `hA.of_le (by exact_mod_cast k.le_succ)`. Establish `hAc : ContDiff ℝ k fun y ↦ A (y + c)` using `hA'.comp (by fun_prop)`.

Rewrite using `[Function.iterate_succ_apply, pow_succ, mul_assoc]`. Use `ih (hAc.sub hA') fun y ↦ ?_` and prove the remaining obligations. Establish `hd : Differentiable ℝ (iteratedFDeriv ℝ k A)` using `hA.differentiable_iteratedFDeriv (by exact_mod_cast k.lt_succ_self)`. Use `Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (C := M) (f := iteratedFDeriv ℝ k A) (x := y) (y := y + c) (fun z _ ↦ hd z) (fun z _ ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM z) convex_univ trivial trivial` as an intermediate fact. Rewrite using `[fun_iteratedFDeriv_sub_apply hAc.contDiffAt hA'.contDiffAt, iteratedFDeriv_comp_add_right]`.

Simplify `this` using `[mul_comm]`.
-/
theorem norm_fwdDiff_iter_le (c : E) (k : ℕ) {A : E → V} (hA : ContDiff ℝ k A) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ M) (x : E) :
    ‖(fwdDiff c)^[k] A x‖ ≤ ‖c‖ ^ k * M := by
  induction k generalizing A M with
  | zero => simpa using hM x
  | succ k ih =>
    have hA' : ContDiff ℝ k A := hA.of_le (by exact_mod_cast k.le_succ)
    have hAc : ContDiff ℝ k fun y ↦ A (y + c) := hA'.comp (by fun_prop)
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc]
    refine ih (hAc.sub hA') fun y ↦ ?_
    have hd : Differentiable ℝ (iteratedFDeriv ℝ k A) :=
      hA.differentiable_iteratedFDeriv (by exact_mod_cast k.lt_succ_self)
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (C := M)
      (f := iteratedFDeriv ℝ k A) (x := y) (y := y + c) (fun z _ ↦ hd z)
      (fun z _ ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM z) convex_univ trivial trivial
    rw [fun_iteratedFDeriv_sub_apply hAc.contDiffAt hA'.contDiffAt, iteratedFDeriv_comp_add_right]
    simpa [mul_comm] using this

omit [MeasurableSpace E] [BorelSpace E] in

/- English proof (translation)
Take `⟨M, hM⟩` from `(isBounded_latticeCell L).isCompact_closure.exists_bound_of_continuousOn hc.continuousOn`. Use `⟨M, fun b ↦ ?_⟩` and prove the remaining obligations. Take `⟨v, hv, -⟩` from `ZSpan.exist_unique_vadd_mem_fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) b`. Establish `hvL : (v : E) ∈ L` using `((Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ).le v.2`. Rewrite using `[← hf v hvL b, add_comm]`.

Conclude with `hM _ (subset_closure hv)`.
-/
theorem exists_bound_of_lattice_periodic {W : Type*} [NormedAddCommGroup W] {f : E → W}
    (hf : ∀ x ∈ L, Function.Periodic f x) (hc : Continuous f) : ∃ M, ∀ b, ‖f b‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isBounded_latticeCell L).isCompact_closure.exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun b ↦ ?_⟩
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) b
  have hvL : (v : E) ∈ L := ((Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ).le v.2
  rw [← hf v hvL b, add_comm]
  exact hM _ (subset_closure hv)

/- English proof (translation)
Break down `eq_or_ne ν 0 with rfl | h0` into its components or cases. Break down `k with _ | k` into its components or cases. Simplify `hM b) 0` using `using norm_latticeFourierCoeff_le (fun b ↦ by simpa`. Simplify using `using (norm_nonneg _).trans (hM 0)`. Establish `hn : 0 < ‖ν‖` using `norm_pos_iff.2 h0`.

Use `set c : E := (2 * ‖ν‖ ^ 2)⁻¹ • ν with hc`. Establish `h1 : ⟪ν, c⟫ = 1 / 2`. Rewrite using `[hc, inner_smul_right, real_inner_self_eq_norm_sq]`. Clear the denominators using the available nonvanishing facts. Establish `h2 : ‖c‖ = (2 * ‖ν‖)⁻¹`.

Rewrite using `[hc, norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp`. Establish `h3` using `norm_latticeFourierCoeff_le (L := L) (norm_fwdDiff_iter_le c k hk hM) ν`. Rewrite `h3` using `[latticeFourierCoeff_fwdDiff_iter hA hk.continuous hν, h1, cexp_two_pi_I_half, norm_smul, norm_pow, h2, inv_pow, le_inv_mul_iff₀ (by positivity), ← mul_assoc, ← mul_pow]`. Establish `h4 : ‖(-1 - 1 : ℂ)‖ = 2` using `by norm_num`. Rewrite `h3` using `[h4, show 2 * ‖ν‖ * 2 = 4 * ‖ν‖ by ring]`. Then use the resulting hypothesis.
-/
theorem pow_mul_norm_latticeFourierCoeff_le {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {k : ℕ} (hk : ContDiff ℝ k A) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ M)
    {ν : E} (hν : ν ∈ L*) :
    (4 * ‖ν‖) ^ k * ‖latticeFourierCoeff L A ν‖ ≤ M := by
  rcases eq_or_ne ν 0 with rfl | h0
  · rcases k with _ | k
    · simpa using norm_latticeFourierCoeff_le (fun b ↦ by simpa using hM b) 0
    · simpa using (norm_nonneg _).trans (hM 0)
  have hn : 0 < ‖ν‖ := norm_pos_iff.2 h0
  set c : E := (2 * ‖ν‖ ^ 2)⁻¹ • ν with hc
  have h1 : ⟪ν, c⟫ = 1 / 2 := by
    rw [hc, inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have h2 : ‖c‖ = (2 * ‖ν‖)⁻¹ := by
    rw [hc, norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  have h3 := norm_latticeFourierCoeff_le (L := L) (norm_fwdDiff_iter_le c k hk hM) ν
  rw [latticeFourierCoeff_fwdDiff_iter hA hk.continuous hν, h1, cexp_two_pi_I_half, norm_smul,
    norm_pow, h2, inv_pow, le_inv_mul_iff₀ (by positivity), ← mul_assoc, ← mul_pow] at h3
  have h4 : ‖(-1 - 1 : ℂ)‖ = 2 := by norm_num
  rwa [h4, show 2 * ‖ν‖ * 2 = 4 * ‖ν‖ by ring] at h3

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Establish `hpos` using `ZLattice.covolume_pos L volume`. Simplify using `only [latticeFourierCoeff, smul_smul, ← cexp_two_pi_I_add, neg_add_cancel]`. Simplify using `[← covolume_eq_volume_latticeCell, smul_smul, hpos.ne']`.

Establish `hn : 0 < ‖μ - ν‖` using `norm_pos_iff.2 (sub_ne_zero.2 h) set c : E := (2 * ‖μ - ν‖ ^ 2)⁻¹ • (μ - ν) with hc`. Establish `h1 : ⟪μ, c⟫ = ⟪ν, c⟫ + 1 / 2`. Rewrite using `[← sub_eq_iff_eq_add', ← inner_sub_left, hc, inner_smul_right, real_inner_self_eq_norm_sq]`. Clear the denominators using the available nonvanishing facts. Establish `h2` using `latticeFourierCoeff_comp_add (L := L) (A := fun b ↦ e[⟪μ, b⟫] • v) (fun x hx b ↦ by simp only [cexp_inner_add_lattice hμ hx]) hν c`.

Simplify using `only [inner_add_right, cexp_two_pi_I_add, mul_comm _ e[⟪μ, c⟫], mul_smul] at h2`. Rewrite `h2` using `[latticeFourierCoeff_smul, h1, cexp_two_pi_I_add, cexp_two_pi_I_half, ← sub_eq_zero, ← sub_smul, smul_eq_zero]`. Use `h2.resolve_left fun h3 ↦ Complex.exp_ne_zero (2 * π * Complex.I * (⟪ν, c⟫ : ℝ)) ?_` and prove the remaining obligations. Take the linear combination `(-1 / 2 : ℂ) * h3`.
-/
theorem latticeFourierCoeff_cexp_smul [CompleteSpace V] [DecidableEq E] {μ ν : E} (hμ : μ ∈ L*)
    (hν : ν ∈ L*) (v : V) :
    latticeFourierCoeff L (fun b ↦ e[⟪μ, b⟫] • v) ν = if μ = ν then v else 0 := by
  split_ifs with h
  · subst h
    have hpos := ZLattice.covolume_pos L volume
    simp only [latticeFourierCoeff, smul_smul, ← cexp_two_pi_I_add, neg_add_cancel]
    simp [← covolume_eq_volume_latticeCell, smul_smul, hpos.ne']
  · have hn : 0 < ‖μ - ν‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
    set c : E := (2 * ‖μ - ν‖ ^ 2)⁻¹ • (μ - ν) with hc
    have h1 : ⟪μ, c⟫ = ⟪ν, c⟫ + 1 / 2 := by
      rw [← sub_eq_iff_eq_add', ← inner_sub_left, hc, inner_smul_right,
        real_inner_self_eq_norm_sq]; field_simp
    have h2 := latticeFourierCoeff_comp_add (L := L) (A := fun b ↦ e[⟪μ, b⟫] • v)
      (fun x hx b ↦ by simp only [cexp_inner_add_lattice hμ hx]) hν c
    simp only [inner_add_right, cexp_two_pi_I_add, mul_comm _ e[⟪μ, c⟫], mul_smul] at h2
    rw [latticeFourierCoeff_smul, h1, cexp_two_pi_I_add, cexp_two_pi_I_half, ← sub_eq_zero,
      ← sub_smul, smul_eq_zero] at h2
    refine h2.resolve_left fun h3 ↦ Complex.exp_ne_zero (2 * π * Complex.I * (⟪ν, c⟫ : ℝ)) ?_
    linear_combination (-1 / 2 : ℂ) * h3

/- English proof (translation)
Simplify using `only [← fun j ↦ latticeFourierCoeff_cexp_smul (hm j) hν (a j), latticeFourierCoeff]`. Use `HasSum.const_smul _ ?_` and prove the remaining obligations. Simplify using `only [← tsum_const_smul'' e[-⟪ν, _⟫]]`. Use `hasSum_integral_of_summable_integral_norm (fun j ↦ integrableOn_latticeCell_of_continuous L (by fun_prop)) ?_` and prove the remaining obligations. Simplify using `only [norm_smul, norm_cexp_two_pi_I, one_mul, integral_const]`.

Conclude with `ha.const_smul _`.
-/
theorem hasSum_latticeFourierCoeff_tsum [CompleteSpace V] [DecidableEq E] {ι : Type*}
    [Countable ι] {m : ι → E} (hm : ∀ j, m j ∈ L*) {a : ι → V} (ha : Summable fun j ↦ ‖a j‖)
    {ν : E} (hν : ν ∈ L*) :
    HasSum (fun j ↦ if m j = ν then a j else 0)
      (latticeFourierCoeff L (fun b ↦ ∑' j, e[⟪m j, b⟫] • a j) ν) := by
  simp only [← fun j ↦ latticeFourierCoeff_cexp_smul (hm j) hν (a j), latticeFourierCoeff]
  refine HasSum.const_smul _ ?_
  simp only [← tsum_const_smul'' e[-⟪ν, _⟫]]
  refine hasSum_integral_of_summable_integral_norm (fun j ↦ integrableOn_latticeCell_of_continuous L
    (by fun_prop)) ?_
  simp only [norm_smul, norm_cexp_two_pi_I, one_mul, integral_const]
  exact ha.const_smul _

omit [InnerProductSpace ℝ E] in

/- English proof (translation)
Use `set T := b.equivFunL.symm with hT`. Establish `hae : T ⁻¹' ZSpan.fundamentalDomain b =ᵐ[volume] {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1}`. Establish `h1 : T ⁻¹' ZSpan.fundamentalDomain b = Set.pi univ fun _ ↦ Ico (0 : ℝ) 1`. Use extensionality with `x`. Establish `: ∀ i, b.repr (T x) i = x i` using `fun i ↦ congrFun (b.equivFun.apply_symm_apply x) i`.

Simplify using `only [mem_preimage, ZSpan.mem_fundamentalDomain, this, mem_univ_pi]`. Establish `h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2]`.

Conclude with `Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm`. Establish `hemb : MeasurableEmbedding T` using `T.toHomeomorph.measurableEmbedding`. Establish `hμ` using `Measure.isAddLeftInvariant_eq_smul (Measure.map T volume) μ`. Use `set c := Measure.addHaarScalarFactor (Measure.map T volume) μ`. Establish `hone : (Measure.map T volume).real (ZSpan.fundamentalDomain b) = 1`.

Rewrite using `[measureReal_def, hemb.map_apply, measure_congr hae]`. Establish `h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[h2, Real.volume_pi_Ioc]`.

Simplify using the standard rewrite rules. Establish `hint` using `hemb.setIntegral_map (μ := volume) g (ZSpan.fundamentalDomain b)`. Rewrite `hint` using `[setIntegral_congr_set hae]`. Rewrite `hone` using `[hμ, measureReal_nnreal_smul_apply]`. Rewrite `hint` using `[hμ, Measure.restrict_smul, integral_smul_nnreal_measure]`.

Rewrite using `[← eq_inv_of_mul_eq_one_left hone]`. Conclude with `hint`.
-/
theorem average_fundamentalDomain_eq_cube [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → V) :
    (μ.real (ZSpan.fundamentalDomain b))⁻¹ • ∫ y in ZSpan.fundamentalDomain b, g y ∂μ =
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1}, g (b.equivFun.symm x) := by
  set T := b.equivFunL.symm with hT
  have hae : T ⁻¹' ZSpan.fundamentalDomain b =ᵐ[volume] {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} := by
    have h1 : T ⁻¹' ZSpan.fundamentalDomain b = Set.pi univ fun _ ↦ Ico (0 : ℝ) 1 := by
      ext x
      have : ∀ i, b.repr (T x) i = x i := fun i ↦ congrFun (b.equivFun.apply_symm_apply x) i
      simp only [mem_preimage, ZSpan.mem_fundamentalDomain, this, mem_univ_pi]
    have h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1 := by
      ext x; simp
    rw [h1, h2]
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hμ := Measure.isAddLeftInvariant_eq_smul (Measure.map T volume) μ
  set c := Measure.addHaarScalarFactor (Measure.map T volume) μ
  have hone : (Measure.map T volume).real (ZSpan.fundamentalDomain b) = 1 := by
    rw [measureReal_def, hemb.map_apply, measure_congr hae]
    have h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1 := by
      ext x; simp
    rw [h2, Real.volume_pi_Ioc]
    simp
  have hint := hemb.setIntegral_map (μ := volume) g (ZSpan.fundamentalDomain b)
  rw [setIntegral_congr_set hae] at hint
  rw [hμ, measureReal_nnreal_smul_apply] at hone
  rw [hμ, Measure.restrict_smul, integral_smul_nnreal_measure] at hint
  rw [← eq_inv_of_mul_eq_one_left hone]
  exact hint

/- English proof (translation)
Establish `: MeasurableVAdd L E` using `(inferInstance : MeasurableVAdd L.toAddSubgroup E)`. Establish `: VAddInvariantMeasure L E μ` using `(inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)`. Rewrite using `[← (isAddFundamentalDomain_latticeCell L μ).setIntegral_eq hF fun x b ↦ ?_, ZLattice.covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain_latticeCell L μ), latticeFourierCoeff, covolume_eq_volume_latticeCell, latticeCell, average_fundamentalDomain_eq_cube, average_fu …`. Establish `: x +ᵥ b = b + (x : E)` using `add_comm _ _`. Rewrite using `[this, cexp_neg_inner_add_lattice hν x.2, hA x x.2]`.
-/
theorem latticeFourierCoeff_eq_setIntegral_haar {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {ν : E} (hν : ν ∈ L*) (μ : Measure E) [μ.IsAddHaarMeasure] {F : Set E}
    (hF : IsAddFundamentalDomain L F μ) :
    latticeFourierCoeff L A ν = (ZLattice.covolume L μ)⁻¹ • ∫ b in F, e[-⟪ν, b⟫] • A b ∂μ := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [← (isAddFundamentalDomain_latticeCell L μ).setIntegral_eq hF fun x b ↦ ?_,
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain_latticeCell L μ),
    latticeFourierCoeff, covolume_eq_volume_latticeCell, latticeCell,
    average_fundamentalDomain_eq_cube, average_fundamentalDomain_eq_cube]
  have : x +ᵥ b = b + (x : E) := add_comm _ _
  rw [this, cexp_neg_inner_add_lattice hν x.2, hA x x.2]

omit [MeasurableSpace E] [BorelSpace E] in
variable (L) in

/- English proof (translation)
Establish `hB : LinearMap.BilinForm.Nondegenerate (innerₗ E)`. Apply the tactic sequence `refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> simpa using hx x`. Use `set b₀ := b.ofZLatticeBasis ℝ L`. Use `set b' := LinearMap.BilinForm.dualBasis _ hB b₀`. Establish `h : L* = Submodule.span ℤ (range b')`.

Rewrite using `[← LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB, b.ofZLatticeBasis_span ℝ]`. Use `⟨b', h, ((b'.restrictScalars ℤ).equivFun.symm.trans (LinearEquiv.ofEq _ _ h.symm)).toEquiv, fun n x ↦ ?_⟩` and prove the remaining obligations. Establish `hij : ∀ i j, ⟪b' i, b₀ j⟫ = if j = i then 1 else 0` using `fun i j ↦ LinearMap.BilinForm.apply_dualBasis_left hB b₀ i j`. Simplify using `[sum_inner, inner_sum, inner_smul_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, hij, mul_comm]`.
-/
theorem exists_equiv_innerDual {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    ∃ b' : Basis ι ℝ E, L* = Submodule.span ℤ (range b') ∧ ∃ φ : (ι → ℤ) ≃ L*,
      ∀ n x, ⟪(φ n : E), (b.ofZLatticeBasis ℝ L).equivFun.symm x⟫ = ∑ i, n i * x i := by
  classical
  have hB : LinearMap.BilinForm.Nondegenerate (innerₗ E) := by
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> simpa using hx x
  set b₀ := b.ofZLatticeBasis ℝ L
  set b' := LinearMap.BilinForm.dualBasis _ hB b₀
  have h : L* = Submodule.span ℤ (range b') := by
    rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB, b.ofZLatticeBasis_span ℝ]
  refine ⟨b', h, ((b'.restrictScalars ℤ).equivFun.symm.trans
    (LinearEquiv.ofEq _ _ h.symm)).toEquiv, fun n x ↦ ?_⟩
  have hij : ∀ i j, ⟪b' i, b₀ j⟫ = if j = i then 1 else 0 := fun i j ↦
    LinearMap.BilinForm.apply_dualBasis_left hB b₀ i j
  simp [sum_inner, inner_sum, inner_smul_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, hij,
    mul_comm]

omit [MeasurableSpace E] [BorelSpace E] in
/- English proof (translation)
Take `⟨b', h, -⟩` from `exists_equiv_innerDual L (Free.chooseBasis ℤ L)`. Rewrite using `[h]`. Conclude with `ZLattice.summable_norm_pow_inv (Submodule.span ℤ (range b')) k (by rwa [ZLattice.rank ℝ])`.
-/
theorem summable_norm_inv_pow_innerDual {k : ℕ} (hk : finrank ℝ E < k) :
    Summable fun ν : L* ↦ ‖(ν : E)‖⁻¹ ^ k := by
  obtain ⟨b', h, -⟩ := exists_equiv_innerDual L (Free.chooseBasis ℤ L)
  rw [h]
  exact ZLattice.summable_norm_pow_inv (Submodule.span ℤ (range b')) k
    (by rwa [ZLattice.rank ℝ])

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_bound_of_lattice_periodic (L := L) (f := iteratedFDeriv ℝ k A) (fun x hx b ↦ by`. Rewrite using `[← iteratedFDeriv_comp_add_right, show (fun z ↦ A (z + x)) = A from funext (hA x hx)])`. Use the proof step `(hAk.continuous_iteratedFDeriv le_rfl)`. Use `.of_norm_bounded_eventually ((summable_norm_inv_pow_innerDual (L := L) hk).mul_left ((4 ^ k)⁻¹ * M)) ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_cofinite_ne 0] with ν h0`.

Establish `hn : 0 < ‖(ν : E)‖` using `norm_pos_iff.2 (by simpa using h0)`. Use `pow_mul_norm_latticeFourierCoeff_le hA hAk hM ν.2` as an intermediate fact. Rewrite `this` using `[← le_inv_mul_iff₀ (by positivity), mul_pow, mul_inv]`. Rewrite using `[norm_norm, inv_pow, mul_right_comm]`. Conclude with `this`.
-/
theorem summable_norm_latticeFourierCoeff {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {k : ℕ} (hk : finrank ℝ E < k) (hAk : ContDiff ℝ k A) :
    Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖ := by
  obtain ⟨M, hM⟩ := exists_bound_of_lattice_periodic (L := L) (f := iteratedFDeriv ℝ k A)
    (fun x hx b ↦ by
      rw [← iteratedFDeriv_comp_add_right, show (fun z ↦ A (z + x)) = A from funext (hA x hx)])
    (hAk.continuous_iteratedFDeriv le_rfl)
  refine .of_norm_bounded_eventually
    ((summable_norm_inv_pow_innerDual (L := L) hk).mul_left ((4 ^ k)⁻¹ * M)) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with ν h0
  have hn : 0 < ‖(ν : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have := pow_mul_norm_latticeFourierCoeff_le hA hAk hM ν.2
  rw [← le_inv_mul_iff₀ (by positivity), mul_pow, mul_inv] at this
  rw [norm_norm, inv_pow, mul_right_comm]
  exact this

/- English proof (translation)
Use `set b := Free.chooseBasis ℤ L`. Use `set b₀ := b.ofZLatticeBasis ℝ L`. Take `⟨-, -, φ, hφ⟩` from `exists_equiv_innerDual L b`. Use `set p : (Free.ChooseBasisIndex ℤ L → ℝ) → UnitAddTorus (Free.ChooseBasisIndex ℤ L) := fun x i ↦ (x i : UnitAddCircle) with hp`. Establish `hq : IsOpenQuotientMap p` using `IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk`.

Use `set f₀ : UnitAddTorus (Free.ChooseBasisIndex ℤ L) → ℂ := fun z ↦ A (b₀.equivFun.symm (Function.surjInv hq.surjective z)) with hf₀`. Establish `hfp : ∀ x, f₀ (p x) = A (b₀.equivFun.symm x)` using `fun x ↦ by set x' := Function.surjInv hq.surjective (p x)`. Establish `h1 : p x' = p x` using `Function.surjInv_eq _ _`. Establish `h2 : b₀.equivFun.symm (x' - x) ∈ L`. Rewrite using `[Basis.equivFun_symm_apply]`.

Use `sum_mem fun i _ ↦ ?_` and prove the remaining obligations. Establish `h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0`. Rewrite using `[AddCircle.coe_sub, sub_eq_zero]`. Conclude with `congrFun h1 i`. Take `⟨n, hn⟩` from `(AddCircle.coe_eq_zero_iff _).1 h3`.

Rewrite using `[Pi.sub_apply, ← hn, smul_assoc, one_smul]`. Conclude with `L.smul_mem n (by simp [b₀])`. Rewrite using `[← hA _ h2 (b₀.equivFun.symm x), ← map_add, add_sub_cancel]`. Set `f : C(UnitAddTorus (Free.ChooseBasisIndex ℤ L), ℂ)` to `⟨f₀, hq.isQuotientMap.continuous_iff.2 <| by`. Rewrite using `[show f₀ ∘ p = A ∘ b₀.equivFunL.symm from funext hfp]`.

Use the proof step `fun_prop⟩`. Establish `hchar : ∀ n x, UnitAddTorus.mFourier n (p x) = e[∑ i, n i * x i]` using `fun n x ↦ by`. Simplify using `only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply, ← Complex.exp_sum]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ by ring`. Establish `hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = latticeFourierCoeff L A (φ n)` using `fun n ↦ by`. Rewrite using `[UnitAddTorus.mFourierCoeff_eq_integral f n 0, latticeFourierCoeff, covolume_eq_volume_latticeCell, latticeCell, average_fundamentalDomain_eq_cube]`. Simplify using `only [Pi.zero_apply, zero_add]`.

Use `integral_congr_ae (.of_forall fun x ↦ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _`. Simplify using `only [hchar, hfp]`. Use `congr 4`. Use `Eq.trans ?_ (congrArg Neg.neg (hφ n x).symm)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hsum` using `UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f) (by rw [funext hcoeff]; exact φ.summable_iff.2 hs) (p (b₀.equivFun y))`. Rewrite using `[← φ.hasSum_iff]`. Express the relevant statement in the definitionally equal form `HasSum _ (f₀ (p _)) at hsum`. Simplify using `only [hfp, hchar, hcoeff, ← hφ] at hsum`.

Simplify `hsum` using `only [b₀, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_comm, Function.comp_def]`.
-/
private theorem hasSum_latticeFourier_complex {A : E → ℂ} (hA : ∀ x ∈ L, Function.Periodic A x)
    (hc : Continuous A) (hs : Summable fun ν : L* ↦ latticeFourierCoeff L A ν) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by
  set b := Free.chooseBasis ℤ L
  set b₀ := b.ofZLatticeBasis ℝ L
  obtain ⟨-, -, φ, hφ⟩ := exists_equiv_innerDual L b
  set p : (Free.ChooseBasisIndex ℤ L → ℝ) → UnitAddTorus (Free.ChooseBasisIndex ℤ L) :=
    fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Free.ChooseBasisIndex ℤ L) → ℂ :=
    fun z ↦ A (b₀.equivFun.symm (Function.surjInv hq.surjective z)) with hf₀
  have hfp : ∀ x, f₀ (p x) = A (b₀.equivFun.symm x) := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : b₀.equivFun.symm (x' - x) ∈ L := by
      rw [Basis.equivFun_symm_apply]
      refine sum_mem fun i _ ↦ ?_
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      rw [Pi.sub_apply, ← hn, smul_assoc, one_smul]
      exact L.smul_mem n (by simp [b₀])
    rw [← hA _ h2 (b₀.equivFun.symm x), ← map_add, add_sub_cancel]
  let f : C(UnitAddTorus (Free.ChooseBasisIndex ℤ L), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A ∘ b₀.equivFunL.symm from funext hfp]; fun_prop⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier n (p x) = e[∑ i, n i * x i] := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = latticeFourierCoeff L A (φ n) := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0, latticeFourierCoeff,
      covolume_eq_volume_latticeCell, latticeCell, average_fundamentalDomain_eq_cube]
    simp only [Pi.zero_apply, zero_add]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp]
    congr 4
    refine Eq.trans ?_ (congrArg Neg.neg (hφ n x).symm)
    simp
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact φ.summable_iff.2 hs) (p (b₀.equivFun y))
  rw [← φ.hasSum_iff]
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hfp, hchar, hcoeff, ← hφ] at hsum
  simpa only [b₀, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_comm, Function.comp_def]
    using hsum

/- English proof (translation)
Establish `h1 : Summable fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν` using `.of_norm (by simpa only [norm_smul, norm_cexp_two_pi_I, one_mul] using hs)`. Use `h1.hasSum using 1` and compare the differences between its conclusion and the goal. Use `(SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun T ↦ ?_` and prove the remaining obligations. Establish `h2` using `hasSum_latticeFourier_complex (L := L) (A := fun b ↦ T (A b)) (fun x hx b ↦ by simp only [hA x hx b]) (by fun_prop) (by simpa only [latticeFourierCoeff_clm T hc, Function.comp_def] using hs.of_norm.map T T.continuous) y`. Simplify using `only [latticeFourierCoeff_clm T hc, ← map_smul] at h2`.

Conclude with `h2.unique (T.hasSum h1.hasSum)`.
-/
theorem hasSum_latticeFourier_of_summable_norm [CompleteSpace V] {A : E → V}
    (hA : ∀ x ∈ L, Function.Periodic A x) (hc : Continuous A)
    (hs : Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by
  have h1 : Summable fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν :=
    .of_norm (by simpa only [norm_smul, norm_cexp_two_pi_I, one_mul] using hs)
  convert h1.hasSum using 1
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun T ↦ ?_
  have h2 := hasSum_latticeFourier_complex (L := L) (A := fun b ↦ T (A b))
    (fun x hx b ↦ by simp only [hA x hx b]) (by fun_prop)
    (by simpa only [latticeFourierCoeff_clm T hc, Function.comp_def] using hs.of_norm.map T T.continuous) y
  simp only [latticeFourierCoeff_clm T hc, ← map_smul] at h2
  exact h2.unique (T.hasSum h1.hasSum)

/- English proof (translation)
Establish `: CompleteSpace V` using `FiniteDimensional.complete ℂ V`. Establish `: FiniteDimensional ℝ V` using `Module.Finite.trans ℂ V`. Conclude with `hasSum_latticeFourier_of_summable_norm hA hc (summable_norm_iff.2 hs) y`.
-/
theorem hasSum_latticeFourier_of_summable [FiniteDimensional ℂ V] {A : E → V}
    (hA : ∀ x ∈ L, Function.Periodic A x) (hc : Continuous A)
    (hs : Summable fun ν : L* ↦ latticeFourierCoeff L A ν) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  exact hasSum_latticeFourier_of_summable_norm hA hc (summable_norm_iff.2 hs) y

/- English proof (translation)
Establish `hs` using `summable_norm_latticeFourierCoeff hA (Nat.lt_succ_self _) (hsm.of_le (by exact_mod_cast le_top))`. Take `⟨M, hM⟩` from `exists_bound_of_lattice_periodic hA hsm.continuous`. Establish `hb : BddAbove (range fun b ↦ ‖A b‖)` using `⟨M, by rintro _ ⟨b, rfl⟩; exact hM b⟩`. Conclude with `⟨⟨hb, fun ν ↦ norm_latticeFourierCoeff_le (le_ciSup hb) ν⟩, hs, hasSum_latticeFourier_of_summable_norm hA hsm.continuous hs, fun c ν ↦ latticeFourierCoeff_comp_add hA ν.2 c⟩`.
-/
theorem latticeFourier_of_contDiff [CompleteSpace V] {A : E → V} (hsm : ContDiff ℝ ∞ A)
    (hA : ∀ x ∈ L, Function.Periodic A x) :
    (BddAbove (range fun b ↦ ‖A b‖) ∧ ∀ ν : L*, ‖latticeFourierCoeff L A ν‖ ≤ ⨆ b, ‖A b‖) ∧
    (Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) ∧
    (∀ b, HasSum (fun ν : L* ↦ e[⟪(ν : E), b⟫] • latticeFourierCoeff L A ν) (A b)) ∧
    ∀ (c : E) (ν : L*), latticeFourierCoeff L (fun b ↦ A (b + c)) ν =
      e[⟪(ν : E), c⟫] • latticeFourierCoeff L A ν := by
  have hs := summable_norm_latticeFourierCoeff hA (Nat.lt_succ_self _)
    (hsm.of_le (by exact_mod_cast le_top))
  obtain ⟨M, hM⟩ := exists_bound_of_lattice_periodic hA hsm.continuous
  have hb : BddAbove (range fun b ↦ ‖A b‖) := ⟨M, by rintro _ ⟨b, rfl⟩; exact hM b⟩
  exact ⟨⟨hb, fun ν ↦ norm_latticeFourierCoeff_le (le_ciSup hb) ν⟩, hs,
    hasSum_latticeFourier_of_summable_norm hA hsm.continuous hs,
    fun c ν ↦ latticeFourierCoeff_comp_add hA ν.2 c⟩

/- English proof (translation)
The claim follows from `have : CompleteSpace V := FiniteDimensional.complete ℂ V latticeFourier_of_contDiff hsm hA`.
-/
theorem latticeFourier_of_contDiff_finiteDimensional [FiniteDimensional ℂ V] {A : E → V}
    (hsm : ContDiff ℝ ∞ A) (hA : ∀ x ∈ L, Function.Periodic A x) :
    (BddAbove (range fun b ↦ ‖A b‖) ∧ ∀ ν : L*, ‖latticeFourierCoeff L A ν‖ ≤ ⨆ b, ‖A b‖) ∧
    (Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) ∧
    (∀ b, HasSum (fun ν : L* ↦ e[⟪(ν : E), b⟫] • latticeFourierCoeff L A ν) (A b)) ∧
    ∀ (c : E) (ν : L*), latticeFourierCoeff L (fun b ↦ A (b + c)) ν =
      e[⟪(ν : E), c⟫] • latticeFourierCoeff L A ν :=
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  latticeFourier_of_contDiff hsm hA

/- English proof (translation)
Use `hasSum_latticeFourier_of_summable_norm hA hc (by simp [h, summable_zero]) y` as an intermediate fact. Simplify using `only [h, smul_zero] at this`. Conclude with `this.unique hasSum_zero`.
-/
theorem eq_zero_of_latticeFourierCoeff_eq_zero [CompleteSpace V] {A : E → V}
    (hA : ∀ x ∈ L, Function.Periodic A x) (hc : Continuous A)
    (h : ∀ ν : L*, latticeFourierCoeff L A ν = 0) (y : E) : A y = 0 := by
  have := hasSum_latticeFourier_of_summable_norm hA hc (by simp [h, summable_zero]) y
  simp only [h, smul_zero] at this
  exact this.unique hasSum_zero

end GlobalTheory
