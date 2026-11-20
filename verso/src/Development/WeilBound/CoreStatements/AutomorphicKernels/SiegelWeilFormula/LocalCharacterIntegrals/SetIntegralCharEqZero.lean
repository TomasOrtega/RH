import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellNu

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

namespace Shell

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {v : HeightOneSpectrum (𝓞 F)} {σ : E →ₐ[F] E}

/- English proof (translation)
Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]`.
-/
theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k e => simp [sigR, sigma_sigma hcm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem sigR_sigR (hcm : IsCMExt F E σ) (a : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigR, sigma_sigma hcm]
  | add x y hx hy => simp only [map_add, hx, hy]

def sigE (hcm : IsCMExt F E σ) : (Fv F v ⊗[F] E) ≃ₐ[Fv F v] (Fv F v ⊗[F] E) :=
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ)
    (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ)
    (by ext <;> simp [sigma_sigma hcm]) (by ext <;> simp [sigma_sigma hcm])

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k e => simp [sigE, sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem sigE_apply (hcm : IsCMExt F E σ) (a : Fv F v ⊗[F] E) : sigE hcm a = sigR (Fv F v) σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigE, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite using `[← sigE_apply hcm, Algebra.trace_eq_of_algEquiv]`.
-/
theorem trace_sigR (hcm : IsCMExt F E σ) (a : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ a) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a := by
  rw [← sigE_apply hcm, Algebra.trace_eq_of_algEquiv]

variable (σ) in

def cs {p q : ℕ} (x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) : Matrix (Fin q) (Fin p) (Fv F v ⊗[F] E) :=
  (x.map (sigR (Fv F v) σ))ᵀ

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cs]`.
-/
theorem cs_add {p q : ℕ} (x y : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) : cs σ (x + y) = cs σ x + cs σ y := by
  ext i j; simp [cs]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cs, Matrix.mul_apply, mul_comm]`.
-/
theorem cs_mul {p q r : ℕ} (x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) (y : Matrix (Fin q) (Fin r) (Fv F v ⊗[F] E)) :
    cs σ (x * y) = cs σ y * cs σ x := by
  ext i j; simp [cs, Matrix.mul_apply, mul_comm]

/- English proof (translation)
Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [cs, Matrix.one_apply, h, eq_comm]`.
-/
theorem cs_one {p : ℕ} : cs σ (1 : Matrix (Fin p) (Fin p) (Fv F v ⊗[F] E)) = 1 := by
  ext i j; by_cases h : i = j <;> simp [cs, Matrix.one_apply, h, eq_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cs, sigR_sigR hcm]`.
-/
theorem cs_cs (hcm : IsCMExt F E σ) {p q : ℕ} (x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) : cs σ (cs σ x) = x := by
  ext i j; simp [cs, sigR_sigR hcm]

/- English proof (translation)
Use extensionality with `i j`. Conclude with `b.2 i j`.
-/
theorem cs_herm {n : ℕ} (b : HermR (Fv F v) σ n) : cs σ (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = b := by
  ext i j; exact b.2 i j

/- English proof (translation)
Simplify using `[cs, Matrix.trace, map_sum]`.
-/
theorem trace_cs {p : ℕ} (x : Matrix (Fin p) (Fin p) (Fv F v ⊗[F] E)) :
    Matrix.trace (cs σ x) = sigR (Fv F v) σ (Matrix.trace x) := by
  simp [cs, Matrix.trace, map_sum]

/- English proof (translation)
Unfold `trPair`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`.
-/
theorem trPair_eq {n : ℕ} (S T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    trPair (Fv F v) S T = algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Matrix.trace (S * T)) := by
  unfold trPair
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/- English proof (translation)
Simplify using `[trPair_eq, mul_add]`.
-/
theorem trPair_add_right {n : ℕ} (S T U : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    trPair (Fv F v) S (T + U) = trPair (Fv F v) S T + trPair (Fv F v) S U := by
  simp [trPair_eq, mul_add]

/- English proof (translation)
Establish `h1 : Matrix.trace (T.1 * (cs σ x * b.1)) = sigR (Fv F v) σ (Matrix.trace (T.1 * b.1 * x))`. Rewrite using `[← trace_cs, cs_mul, cs_mul, cs_herm, cs_herm, Matrix.trace_mul_comm, Matrix.mul_assoc]`. Rewrite using `[trPair_eq, Matrix.mul_add, Matrix.trace_add, map_add, h1, trace_sigR hcm, ← Matrix.mul_assoc, ← two_mul, ← mul_assoc]`. Establish `: algebraMap F (Fv F v) (1 / 2) * 2 = 1`. Rewrite using `[show (2 : Fv F v) = algebraMap F (Fv F v) 2 from (map_ofNat _ 2).symm, ← map_mul]`.

Evaluate the numerical expressions. Rewrite using `[this, one_mul]`.
-/
theorem trPair_lin (hcm : IsCMExt F E σ) {n : ℕ} (T b : HermR (Fv F v) σ n) (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    trPair (Fv F v) T.1 (cs σ x * b.1 + b.1 * x) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Matrix.trace (T.1 * b.1 * x)) := by
  have h1 : Matrix.trace (T.1 * (cs σ x * b.1)) = sigR (Fv F v) σ (Matrix.trace (T.1 * b.1 * x)) := by
    rw [← trace_cs, cs_mul, cs_mul, cs_herm, cs_herm, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [trPair_eq, Matrix.mul_add, Matrix.trace_add, map_add, h1, trace_sigR hcm, ← Matrix.mul_assoc, ← two_mul,
    ← mul_assoc]
  have : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
    rw [show (2 : Fv F v) = algebraMap F (Fv F v) 2 from (map_ofNat _ 2).symm, ← map_mul]; norm_num
  rw [this, one_mul]

/- English proof (translation)
Rewrite using `[cs_add, cs_one]`. Use `noncomm_ring`.
-/
theorem expand {n : ℕ} (b x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    cs σ (1 + x) * b * (1 + x) = b + (cs σ x * b + b * x) + cs σ x * b * x := by
  rw [cs_add, cs_one]; noncomm_ring

/- English proof (translation)
Establish `key : ∫ x in (U : Set V), χ x ∂m = χ x₀ * ∫ x in (U : Set V), χ x ∂m`. Rewrite using `[← integral_indicator hU]`. Use `conv_lhs => rw [← integral_add_left_eq_self _ x₀]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use extensionality with `x`. Distinguish the cases in `hx : x ∈ U`. Establish `: x₀ + x ∈ U` using `U.add_mem hx₀ hx`. Rewrite using `[Set.indicator_of_mem (show x₀ + x ∈ (U : Set V) from this), Set.indicator_of_mem (show x ∈ (U : Set V) from hx), hχ]`. Establish `: x₀ + x ∉ U` using `fun h => hx (by simpa using U.sub_mem h hx₀)`.

Rewrite using `[Set.indicator_of_notMem (show x₀ + x ∉ (U : Set V) from this), Set.indicator_of_notMem (show x ∉ (U : Set V) from hx), mul_zero]`. Establish `h1 : (1 - χ x₀) * ∫ x in (U : Set V), χ x ∂m = 0` using `by rw [sub_mul, one_mul, ← key, sub_self]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h).symm hne`. Conclude with `h`.
-/
theorem setIntegral_char_eq_zero {V : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (m : Measure V) [m.IsAddLeftInvariant] (U : AddSubgroup V) (hU : MeasurableSet (U : Set V))
    (χ : V → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) {x₀ : V} (hx₀ : x₀ ∈ U) (hne : χ x₀ ≠ 1) :
    ∫ x in (U : Set V), χ x ∂m = 0 := by
  have key : ∫ x in (U : Set V), χ x ∂m = χ x₀ * ∫ x in (U : Set V), χ x ∂m := by
    rw [← integral_indicator hU]
    conv_lhs => rw [← integral_add_left_eq_self _ x₀]
    rw [← integral_const_mul]
    congr 1; ext x
    by_cases hx : x ∈ U
    · have : x₀ + x ∈ U := U.add_mem hx₀ hx
      rw [Set.indicator_of_mem (show x₀ + x ∈ (U : Set V) from this), Set.indicator_of_mem (show x ∈ (U : Set V) from hx), hχ]
    · have : x₀ + x ∉ U := fun h => hx (by simpa using U.sub_mem h hx₀)
      rw [Set.indicator_of_notMem (show x₀ + x ∉ (U : Set V) from this), Set.indicator_of_notMem (show x ∉ (U : Set V) from hx), mul_zero]
  have h1 : (1 - χ x₀) * ∫ x in (U : Set V), χ x ∂m = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

/- English proof (translation)
Distinguish the cases in `hf : IntegrableOn f S ν`. Use `swap`. Conclude with `integral_undef hf`. Establish `hfin : IsFiniteMeasure (m.restrict U)` using `⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hUf⟩`. Establish `step1 : ∀ x ∈ U, ∫ b in S, f b ∂ν = ∫ b in S, f b * χ b x ∂ν`.

Introduce `x hx`. Rewrite using `[← hφ x hx]`. Conclude with `setIntegral_congr_fun hSm fun b hb => hfφ x hx b hb`. Establish `hint : Integrable (Function.uncurry fun (x : V) (b : H) => f b * χ b x) ((m.restrict U).prod (ν.restrict S))`. Establish `h1 : Integrable (fun p : V × H => (1 : ℂ) * f p.2) ((m.restrict U).prod (ν.restrict S))` using `(integrable_const (1 : ℂ)).mul_prod hf`.

Use `h1.mono ?_ ?_` and prove the remaining obligations. Use `(hf.aestronglyMeasurable.comp_snd).mul ?_` and prove the remaining obligations. Conclude with `hχc.aestronglyMeasurable`. Use `Filter.Eventually.of_forall fun p => ?_ show ‖f p.2 * χ p.2 p.1‖ ≤ ‖(1 : ℂ) * f p.2‖` and prove the remaining obligations. Rewrite using `[one_mul, norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hχ1 _ _)`. Establish `step2 : ∫ x in U, (∫ b in S, f b ∂ν) ∂m = ∫ x in U, (∫ b in S, f b * χ b x ∂ν) ∂m` using `setIntegral_congr_fun hUm fun x hx => step1 x hx`. Rewrite `step2` using `[integral_integral_swap hint]`. Establish `step3 : ∫ b in S, (∫ x in U, f b * χ b x ∂m) ∂ν = 0`. Establish `: ∀ b ∈ S, ∫ x in U, f b * χ b x ∂m = 0` using `fun b hb => by rw [integral_const_mul, hχ0 b hb, mul_zero]`.

Rewrite using `[setIntegral_congr_fun hSm this, integral_zero]`. Rewrite `step2` using `[step3, setIntegral_const, smul_eq_zero]`. Break down `step2 with h | h` into its components or cases. It suffices to derive a contradiction. Simplify using `[Measure.real, ENNReal.toReal_eq_zero_iff, hU0, hUf] at h`.

Conclude with `h`.
-/
theorem avg_zero {H V : Type*} [TopologicalSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] [SecondCountableTopology H]
    [SecondCountableTopology V]
    (ν : Measure H) (m : Measure V) [SFinite ν] [SFinite m] (U : Set V) (S : Set H) (f : H → ℂ) (χ : H → V → ℂ)
    (φ : V → H → H) (hU0 : m U ≠ 0) (hUf : m U ≠ ⊤)
    (hφ : ∀ x ∈ U, ∫ b in S, f (φ x b) ∂ν = ∫ b in S, f b ∂ν)
    (hfφ : ∀ x ∈ U, ∀ b ∈ S, f (φ x b) = f b * χ b x)
    (hχ0 : ∀ b ∈ S, ∫ x in U, χ b x ∂m = 0) (hχ1 : ∀ b x, ‖χ b x‖ ≤ 1)
    (hχc : Continuous fun p : V × H => χ p.2 p.1) (hSm : MeasurableSet S) (hUm : MeasurableSet U) :
    ∫ b in S, f b ∂ν = 0 := by
  by_cases hf : IntegrableOn f S ν
  swap
  · exact integral_undef hf
  have hfin : IsFiniteMeasure (m.restrict U) := ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hUf⟩

  have step1 : ∀ x ∈ U, ∫ b in S, f b ∂ν = ∫ b in S, f b * χ b x ∂ν := by
    intro x hx
    rw [← hφ x hx]
    exact setIntegral_congr_fun hSm fun b hb => hfφ x hx b hb

  have hint : Integrable (Function.uncurry fun (x : V) (b : H) => f b * χ b x) ((m.restrict U).prod (ν.restrict S)) := by
    have h1 : Integrable (fun p : V × H => (1 : ℂ) * f p.2) ((m.restrict U).prod (ν.restrict S)) :=
      (integrable_const (1 : ℂ)).mul_prod hf
    refine h1.mono ?_ ?_
    · refine (hf.aestronglyMeasurable.comp_snd).mul ?_
      exact hχc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      show ‖f p.2 * χ p.2 p.1‖ ≤ ‖(1 : ℂ) * f p.2‖
      rw [one_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hχ1 _ _)
  have step2 : ∫ x in U, (∫ b in S, f b ∂ν) ∂m = ∫ x in U, (∫ b in S, f b * χ b x ∂ν) ∂m :=
    setIntegral_congr_fun hUm fun x hx => step1 x hx
  rw [integral_integral_swap hint] at step2
  have step3 : ∫ b in S, (∫ x in U, f b * χ b x ∂m) ∂ν = 0 := by
    have : ∀ b ∈ S, ∫ x in U, f b * χ b x ∂m = 0 := fun b hb => by rw [integral_const_mul, hχ0 b hb, mul_zero]
    rw [setIntegral_congr_fun hSm this, integral_zero]
  rw [step3, setIntegral_const, smul_eq_zero] at step2
  rcases step2 with h | h
  · exfalso; simp [Measure.real, ENNReal.toReal_eq_zero_iff, hU0, hUf] at h
  · exact h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [nA_zero, hr]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(nA_add_le _ _).trans (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem nA_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i ∈ s, nA v (f i) ≤ r) : nA v (∑ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nA_zero, hr]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (nA_add_le _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
The claim follows from `nA_sum_le _ _ (nM_nonneg x) fun i _ => nA_le_nM x i i`.
-/
theorem nA_trace_le {p : ℕ} (x : Matrix (Fin p) (Fin p) (Fv F v ⊗[F] E)) : nA v (Matrix.trace x) ≤ nM v x :=
  nA_sum_le _ _ (nM_nonneg x) fun i _ => nA_le_nM x i i

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(nM_le_iff (nM_nonneg x)).2 fun i j => nA_le_nM x j i`. Conclude with `(nM_le_iff (nM_nonneg (v := v) xᵀ)).2 fun i j => nA_le_nM (v := v) xᵀ j i`.
-/
theorem nM_transpose {p q : ℕ} (x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) : nM v xᵀ = nM v x := by
  apply le_antisymm
  · exact (nM_le_iff (nM_nonneg x)).2 fun i j => nA_le_nM x j i
  · exact (nM_le_iff (nM_nonneg (v := v) xᵀ)).2 fun i j => nA_le_nM (v := v) xᵀ j i

variable (v) in
/- English proof (translation)
Take `⟨C, hC, h⟩` from `exists_nM_sig v σ p q`. Conclude with `⟨C, hC, fun x => by rw [cs, nM_transpose]; exact h x⟩`.
-/
theorem exists_nM_cs (σ : E →ₐ[F] E) (p q : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E),
    nM v (cs σ x) ≤ C * nM v x := by
  obtain ⟨C, hC, h⟩ := exists_nM_sig v σ p q
  exact ⟨C, hC, fun x => by rw [cs, nM_transpose]; exact h x⟩

/- English proof (translation)
Establish `hne : (Finset.univ : Finset (Fin p × Fin q)).Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff]`. Establish `: nM v x ≤ 0` using `(nM_le_iff le_rfl).2 fun i j => (h.false (i, j)).elim`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨⟨i, j⟩, -, hm⟩` from `Finset.exists_max_image Finset.univ (fun ij : Fin p × Fin q => nA v (x ij.1 ij.2)) hne`. Use `⟨i, j, le_antisymm (nA_le_nM x i j) ?_⟩` and prove the remaining obligations. Conclude with `(nM_le_iff (nA_nonneg _)).2 fun i' j' => hm (i', j') (Finset.mem_univ _)`.
-/
theorem exists_nM_eq {p q : ℕ} (x : Fin p → Fin q → Fv F v ⊗[F] E) (hx : 0 < nM v x) :
    ∃ i j, nA v (x i j) = nM v x := by
  classical
  have hne : (Finset.univ : Finset (Fin p × Fin q)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
    have : nM v x ≤ 0 := (nM_le_iff le_rfl).2 fun i j => (h.false (i, j)).elim
    linarith
  obtain ⟨⟨i, j⟩, -, hm⟩ := Finset.exists_max_image Finset.univ (fun ij : Fin p × Fin q => nA v (x ij.1 ij.2)) hne
  refine ⟨i, j, le_antisymm (nA_le_nM x i j) ?_⟩
  exact (nM_le_iff (nA_nonneg _)).2 fun i' j' => hm (i', j') (Finset.mem_univ _)

/- English proof (translation)
The claim follows from `nM_add_le x y`.
-/
theorem nMm_add_le {p q : ℕ} (x y : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) :
    nM v (x + y) ≤ max (nM v x) (nM v y) := nM_add_le x y

/- English proof (translation)
The claim follows from `nM_neg x`.
-/
theorem nMm_neg {p q : ℕ} (x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) : nM v (-x) = nM v x := nM_neg x

/- English proof (translation)
Establish `h3' : t3 ≤ Cm * (Cm * (Cs * a) * β) * a` using `h3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCm) ha)`. Establish `e1 : 0 ≤ Cm * Cs * a * β` using `by positivity`. Establish `e2 : 0 ≤ Cm * a * β` using `by positivity`. Establish `e3 : Cm * Cm * Cs * a * β * a ≤ Cm * Cm * Cs * a * β`. Establish `: 0 ≤ Cm * Cm * Cs * a * β` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Apply the tactic sequence `refine max_le (max_le ?_ ?_) ?_ <;> nlinarith`.
-/
theorem max_le_product_bound {Cm Cs a β t1 t2 t3 : ℝ} (hCm : 0 ≤ Cm) (hCs : 0 ≤ Cs) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ β) (h1 : t1 ≤ Cm * (Cs * a) * β) (h2 : t2 ≤ Cm * β * a) (h3 : t3 ≤ Cm * t1 * a) :
    max (max t1 t2) t3 ≤ (Cm * Cs + Cm + Cm * Cm * Cs) * a * β := by
  have h3' : t3 ≤ Cm * (Cm * (Cs * a) * β) * a := h3.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h1 hCm) ha)
  have e1 : 0 ≤ Cm * Cs * a * β := by positivity
  have e2 : 0 ≤ Cm * a * β := by positivity
  have e3 : Cm * Cm * Cs * a * β * a ≤ Cm * Cm * Cs * a * β := by
    have : 0 ≤ Cm * Cm * Cs * a * β := by positivity
    nlinarith
  refine max_le (max_le ?_ ?_) ?_ <;> nlinarith

variable (v) in
/- English proof (translation)
Take `⟨Cm, hCm, hm⟩` from `exists_nM_mul (E := E) v n n n`. Take `⟨Cs, hCs, hs⟩` from `exists_nM_cs v σ n n`. Use `⟨Cm * Cs + Cm + Cm * Cm * Cs, by positivity, fun x b hx => ?_⟩` and prove the remaining obligations. Establish `ha` using `nM_nonneg (v := v) x`. Establish `hb` using `nM_nonneg (v := v) b`.

Establish `h1 : nM v (cs σ x * b) ≤ Cm * (Cs * nM v x) * nM v b` using `(hm _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs x) hCm) hb)`. Establish `h2 : nM v (b * x) ≤ Cm * nM v b * nM v x` using `hm _ _`. Establish `h3 : nM v (cs σ x * b * x) ≤ Cm * nM v (cs σ x * b) * nM v x` using `hm _ _`. Establish `hmax` using `(nM_add_le (v := v) (cs σ x * b + b * x) (cs σ x * b * x)).trans (max_le_max ((nM_add_le (v := v) (cs σ x * b) (b * x))) le_rfl)`. Conclude with `hmax.trans (max_le_product_bound hCm hCs ha hx hb h1 h2 h3)`.
-/
theorem exists_nM_pert (σ : E →ₐ[F] E) (n : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    nM v x ≤ 1 → nM v ((cs σ x * b + b * x) + cs σ x * b * x) ≤ C * nM v x * nM v b := by
  obtain ⟨Cm, hCm, hm⟩ := exists_nM_mul (E := E) v n n n
  obtain ⟨Cs, hCs, hs⟩ := exists_nM_cs v σ n n
  refine ⟨Cm * Cs + Cm + Cm * Cm * Cs, by positivity, fun x b hx => ?_⟩
  have ha := nM_nonneg (v := v) x
  have hb := nM_nonneg (v := v) b
  have h1 : nM v (cs σ x * b) ≤ Cm * (Cs * nM v x) * nM v b :=
    (hm _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs x) hCm) hb)
  have h2 : nM v (b * x) ≤ Cm * nM v b * nM v x := hm _ _
  have h3 : nM v (cs σ x * b * x) ≤ Cm * nM v (cs σ x * b) * nM v x := hm _ _
  have hmax := (nM_add_le (v := v) (cs σ x * b + b * x) (cs σ x * b * x)).trans
    (max_le_max ((nM_add_le (v := v) (cs σ x * b) (b * x))) le_rfl)
  exact hmax.trans (max_le_product_bound hCm hCs ha hx hb h1 h2 h3)

/- English proof (translation)
Establish `h : C * r ≤ C * (1 / (2 * (C + 1)))` using `mul_le_mul_of_nonneg_left hr hC`. Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mul_le_half_of_small {C r : ℝ} (hC : 0 ≤ C) (hr : r ≤ 1 / (2 * (C + 1))) (_hr0 : 0 ≤ r) : C * r ≤ 1 / 2 := by
  have h : C * r ≤ C * (1 / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hr hC
  refine h.trans ?_
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

variable (v) in

/- English proof (translation)
Take `⟨C, hC, h⟩` from `exists_nM_pert v σ n`. Use `⟨min 1 (1 / (2 * (C + 1))), by positivity, fun x hx b => ?_⟩` and prove the remaining obligations. Establish `hx1 : nM v x ≤ 1` using `hx.trans (min_le_left _ _)`. Establish `hsm : C * nM v x ≤ 1 / 2` using `mul_le_half_of_small hC (hx.trans (min_le_right _ _)) (nM_nonneg x)`. Use `(congrArg (nM v) ((expand b x).trans (add_assoc _ _ _))).trans ?_` and prove the remaining obligations.

Break down `(nM_nonneg (v := v) b).lt_or_eq with hb | hb` into its components or cases. Apply `nM_add_eq_of_lt` to reduce the goal to its premises. Use `(h x b hx1).trans_lt ?_` and prove the remaining obligations. Establish `: C * nM v x * nM v b ≤ 1 / 2 * nM v b` using `mul_le_mul_of_nonneg_right hsm hb.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: b = 0` using `nM_eq_zero.1 hb.symm`. Substitute `this` using the available equality. Simplify using the standard rewrite rules.
-/
theorem exists_normPres (σ : E →ₐ[F] E) (n : ℕ) : ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    nM v x ≤ r → ∀ b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v (cs σ (1 + x) * b * (1 + x)) = nM v b := by
  obtain ⟨C, hC, h⟩ := exists_nM_pert v σ n
  refine ⟨min 1 (1 / (2 * (C + 1))), by positivity, fun x hx b => ?_⟩
  have hx1 : nM v x ≤ 1 := hx.trans (min_le_left _ _)
  have hsm : C * nM v x ≤ 1 / 2 := mul_le_half_of_small hC (hx.trans (min_le_right _ _)) (nM_nonneg x)
  refine (congrArg (nM v) ((expand b x).trans (add_assoc _ _ _))).trans ?_
  rcases (nM_nonneg (v := v) b).lt_or_eq with hb | hb
  · apply nM_add_eq_of_lt
    refine (h x b hx1).trans_lt ?_
    have : C * nM v x * nM v b ≤ 1 / 2 * nM v b := mul_le_mul_of_nonneg_right hsm hb.le
    linarith
  · have : b = 0 := nM_eq_zero.1 hb.symm
    subst this; simp

variable (v) in

/- English proof (translation)
Take `⟨r₀, hr₀, hdet⟩` from `exists_isUnit_det (E := E) v n`. Take `⟨Cm, hCm, hm⟩` from `exists_nM_mul (E := E) v n n n`. Use `⟨min r₀ (1 / (2 * (Cm + 1))), by positivity, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hu` using `hdet x (hx.trans (min_le_left _ _))`. Establish `hsm : Cm * nM v x ≤ 1 / 2` using `mul_le_half_of_small hCm (hx.trans (min_le_right _ _)) (nM_nonneg x)`.

Take `⟨x', hx'⟩ : ∃ x' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), x' = (1 + x)⁻¹ - 1` from `⟨_, rfl⟩`. Establish `h1 : (1 + x) * (1 + x') = 1` using `by rw [hx', add_sub_cancel, Matrix.mul_nonsing_inv _ hu]`. Establish `h1' : (1 + x') * (1 + x) = 1` using `by rw [hx', add_sub_cancel, Matrix.nonsing_inv_mul _ hu]`. Use `⟨x', h1, h1', ?_⟩` and prove the remaining obligations. Use `clear hx'`.

Establish `h3 : x' + (x + x * x') = 0`. Establish `h5` using `h1`. Simplify using `only [add_mul, one_mul, mul_add, mul_one] at h5`. Rewrite `h5` using `[add_assoc]`. Establish `h6` using `add_eq_left.1 h5`.

Rewrite using `[← h6]`. Normalize the expressions using the abelian group laws. Establish `h7 : x' = -(x + x * x')` using `eq_neg_of_add_eq_zero_left h3`. Establish `h4 : nM v x' = nM v (x + x * x')` using `by conv_lhs => rw [h7]`. Conclude with `nMm_neg _`.

Establish `e1 : nM v (x + x * x') ≤ max (nM v x) (nM v (x * x'))` using `nMm_add_le x (x * x')`. Establish `e2 : nM v (x * x') ≤ Cm * nM v x * nM v x'` using `hm x x'`. Establish `hle : nM v x' ≤ max (nM v x) (Cm * nM v x * nM v x')` using `h4.le.trans (e1.trans (max_le_max le_rfl e2))`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`.

Establish `hpos : 0 < nM v x'` using `lt_of_le_of_lt (nM_nonneg x) hlt`. Break down `le_max_iff.1 hle with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Cm * nM v x * nM v x' ≤ 1 / 2 * nM v x'` using `mul_le_mul_of_nonneg_right hsm hpos.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_inv (n : ℕ) : ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r →
    ∃ x' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), (1 + x) * (1 + x') = 1 ∧ (1 + x') * (1 + x) = 1 ∧
      nM v x' ≤ nM v x := by
  obtain ⟨r₀, hr₀, hdet⟩ := exists_isUnit_det (E := E) v n
  obtain ⟨Cm, hCm, hm⟩ := exists_nM_mul (E := E) v n n n
  refine ⟨min r₀ (1 / (2 * (Cm + 1))), by positivity, fun x hx => ?_⟩
  have hu := hdet x (hx.trans (min_le_left _ _))
  have hsm : Cm * nM v x ≤ 1 / 2 := mul_le_half_of_small hCm (hx.trans (min_le_right _ _)) (nM_nonneg x)
  obtain ⟨x', hx'⟩ : ∃ x' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), x' = (1 + x)⁻¹ - 1 := ⟨_, rfl⟩
  have h1 : (1 + x) * (1 + x') = 1 := by rw [hx', add_sub_cancel, Matrix.mul_nonsing_inv _ hu]
  have h1' : (1 + x') * (1 + x) = 1 := by rw [hx', add_sub_cancel, Matrix.nonsing_inv_mul _ hu]
  refine ⟨x', h1, h1', ?_⟩
  clear hx'
  have h3 : x' + (x + x * x') = 0 := by
    have h5 := h1
    simp only [add_mul, one_mul, mul_add, mul_one] at h5
    rw [add_assoc] at h5
    have h6 := add_eq_left.1 h5
    rw [← h6]; abel
  have h7 : x' = -(x + x * x') := eq_neg_of_add_eq_zero_left h3
  have h4 : nM v x' = nM v (x + x * x') := by
    conv_lhs => rw [h7]
    exact nMm_neg _
  have e1 : nM v (x + x * x') ≤ max (nM v x) (nM v (x * x')) := nMm_add_le x (x * x')
  have e2 : nM v (x * x') ≤ Cm * nM v x * nM v x' := hm x x'
  have hle : nM v x' ≤ max (nM v x) (Cm * nM v x * nM v x') :=
    h4.le.trans (e1.trans (max_le_max le_rfl e2))
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < nM v x' := lt_of_le_of_lt (nM_nonneg x) hlt
  rcases le_max_iff.1 hle with h | h
  · linarith
  · have : Cm * nM v x * nM v x' ≤ 1 / 2 * nM v x' := mul_le_mul_of_nonneg_right hsm hpos.le
    linarith

variable (v) in

/- English proof (translation)
Take `⟨Cm, hCm, hm⟩` from `exists_nM_mul (E := E) v n n n`. Take `⟨Cs, hCs, hs⟩` from `exists_nM_cs v σ n n`. Take `⟨Ct, hCt, ht⟩` from `exists_trace_le v (E := E)`. Establish `hc2 : 0 ≤ ‖algebraMap F (Fv F v) (1 / 2)‖` using `norm_nonneg _`. Establish `hT` using `nM_nonneg (v := v) T`.

Use `⟨‖algebraMap F (Fv F v) (1 / 2)‖ * Ct * Cm * nM v T * (Cm * Cm * Cs), mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc2 hCt) hCm) hT) (by positivity), fun x b => ?_⟩` and prove the remaining obligations. Establish `ha` using `nM_nonneg (v := v) x`. Establish `hb` using `nM_nonneg (v := v) b`. Establish `q1 : nM v (cs σ x * b) ≤ Cm * (Cs * nM v x) * nM v b` using `(hm _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs x) hCm) hb)`. Establish `q2 : nM v (cs σ x * b * x) ≤ Cm * (Cm * (Cs * nM v x) * nM v b) * nM v x` using `(hm _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left q1 hCm) ha)`.

Establish `e1` using `ht (Matrix.trace (T * (cs σ x * b * x)))`. Establish `e2` using `nA_trace_le (v := v) (T * (cs σ x * b * x))`. Establish `e3` using `hm T (cs σ x * b * x)`. Rewrite using `[trPair_eq, norm_mul]`. Generalize the expression as in `‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Matrix.trace (T * (cs σ x * b * x)))‖ = tt at *`.

Generalize the expression as in `nA v (Matrix.trace (T * (cs σ x * b * x))) = ta at *`. Generalize the expression as in `nM v (T * (cs σ x * b * x)) = tm at *`. Generalize the expression as in `nM v (cs σ x * b * x) = tq at *`. Generalize the expression as in `nM v (cs σ x * b) = tb at *`. Generalize the expression as in `nM v x = a at *`.

Generalize the expression as in `nM v b = β at *`. Generalize the expression as in `nM v T = τ at *`. Generalize the expression as in `‖algebraMap F (Fv F v) (1 / 2)‖ = c2 at *`. Establish `k1 : tt ≤ Ct * (Cm * τ * tq)` using `e1.trans (mul_le_mul_of_nonneg_left (e2.trans e3) hCt)`. Establish `k2 : Cm * τ * tq ≤ Cm * τ * (Cm * (Cm * (Cs * a) * β) * a)` using `mul_le_mul_of_nonneg_left q2 (by positivity)`.

Establish `k3 : tt ≤ Ct * (Cm * τ * (Cm * (Cm * (Cs * a) * β) * a))` using `k1.trans (mul_le_mul_of_nonneg_left k2 hCt)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_quad (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    ∃ C, 0 ≤ C ∧ ∀ x b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      ‖trPair (Fv F v) T (cs σ x * b * x)‖ ≤ C * nM v x ^ 2 * nM v b := by
  obtain ⟨Cm, hCm, hm⟩ := exists_nM_mul (E := E) v n n n
  obtain ⟨Cs, hCs, hs⟩ := exists_nM_cs v σ n n
  obtain ⟨Ct, hCt, ht⟩ := exists_trace_le v (E := E)
  have hc2 : 0 ≤ ‖algebraMap F (Fv F v) (1 / 2)‖ := norm_nonneg _
  have hT := nM_nonneg (v := v) T
  refine ⟨‖algebraMap F (Fv F v) (1 / 2)‖ * Ct * Cm * nM v T * (Cm * Cm * Cs),
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc2 hCt) hCm) hT) (by positivity), fun x b => ?_⟩
  have ha := nM_nonneg (v := v) x
  have hb := nM_nonneg (v := v) b
  have q1 : nM v (cs σ x * b) ≤ Cm * (Cs * nM v x) * nM v b :=
    (hm _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs x) hCm) hb)
  have q2 : nM v (cs σ x * b * x) ≤ Cm * (Cm * (Cs * nM v x) * nM v b) * nM v x :=
    (hm _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left q1 hCm) ha)
  have e1 := ht (Matrix.trace (T * (cs σ x * b * x)))
  have e2 := nA_trace_le (v := v) (T * (cs σ x * b * x))
  have e3 := hm T (cs σ x * b * x)
  rw [trPair_eq, norm_mul]
  generalize ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Matrix.trace (T * (cs σ x * b * x)))‖ = tt at *
  generalize nA v (Matrix.trace (T * (cs σ x * b * x))) = ta at *
  generalize nM v (T * (cs σ x * b * x)) = tm at *
  generalize nM v (cs σ x * b * x) = tq at *
  generalize nM v (cs σ x * b) = tb at *
  generalize nM v x = a at *
  generalize nM v b = β at *
  generalize nM v T = τ at *
  generalize ‖algebraMap F (Fv F v) (1 / 2)‖ = c2 at *
  have k1 : tt ≤ Ct * (Cm * τ * tq) := e1.trans (mul_le_mul_of_nonneg_left (e2.trans e3) hCt)
  have k2 : Cm * τ * tq ≤ Cm * τ * (Cm * (Cm * (Cs * a) * β) * a) := mul_le_mul_of_nonneg_left q2 (by positivity)
  have k3 : tt ≤ Ct * (Cm * τ * (Cm * (Cm * (Cs * a) * β) * a)) := k1.trans (mul_le_mul_of_nonneg_left k2 hCt)
  calc c2 * tt ≤ c2 * (Ct * (Cm * τ * (Cm * (Cm * (Cs * a) * β) * a))) := mul_le_mul_of_nonneg_left k3 hc2
    _ = c2 * Ct * Cm * τ * (Cm * Cm * Cs) * a ^ 2 * β := by ring

/- English proof (translation)
Use `(nM_le_iff (nA_nonneg w)).2 fun i' j' => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = i' ∧ j = j'`. Rewrite using `[Matrix.single_apply, if_pos h]`. Rewrite using `[Matrix.single_apply, if_neg h, nA_zero]`. Conclude with `nA_nonneg w`.
-/
theorem nM_single_le {p q : ℕ} (i : Fin p) (j : Fin q) (w : Fv F v ⊗[F] E) :
    nM v (Matrix.single i j w) ≤ nA v w := by
  refine (nM_le_iff (nA_nonneg w)).2 fun i' j' => ?_
  by_cases h : i = i' ∧ j = j'
  · rw [Matrix.single_apply, if_pos h]
  · rw [Matrix.single_apply, if_neg h, nA_zero]; exact nA_nonneg w

variable (v) in

/- English proof (translation)
Take `⟨y₀, hy₀⟩` from `exists_psiV_ne_one (v := v) hcm hψ`. Take `⟨c, hc, htr⟩` from `exists_trace_ge (E := E) v`. Take `⟨Cm, hCm, hm⟩` from `exists_nM_mul (E := E) v n n n`. Take `⟨Ti, hTi'⟩ : ∃ Ti : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), Ti * T = 1` from `⟨T⁻¹, Matrix.nonsing_inv_mul _ hT⟩`. Establish `hy0 : y₀ ≠ 0` using `by rintro rfl; exact hy₀ (psiV_zero ψ)`.

Establish `hny0 : 0 < ‖y₀‖` using `norm_pos_iff.2 hy0`. Establish `hTi` using `nM_nonneg (v := v) Ti`. Establish `hCT : 0 < Cm * nM v Ti + 1` using `by have := mul_nonneg hCm hTi; linarith`. Establish `hC0 : 0 < ‖y₀‖ * (Cm * nM v Ti + 1) / c` using `div_pos (mul_pos hny0 hCT) hc`. Use `⟨‖y₀‖ * (Cm * nM v Ti + 1) / c, hC0, fun b hb r hr => ?_⟩` and prove the remaining obligations.

Take `⟨Y, hY⟩ : ∃ Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), T * b = Y` from `⟨_, rfl⟩`. Establish `hTb0` using `nM_nonneg (v := v) Y`. Establish `hTb : nM v b ≤ (Cm * nM v Ti + 1) * nM v Y`. Establish `e : Ti * Y = b` using `by rw [← hY, ← Matrix.mul_assoc, hTi', Matrix.one_mul]`. Establish `h1 : nM v (Ti * Y) ≤ Cm * nM v Ti * nM v Y` using `hm _ _`.

Rewrite `h1` using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpos : 0 < nM v Y`. Assume the negation of the conclusion as `h`. Establish `h0 : nM v Y = 0` using `le_antisymm (not_lt.1 h) hTb0`.

Rewrite `hTb` using `[h0, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hY]`. Take `⟨i, j, hij⟩` from `exists_nM_eq Y hpos`. Take `⟨a', ha', hge⟩` from `htr (Y i j)`.

Rewrite `hge` using `[hij]`. Establish `hτpos : 0 < ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * Y i j)‖` using `lt_of_lt_of_le (mul_pos hc hpos) hge`. Establish `hτ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * Y i j) ≠ 0` using `norm_pos_iff.1 hτpos`. Take `⟨τ, hτdef⟩ : ∃ τ, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * Y i j) = τ` from `⟨_, rfl⟩`. Rewrite `hτpos`, `hτ`, `hge` using `[hτdef]`.

Use `⟨Matrix.single j i ((-y₀ / τ) • a'), ?_, ?_⟩` and prove the remaining obligations. Use `(nM_single_le j i _).trans ?_` and prove the remaining obligations. Rewrite using `[nA_smul, norm_div, norm_neg]`. Establish `h1 : ‖y₀‖ / ‖τ‖ * nA v a' ≤ ‖y₀‖ / ‖τ‖` using `mul_le_of_le_one_right (div_nonneg hny0.le hτpos.le) ha'`. Use `h1.trans ?_` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ hτpos]`. Establish `k2 : ‖y₀‖ * (Cm * nM v Ti + 1) ≤ r * nM v b * c`. Rewrite `hr` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr0 : 0 ≤ r`.

Assume the negation of the conclusion as `h`. Establish `: r * nM v b < 0` using `mul_neg_of_neg_of_pos (not_le.1 h) hb`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `k3 : r * nM v b * c ≤ r * ((Cm * nM v Ti + 1) * nM v Y) * c` using `by gcongr`. Establish `k4 : ‖y₀‖ ≤ r * nM v Y * c`.

Establish `: ‖y₀‖ * (Cm * nM v Ti + 1) ≤ (r * nM v Y * c) * (Cm * nM v Ti + 1)` using `by nlinarith`. Conclude with `le_of_mul_le_mul_right this hCT`. Combine the equalities or inequalities in the displayed calculation. Establish `htrace : Matrix.trace (Y * Matrix.single j i ((-y₀ / τ) • a')) = Y i j * ((-y₀ / τ) • a')`. Rewrite using `[Matrix.trace_mul_single]`.

Simplify using `[mul_comm]`. Rewrite using `[htrace, mul_smul_comm, map_smul, mul_comm (Y i j) a', hτdef, smul_eq_mul, div_mul_cancel₀ _ hτ, neg_neg]`. Conclude with `hy₀`.
-/
theorem exists_nontriv (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (hT : IsUnit T.det) :
    ∃ C > 0, ∀ b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), 0 < nM v b → ∀ r : ℝ, C ≤ r * nM v b →
      ∃ x₀ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x₀ ≤ r ∧
        psiV F ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Matrix.trace (T * b * x₀))) ≠ 1 := by
  obtain ⟨y₀, hy₀⟩ := exists_psiV_ne_one (v := v) hcm hψ
  obtain ⟨c, hc, htr⟩ := exists_trace_ge (E := E) v
  obtain ⟨Cm, hCm, hm⟩ := exists_nM_mul (E := E) v n n n
  obtain ⟨Ti, hTi'⟩ : ∃ Ti : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), Ti * T = 1 := ⟨T⁻¹, Matrix.nonsing_inv_mul _ hT⟩
  have hy0 : y₀ ≠ 0 := by rintro rfl; exact hy₀ (psiV_zero ψ)
  have hny0 : 0 < ‖y₀‖ := norm_pos_iff.2 hy0
  have hTi := nM_nonneg (v := v) Ti
  have hCT : 0 < Cm * nM v Ti + 1 := by have := mul_nonneg hCm hTi; linarith
  have hC0 : 0 < ‖y₀‖ * (Cm * nM v Ti + 1) / c := div_pos (mul_pos hny0 hCT) hc
  refine ⟨‖y₀‖ * (Cm * nM v Ti + 1) / c, hC0, fun b hb r hr => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), T * b = Y := ⟨_, rfl⟩
  have hTb0 := nM_nonneg (v := v) Y
  have hTb : nM v b ≤ (Cm * nM v Ti + 1) * nM v Y := by
    have e : Ti * Y = b := by rw [← hY, ← Matrix.mul_assoc, hTi', Matrix.one_mul]
    have h1 : nM v (Ti * Y) ≤ Cm * nM v Ti * nM v Y := hm _ _
    rw [e] at h1
    nlinarith
  have hpos : 0 < nM v Y := by
    by_contra h
    have h0 : nM v Y = 0 := le_antisymm (not_lt.1 h) hTb0
    rw [h0, mul_zero] at hTb
    linarith
  rw [hY]
  obtain ⟨i, j, hij⟩ := exists_nM_eq Y hpos
  obtain ⟨a', ha', hge⟩ := htr (Y i j)
  rw [hij] at hge
  have hτpos : 0 < ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * Y i j)‖ :=
    lt_of_lt_of_le (mul_pos hc hpos) hge
  have hτ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * Y i j) ≠ 0 := norm_pos_iff.1 hτpos
  obtain ⟨τ, hτdef⟩ : ∃ τ, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * Y i j) = τ := ⟨_, rfl⟩
  rw [hτdef] at hτpos hτ hge
  refine ⟨Matrix.single j i ((-y₀ / τ) • a'), ?_, ?_⟩
  · refine (nM_single_le j i _).trans ?_
    rw [nA_smul, norm_div, norm_neg]
    have h1 : ‖y₀‖ / ‖τ‖ * nA v a' ≤ ‖y₀‖ / ‖τ‖ := mul_le_of_le_one_right (div_nonneg hny0.le hτpos.le) ha'
    refine h1.trans ?_
    rw [div_le_iff₀ hτpos]
    have k2 : ‖y₀‖ * (Cm * nM v Ti + 1) ≤ r * nM v b * c := by
      rw [div_le_iff₀ hc] at hr; linarith
    have hr0 : 0 ≤ r := by
      by_contra h
      have : r * nM v b < 0 := mul_neg_of_neg_of_pos (not_le.1 h) hb
      linarith
    have k3 : r * nM v b * c ≤ r * ((Cm * nM v Ti + 1) * nM v Y) * c := by gcongr
    have k4 : ‖y₀‖ ≤ r * nM v Y * c := by
      have : ‖y₀‖ * (Cm * nM v Ti + 1) ≤ (r * nM v Y * c) * (Cm * nM v Ti + 1) := by nlinarith
      exact le_of_mul_le_mul_right this hCT
    calc ‖y₀‖ ≤ r * (c * nM v Y) := by linarith
      _ ≤ r * ‖τ‖ := mul_le_mul_of_nonneg_left hge hr0
  · have htrace : Matrix.trace (Y * Matrix.single j i ((-y₀ / τ) • a')) = Y i j * ((-y₀ / τ) • a') := by
      rw [Matrix.trace_mul_single]; simp [mul_comm]
    rw [htrace, mul_smul_comm, map_smul, mul_comm (Y i j) a', hτdef, smul_eq_mul,
      div_mul_cancel₀ _ hτ, neg_neg]
    exact hy₀

instance secondCountable_Mat (n : ℕ) : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))

instance t2Space_local_matrix (n : ℕ) : T2Space (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
  inferInstanceAs (T2Space (Fin n → Fin n → Fv F v ⊗[F] E))

instance secondCountable_Herm (n : ℕ) : SecondCountableTopology (HermR (Fv F v) σ n) :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable (σ) in

def conjM {n : ℕ} (a b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  cs σ a * b * a

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a b`. Conclude with `h a b`. Introduce `h a b`.

Conclude with `congrFun (congrFun h a) b`.
-/
theorem mem_herm_iff {n : ℕ} (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : S ∈ HermR (Fv F v) σ n ↔ cs σ S = S := by
  constructor
  · intro h; ext a b; exact h a b
  · intro h a b; exact congrFun (congrFun h a) b

/- English proof (translation)
Rewrite using `[mem_herm_iff, conjM, cs_mul, cs_mul, cs_cs hcm, cs_herm, Matrix.mul_assoc]`.
-/
theorem conj_mem (hcm : IsCMExt F E σ) {n : ℕ} (a : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (b : HermR (Fv F v) σ n) :
    conjM σ a b.1 ∈ HermR (Fv F v) σ n := by
  rw [mem_herm_iff, conjM, cs_mul, cs_mul, cs_cs hcm, cs_herm, Matrix.mul_assoc]

/- English proof (translation)
Unfold `conjM`. Rewrite using `[show cs σ a' * (cs σ a * b * a) * a' = (cs σ a' * cs σ a) * b * (a * a') by`. Simplify using `only [Matrix.mul_assoc], ← cs_mul, h, cs_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem conjM_conjM {n : ℕ} (a a' b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (h : a * a' = 1) :
    conjM σ a' (conjM σ a b) = b := by
  unfold conjM
  rw [show cs σ a' * (cs σ a * b * a) * a' = (cs σ a' * cs σ a) * b * (a * a') by
    simp only [Matrix.mul_assoc], ← cs_mul, h, cs_one, Matrix.one_mul, Matrix.mul_one]

def conjE (hcm : IsCMExt F E σ) {n : ℕ} (a a' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (h1 : a * a' = 1)
    (h2 : a' * a = 1) : HermR (Fv F v) σ n ≃+ HermR (Fv F v) σ n where
  toFun b := ⟨conjM σ a b.1, conj_mem hcm a b⟩
  invFun b := ⟨conjM σ a' b.1, conj_mem hcm a' b⟩
  left_inv b := Subtype.ext (conjM_conjM a a' b.1 h1)
  right_inv b := Subtype.ext (conjM_conjM a' a b.1 h2)
  map_add' b c := by
    apply Subtype.ext
    simp [conjM, Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
The claim follows from `(continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const`.
-/
theorem continuous_conj {n : ℕ} (a : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    Continuous fun b : HermR (Fv F v) σ n => conjM σ a b.1 :=
  (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

/- English proof (translation)
The claim follows from `(continuous_conj a).subtype_mk _`.
-/
theorem continuous_conjE (hcm : IsCMExt F E σ) {n : ℕ} (a a' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (h1 : a * a' = 1) (h2 : a' * a = 1) : Continuous (conjE hcm a a' h1 h2) :=
  (continuous_conj a).subtype_mk _

/- English proof (translation)
The claim follows from `(continuous_conj a').subtype_mk _`.
-/
theorem continuous_conjE_symm (hcm : IsCMExt F E σ) {n : ℕ} (a a' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (h1 : a * a' = 1) (h2 : a' * a = 1) : Continuous (conjE hcm a a' h1 h2).symm :=
  (continuous_conj a').subtype_mk _

/- English proof (translation)
The claim follows from `(isClosed_hermSet v σ n).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_ballM r)`.
-/
theorem isCompact_ballH (n : ℕ) (r : ℝ) : IsCompact {b : HermR (Fv F v) σ n | nM v b.1 ≤ r} :=
  (isClosed_hermSet v σ n).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_ballM r)

/- English proof (translation)
The claim follows from `IsOpen.preimage continuous_subtype_val (isOpen_ballM hr : IsOpen {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | nM v x ≤ r})`.
-/
theorem isOpen_ballH (n : ℕ) {r : ℝ} (hr : 0 < r) : IsOpen {b : HermR (Fv F v) σ n | nM v b.1 ≤ r} :=
  IsOpen.preimage continuous_subtype_val
    (isOpen_ballM hr : IsOpen {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | nM v x ≤ r})

/- English proof (translation)
Rewrite using `[← integral_indicator hSm, ← integral_indicator hSm]`. Establish `hmem : ∀ b, e b ∈ S ↔ b ∈ S` using `fun b => by`. Rewrite using `[← Set.mem_preimage, hS]`. Establish `: S.indicator (fun b => f (e b)) = (S.indicator f) ∘ e`. Use function extensionality and compare the values at `b`.

Distinguish the cases in `hb : b ∈ S`. Rewrite using `[Set.indicator_of_mem hb, Function.comp_apply, Set.indicator_of_mem ((hmem b).2 hb)]`. Rewrite using `[Set.indicator_of_notMem hb, Function.comp_apply, Set.indicator_of_notMem (fun h => hb ((hmem b).1 h))]`. Rewrite using `[this]`. Conclude with `he.integral_comp' (S.indicator f)`.
-/
theorem setIntegral_comp_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (e : G ≃ᵐ G)
    (he : MeasurePreserving e μ μ) (S : Set G) (hSm : MeasurableSet S) (hS : e ⁻¹' S = S) (f : G → ℂ) :
    ∫ b in S, f (e b) ∂μ = ∫ b in S, f b ∂μ := by
  rw [← integral_indicator hSm, ← integral_indicator hSm]
  have hmem : ∀ b, e b ∈ S ↔ b ∈ S := fun b => by
    rw [← Set.mem_preimage, hS]
  have : S.indicator (fun b => f (e b)) = (S.indicator f) ∘ e := by
    funext b
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb, Function.comp_apply, Set.indicator_of_mem ((hmem b).2 hb)]
    · rw [Set.indicator_of_notMem hb, Function.comp_apply, Set.indicator_of_notMem (fun h => hb ((hmem b).1 h))]
  rw [this]
  exact he.integral_comp' (S.indicator f)

/- English proof (translation)
Use `set e := conjE hcm (1 + x) (1 + x') h1 h2`. Establish `hc` using `continuous_conjE hcm (1 + x) (1 + x') h1 h2`. Establish `hc'` using `continuous_conjE_symm hcm (1 + x) (1 + x') h1 h2`. Set `eh : HermR (Fv F v) σ n ≃ₜ HermR (Fv F v) σ n` to `{ toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }`. Establish `hn : ∀ b : HermR (Fv F v) σ n, nM v (e b).1 = nM v b.1` using `fun b => hpres b.1`.

Establish `hB : e ⁻¹' {b : HermR (Fv F v) σ n | nM v b.1 ≤ 1} = {b | nM v b.1 ≤ 1}`. Use extensionality with `b`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`. Rewrite using `[hn]`. Establish `hmp : MeasurePreserving e νv νv` using `measurePreserving_of_addEquiv νv e hc hc' _ (isCompact_ballH n 1) (by rw [(isOpen_ballH n one_pos).interior_eq]; exact ⟨0, (le_of_eq nM_zero).trans zero_le_one⟩) hB`.

Establish `hS : e ⁻¹' {b : HermR (Fv F v) σ n | P (nM v b.1)} = {b | P (nM v b.1)}`. Use extensionality with `b`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`. Rewrite using `[hn]`. Conclude with `setIntegral_comp_eq νv eh.toMeasurableEquiv hmp _ hSm hS f`.
-/
theorem setIntegral_conj (hcm : IsCMExt F E σ) {n : ℕ} (νv : Measure (HermR (Fv F v) σ n)) [νv.IsAddHaarMeasure]
    (x x' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (h1 : (1 + x) * (1 + x') = 1) (h2 : (1 + x') * (1 + x) = 1)
    (hpres : ∀ b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v (conjM σ (1 + x) b) = nM v b)
    (P : ℝ → Prop) (hSm : MeasurableSet {b : HermR (Fv F v) σ n | P (nM v b.1)}) (f : HermR (Fv F v) σ n → ℂ) :
    ∫ b in {b : HermR (Fv F v) σ n | P (nM v b.1)}, f (conjE hcm (1 + x) (1 + x') h1 h2 b) ∂νv =
      ∫ b in {b : HermR (Fv F v) σ n | P (nM v b.1)}, f b ∂νv := by
  set e := conjE hcm (1 + x) (1 + x') h1 h2
  have hc := continuous_conjE hcm (1 + x) (1 + x') h1 h2
  have hc' := continuous_conjE_symm hcm (1 + x) (1 + x') h1 h2
  let eh : HermR (Fv F v) σ n ≃ₜ HermR (Fv F v) σ n :=
    { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hn : ∀ b : HermR (Fv F v) σ n, nM v (e b).1 = nM v b.1 := fun b => hpres b.1
  have hB : e ⁻¹' {b : HermR (Fv F v) σ n | nM v b.1 ≤ 1} = {b | nM v b.1 ≤ 1} := by
    ext b; simp only [Set.mem_preimage, Set.mem_setOf_eq]; rw [hn]
  have hmp : MeasurePreserving e νv νv := measurePreserving_of_addEquiv νv e hc hc' _ (isCompact_ballH n 1)
    (by rw [(isOpen_ballH n one_pos).interior_eq]; exact ⟨0, (le_of_eq nM_zero).trans zero_le_one⟩) hB
  have hS : e ⁻¹' {b : HermR (Fv F v) σ n | P (nM v b.1)} = {b | P (nM v b.1)} := by
    ext b; simp only [Set.mem_preimage, Set.mem_setOf_eq]; rw [hn]
  exact setIntegral_comp_eq νv eh.toMeasurableEquiv hmp _ hSm hS f

instance measMat (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → Fv F v ⊗[F] E))

instance borelMat (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → Fv F v ⊗[F] E))

instance locallyCompactMat (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))

def ballSub (n : ℕ) (r : ℝ) (hr : 0 ≤ r) : AddSubgroup (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) where
  carrier := {x | nM v x ≤ r}
  zero_mem' := (le_of_eq nM_zero).trans hr
  add_mem' {x y} hx hy := (nMm_add_le x y).trans (max_le hx hy)
  neg_mem' {x} hx := by simpa [Set.mem_setOf_eq, nMm_neg] using hx

def chi (ψ : AddChar (AF F) ℂ) {n : ℕ} (T b : HermR (Fv F v) σ n) (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : ℂ :=
  psiV F ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Matrix.trace (T.1 * b.1 * x)))

/- English proof (translation)
Simplify using `only [chi, Matrix.mul_add, Matrix.trace_add, map_add, neg_add]`. Conclude with `psiV_add ψ _ _`.
-/
theorem chi_add (ψ : AddChar (AF F) ℂ) {n : ℕ} (T b : HermR (Fv F v) σ n) (x y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    chi ψ T b (x + y) = chi ψ T b x * chi ψ T b y := by
  simp only [chi, Matrix.mul_add, Matrix.trace_add, map_add, neg_add]
  exact psiV_add ψ _ _

/- English proof (translation)
Establish `htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))` using `IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))`. Use `(continuous_psiV hψ).comp (htr.comp ?_).neg` and prove the remaining obligations. Conclude with `((continuous_const.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul continuous_fst).matrix_trace`.
-/
theorem continuous_chi {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {n : ℕ} (T : HermR (Fv F v) σ n) :
    Continuous fun p : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) × HermR (Fv F v) σ n => chi ψ T p.2 p.1 := by
  have htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))
  refine (continuous_psiV hψ).comp (htr.comp ?_).neg
  exact ((continuous_const.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul continuous_fst).matrix_trace

/- English proof (translation)
Rewrite using `[conjM, expand, trPair_add_right, trPair_add_right, trPair_lin hcm]`.
-/
theorem trPair_conj (hcm : IsCMExt F E σ) {n : ℕ} (T b : HermR (Fv F v) σ n) (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    trPair (Fv F v) T.1 (conjM σ (1 + x) b.1) = trPair (Fv F v) T.1 b.1 +
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Matrix.trace (T.1 * b.1 * x)) + trPair (Fv F v) T.1 (cs σ x * b.1 * x) := by
  rw [conjM, expand, trPair_add_right, trPair_add_right, trPair_lin hcm]

/- English proof (translation)
Use `haveI : νv.IsAddHaarMeasure := h.sdH.1`. Use `haveI : μv.IsAddHaarMeasure := h.sdW.1`. Use `haveI : lam.IsAddHaarMeasure := h.haar`. Take `⟨r1, hr1, hpres⟩` from `exists_normPres v σ n`. Take `⟨r2, hr2, hinv⟩` from `exists_inv (E := E) v n`.

Take `⟨r3, hr3, hJ⟩` from `jtR_conj_inv v σ h.cm J (psiV F ψ v) μv Φv h.sb`. Take `⟨r4, hr4, hnu⟩` from `lattice_norm_conj_invariant v σ h.cm lam L₁ L₂ h.co₁ h.co₂`. Take `⟨Cq, hCq, hquad⟩` from `exists_quad v σ T.1`. Take `⟨Cν, hCν, hnt⟩` from `exists_nontriv v σ h.cm h.chr T.1 h.unit`. Take `⟨ε, hε, hsmall⟩` from `exists_psiV_small (v := v) h.chr`.

Use `set r0 := min (min r1 r2) (min r3 r4) with hr0def`. Establish `hr0 : 0 < r0` using `lt_min (lt_min hr1 hr2) (lt_min hr3 hr4)`. Use `⟨max (max (Cν / r0) (Cq * Cν ^ 2 * q / ε)) 1, fun R hR z => ?_⟩` and prove the remaining obligations. Establish `hR1 : 1 ≤ R` using `(le_max_right _ _).trans hR`. Establish `hRpos : 0 < R` using `lt_of_lt_of_le one_pos hR1`.

Establish `hRa : Cν / r0 ≤ R` using `(le_max_left _ _).trans ((le_max_left _ _).trans hR)`. Establish `hRb : Cq * Cν ^ 2 * q / ε ≤ R` using `(le_max_right _ _).trans ((le_max_left _ _).trans hR)`. Use `set r := Cν / R with hrdef`. Establish `hrpos : 0 < r` using `div_pos hCν hRpos`. Establish `hrr0 : r ≤ r0` using `by rw [hrdef, div_le_iff₀ hRpos, mul_comm]; rwa [div_le_iff₀ hr0] at hRa`.

Establish `hrle : ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → nM v x ≤ r1 ∧ nM v x ≤ r2 ∧ nM v x ≤ r3 ∧ nM v x ≤ r4` using `fun x hx => ⟨hx.trans (hrr0.trans ((min_le_left _ _).trans (min_le_left _ _))), hx.trans (hrr0.trans ((min_le_left _ _).trans (min_le_right _ _))), hx.trans (hrr0.trans ((min_le_right _ _).trans (min_le_left _ _))), hx.trans (hrr0.trans ((min_le_right _ _).trans (min_le_right _ _ …`. Set `x' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `fun x => if hx : nM v x ≤ r then Classical.choose (hinv x (hrle x hx).2.1) else -x`. Establish `hx'1 : ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → (1 + x) * (1 + x' x) = 1 ∧ (1 + x' x) * (1 + x) = 1`. Introduce `x hx`. Establish `hs` using `Classical.choose_spec (hinv x (hrle x hx).2.1)`.

Simplify using `only [x', dif_pos hx]`. Conclude with `⟨hs.1, hs.2.1⟩`. Set `φ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) → HermR (Fv F v) σ n → HermR (Fv F v) σ n` to `fun x b => if hx : nM v x ≤ r then conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx).1 (hx'1 x hx).2 b else b`. Use `set S := {b : HermR (Fv F v) σ n | R < nM v b.1 ∧ nM v b.1 ≤ q * R} with hSdef`. Establish `hSm : MeasurableSet S`.

Establish `hc : Measurable fun b : HermR (Fv F v) σ n => nM v b.1` using `(show Continuous fun b : HermR (Fv F v) σ n => nM v b.1 from continuous_nM.comp continuous_subtype_val).measurable`. Conclude with `(measurableSet_lt measurable_const hc).inter (measurableSet_le hc measurable_const)`. Set `U` to `ballSub (v := v) (E := E) n r hrpos.le`. Establish `hUm : MeasurableSet (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))` using `(isClosed_le continuous_nM continuous_const).measurableSet`. Take `⟨m, hm⟩ : ∃ m : Measure (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), m.IsAddHaarMeasure` from `⟨Measure.addHaar, inferInstance⟩`.

Establish `hUo : IsOpen (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))` using `isOpen_ballM hrpos`. Establish `hU0 : m U ≠ 0` using `hUo.measure_ne_zero m ⟨0, (le_of_eq nM_zero).trans hrpos.le⟩`. Use `haveI := hm`. Establish `hUf : m U ≠ ⊤` using `(show IsCompact (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) from isCompact_ballM r).measure_lt_top.ne`. Use `avg_zero νv m (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) S (whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z) (fun b x => chi ψ T b x) φ hU0 hUf ?_ ?_ ?_ ?_ (continuous_chi h.chr T) hSm hUm` and prove the remaining obligations.

Introduce `x hx`. Establish `hx0 : nM v x ≤ r` using `hx`. Establish `e1 : ∀ b, φ x b = conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b` using `fun b => by`. Simplify using `only [φ, dif_pos hx0]`. Simplify using `only [e1]`.

Conclude with `setIntegral_conj h.cm νv x (x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 (fun b => hpres x (hrle x hx0).1 b) (fun t => R < t ∧ t ≤ q * R) hSm _`. Introduce `x hx b hb`. Establish `hx0 : nM v x ≤ r` using `hx`. Establish `e1 : φ x b = conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b`. Simplify using `only [φ, dif_pos hx0]`.

Rewrite using `[e1]`. Establish `hval : (conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b).1 = conjM σ (1 + x) b.1` using `rfl`. Establish `hnu' : nu2 lam L₁ L₂ (conjM σ (1 + x) b.1) = nu2 lam L₁ L₂ b.1` using `hnu x (hrle x hx0).2.2.2 b.1`. Establish `hJ' : jtR (Fv F v) σ J (psiV F ψ v) μv Φv (conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b) = jtR (Fv F v) σ J (psiV F ψ v) μv Φv b` using `hJ x (hrle x hx0).2.2.1 b _ hval`. Establish `hq1 : psiV F ψ v (-trPair (Fv F v) T.1 (cs σ x * b.1 * x)) = 1`.

Apply `hsmall` to reduce the goal to its premises. Rewrite using `[norm_neg]`. Use `(hquad x b.1).trans ?_` and prove the remaining obligations. Establish `hb2 : nM v b.1 ≤ q * R` using `hb.2`. Establish `hxr : nM v x ^ 2 ≤ r ^ 2` using `pow_le_pow_left₀ (nM_nonneg x) hx0 2`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul_of_nonneg_left hxr hCq) hb2 (nM_nonneg _)` to reduce the goal to its premises. Conclude with `mul_nonneg hCq (sq_nonneg r)`. Use `_ = Cq * Cν ^ 2 * q / R := by rw [hrdef]; field_simp`. Use `_ ≤ ε := by rw [div_le_iff₀ hRpos, mul_comm ε R]; rwa [div_le_iff₀ hε] at hRb`.

Simplify using `only [whI, hnu', hJ', hval, trPair_conj h.cm, chi]`. Rewrite using `[neg_add, neg_add, psiV_add, psiV_add, hq1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `b hb`. Establish `hbpos : 0 < nM v b.1` using `lt_trans hRpos hb.1`.

Establish `hC : Cν ≤ r * nM v b.1`. Rewrite using `[hrdef, div_mul_eq_mul_div, le_div_iff₀ hRpos]`. Conclude with `mul_le_mul_of_nonneg_left hb.1.le hCν.le`. Take `⟨x₀, hx₀, hne⟩` from `hnt b.1 hbpos r hC`. Conclude with `setIntegral_char_eq_zero m U hUm (chi ψ T b) (chi_add ψ T b) (x₀ := x₀) hx₀ hne`.

Introduce `b x`. Conclude with `(norm_psiV h.chr _).le`.
-/
theorem shellP_core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) μv νv lam L₁ L₂ Φv g T
    (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (q : ℝ) (hq : 1 < q) : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ z : ℂ,
      ∫ b in {b : HermR (Fv F v) σ n | R < nM v b.1 ∧ nM v b.1 ≤ q * R},
        whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b ∂νv = 0 := by
  haveI : νv.IsAddHaarMeasure := h.sdH.1
  haveI : μv.IsAddHaarMeasure := h.sdW.1
  haveI : lam.IsAddHaarMeasure := h.haar
  obtain ⟨r1, hr1, hpres⟩ := exists_normPres v σ n
  obtain ⟨r2, hr2, hinv⟩ := exists_inv (E := E) v n
  obtain ⟨r3, hr3, hJ⟩ := jtR_conj_inv v σ h.cm J (psiV F ψ v) μv Φv h.sb
  obtain ⟨r4, hr4, hnu⟩ := lattice_norm_conj_invariant v σ h.cm lam L₁ L₂ h.co₁ h.co₂
  obtain ⟨Cq, hCq, hquad⟩ := exists_quad v σ T.1
  obtain ⟨Cν, hCν, hnt⟩ := exists_nontriv v σ h.cm h.chr T.1 h.unit
  obtain ⟨ε, hε, hsmall⟩ := exists_psiV_small (v := v) h.chr
  set r0 := min (min r1 r2) (min r3 r4) with hr0def
  have hr0 : 0 < r0 := lt_min (lt_min hr1 hr2) (lt_min hr3 hr4)
  refine ⟨max (max (Cν / r0) (Cq * Cν ^ 2 * q / ε)) 1, fun R hR z => ?_⟩
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRa : Cν / r0 ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hRb : Cq * Cν ^ 2 * q / ε ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
  set r := Cν / R with hrdef
  have hrpos : 0 < r := div_pos hCν hRpos
  have hrr0 : r ≤ r0 := by rw [hrdef, div_le_iff₀ hRpos, mul_comm]; rwa [div_le_iff₀ hr0] at hRa
  have hrle : ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r →
      nM v x ≤ r1 ∧ nM v x ≤ r2 ∧ nM v x ≤ r3 ∧ nM v x ≤ r4 := fun x hx =>
    ⟨hx.trans (hrr0.trans ((min_le_left _ _).trans (min_le_left _ _))),
     hx.trans (hrr0.trans ((min_le_left _ _).trans (min_le_right _ _))),
     hx.trans (hrr0.trans ((min_le_right _ _).trans (min_le_left _ _))),
     hx.trans (hrr0.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩

  let x' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun x =>
    if hx : nM v x ≤ r then Classical.choose (hinv x (hrle x hx).2.1) else -x
  have hx'1 : ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r →
      (1 + x) * (1 + x' x) = 1 ∧ (1 + x' x) * (1 + x) = 1 := by
    intro x hx
    have hs := Classical.choose_spec (hinv x (hrle x hx).2.1)
    simp only [x', dif_pos hx]
    exact ⟨hs.1, hs.2.1⟩
  let φ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) → HermR (Fv F v) σ n → HermR (Fv F v) σ n := fun x b =>
    if hx : nM v x ≤ r then conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx).1 (hx'1 x hx).2 b else b
  set S := {b : HermR (Fv F v) σ n | R < nM v b.1 ∧ nM v b.1 ≤ q * R} with hSdef
  have hSm : MeasurableSet S := by
    have hc : Measurable fun b : HermR (Fv F v) σ n => nM v b.1 :=
      (show Continuous fun b : HermR (Fv F v) σ n => nM v b.1 from continuous_nM.comp continuous_subtype_val).measurable
    exact (measurableSet_lt measurable_const hc).inter (measurableSet_le hc measurable_const)
  let U := ballSub (v := v) (E := E) n r hrpos.le
  have hUm : MeasurableSet (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
    (isClosed_le continuous_nM continuous_const).measurableSet
  obtain ⟨m, hm⟩ : ∃ m : Measure (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), m.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  have hUo : IsOpen (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := isOpen_ballM hrpos
  have hU0 : m U ≠ 0 := hUo.measure_ne_zero m ⟨0, (le_of_eq nM_zero).trans hrpos.le⟩
  haveI := hm
  have hUf : m U ≠ ⊤ := (show IsCompact (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) from
    isCompact_ballM r).measure_lt_top.ne
  refine avg_zero νv m (U : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) S
    (whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z) (fun b x => chi ψ T b x) φ hU0 hUf ?_ ?_ ?_ ?_
    (continuous_chi h.chr T) hSm hUm
  ·
    intro x hx
    have hx0 : nM v x ≤ r := hx
    have e1 : ∀ b, φ x b = conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b := fun b => by
      simp only [φ, dif_pos hx0]
    simp only [e1]
    exact setIntegral_conj h.cm νv x (x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 (fun b => hpres x (hrle x hx0).1 b)
      (fun t => R < t ∧ t ≤ q * R) hSm _
  ·
    intro x hx b hb
    have hx0 : nM v x ≤ r := hx
    have e1 : φ x b = conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b := by
      simp only [φ, dif_pos hx0]
    rw [e1]
    have hval : (conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b).1 = conjM σ (1 + x) b.1 := rfl
    have hnu' : nu2 lam L₁ L₂ (conjM σ (1 + x) b.1) = nu2 lam L₁ L₂ b.1 :=
      hnu x (hrle x hx0).2.2.2 b.1
    have hJ' : jtR (Fv F v) σ J (psiV F ψ v) μv Φv (conjE h.cm (1 + x) (1 + x' x) (hx'1 x hx0).1 (hx'1 x hx0).2 b) =
        jtR (Fv F v) σ J (psiV F ψ v) μv Φv b := hJ x (hrle x hx0).2.2.1 b _ hval
    have hq1 : psiV F ψ v (-trPair (Fv F v) T.1 (cs σ x * b.1 * x)) = 1 := by
      apply hsmall
      rw [norm_neg]
      refine (hquad x b.1).trans ?_
      have hb2 : nM v b.1 ≤ q * R := hb.2
      have hxr : nM v x ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (nM_nonneg x) hx0 2
      calc Cq * nM v x ^ 2 * nM v b.1 ≤ Cq * r ^ 2 * (q * R) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hxr hCq) hb2 (nM_nonneg _)
            exact mul_nonneg hCq (sq_nonneg r)
        _ = Cq * Cν ^ 2 * q / R := by rw [hrdef]; field_simp
        _ ≤ ε := by rw [div_le_iff₀ hRpos, mul_comm ε R]; rwa [div_le_iff₀ hε] at hRb
    simp only [whI, hnu', hJ', hval, trPair_conj h.cm, chi]
    rw [neg_add, neg_add, psiV_add, psiV_add, hq1]
    ring
  ·
    intro b hb
    have hbpos : 0 < nM v b.1 := lt_trans hRpos hb.1
    have hC : Cν ≤ r * nM v b.1 := by
      rw [hrdef, div_mul_eq_mul_div, le_div_iff₀ hRpos]
      exact mul_le_mul_of_nonneg_left hb.1.le hCν.le
    obtain ⟨x₀, hx₀, hne⟩ := hnt b.1 hbpos r hC
    exact setIntegral_char_eq_zero m U hUm (chi ψ T b) (chi_add ψ T b) (x₀ := x₀) hx₀ hne
  · intro b x
    exact (norm_psiV h.chr _).le

end Shell

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J n ψ v μv νv lam L₁ L₂ Φv g T h q hq` and use `Shell.shellP_core σ M J n ψ v μv νv lam L₁ L₂ Φv g T h q hq`.
-/
theorem shellP : ShellP := fun F E _ _ _ _ _ σ M J n ψ v μv νv lam L₁ L₂ Φv g T h q hq =>
  Shell.shellP_core σ M J n ψ v μv νv lam L₁ L₂ Φv g T h q hq

end PositivityTheory.SiegelWeilFormula.SwLocFin
