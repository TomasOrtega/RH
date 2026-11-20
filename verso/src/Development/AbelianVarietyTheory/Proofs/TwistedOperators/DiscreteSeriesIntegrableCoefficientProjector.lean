import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorOfIntegrableDiscreteSeriesCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarJacLeExpStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix MeasureTheory

namespace GlobalTheory.DSProj

variable {p q : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jm_eq : Jm p q = Matrix.fromBlocks 1 0 0 (-1) := rfl

/- English proof (translation)
Establish `h12 : X.toBlocks₁₂ = 0`. Use extensionality with `i j; exact hK _ _ (by simp [sameBlock])`. Establish `h21 : X.toBlocks₂₁ = 0`. Use extensionality with `i j; exact hK _ _ (by simp [sameBlock])`. Use `show Xᴴ * Jm p q + Jm p q * X = 0`.

Rewrite using `[hs, jm_eq, ← Matrix.fromBlocks_toBlocks X, h12, h21]`. Simplify using `[Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]`.
-/
theorem mem_upq_of_skew {X : Mat p q} (hK : IsKC X) (hs : Xᴴ = -X) : X ∈ upq p q := by
  have h12 : X.toBlocks₁₂ = 0 := by
    ext i j; exact hK _ _ (by simp [sameBlock])
  have h21 : X.toBlocks₂₁ = 0 := by
    ext i j; exact hK _ _ (by simp [sameBlock])
  show Xᴴ * Jm p q + Jm p q * X = 0
  rw [hs, jm_eq, ← Matrix.fromBlocks_toBlocks X, h12, h21]
  simp [Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]

/- English proof (translation)
Introduce `x y hxy`. Assume the negation of the conclusion as `hne`. Establish `: a = x ∧ b = y`. Assume the negation of the conclusion as `hh`. Conclude with `hne (by simp [Eab, hh])`.

Take `⟨rfl, rfl⟩` from `this`. Conclude with `hxy h`.
-/
theorem isKC_Eab' {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro x y hxy
  by_contra hne
  have : a = x ∧ b = y := by
    by_contra hh
    exact hne (by simp [Eab, hh])
  obtain ⟨rfl, rfl⟩ := this
  exact hxy h

/- English proof (translation)
Apply the tactic sequence `cases a <;> cases b <;> simp_all [sameBlock]`.
-/
theorem sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [sameBlock]

variable {T : GrpData p q}

/- English proof (translation)
The claim follows from `(LinearIsometry.mk (U.π g).toLinearMap (U.isom g)).inner_map_map x y`.
-/
theorem inner_pi (U : URep T) (g : T.G) (x y : U.H) : inner ℂ (U.π g x) (U.π g y) = inner ℂ x y :=
  (LinearIsometry.mk (U.π g).toLinearMap (U.isom g)).inner_map_map x y

/- English proof (translation)
Establish `h` using `(D.der X hX v).inner ℂ (D.der X hX w)`. Simplify using `only [inner_pi, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h`. Conclude with `h.unique (hasDerivAt_const _ _)`.
-/
theorem skew (D : DSRep T) {X : Mat p q} (hX : X ∈ upq p q) (v w : D.HK.V) :
    inner ℂ (D.ι v) (D.ι (D.HK.act X w)) + inner ℂ (D.ι (D.HK.act X v)) (D.ι w) = 0 := by
  have h := (D.der X hX v).inner ℂ (D.der X hX w)
  simp only [inner_pi, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h
  exact h.unique (hasDerivAt_const _ _)

/- English proof (translation)
Establish `k1` using `isKC_Eab' h`. Establish `k2` using `isKC_Eab' (sameBlock_symm h)`. Establish `h1` using `skew D (X := Eab a b - Eab b a) (mem_upq_of_skew (fun x y hxy => by simp [k1 x y hxy, k2 x y hxy]) (by simp [Eab, Matrix.conjTranspose_single])) v w`. Establish `h2` using `skew D (X := Complex.I • (Eab a b + Eab b a)) (mem_upq_of_skew (fun x y hxy => by simp [k1 x y hxy, k2 x y hxy]) (by`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add]`.

Simplify using `only [Eab, Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, neg_smul]`. Rewrite using `[add_comm])) v w`. Simplify using `only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I] at h1 h2`. Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Take the linear combination `(1 / 2) * h1 + (Complex.I / 2) * h2 + (1/2) * (inner ℂ (D.ι (D.HK.act (Eab a b) v)) (D.ι w) + inner ℂ (D.ι (D.HK.act (Eab b a) v)) (D.ι w) - inner ℂ (D.ι v) (D.ι (D.HK.act (Eab b a) w)) - inner ℂ (D.ι v) (D.ι (D.HK.act (Eab a b) w))) * hI`.
-/
theorem adj_Eab (D : DSRep T) {a b : Ix p q} (h : sameBlock a b) (v w : D.HK.V) :
    inner ℂ (D.ι (D.HK.act (Eab a b) v)) (D.ι w) = inner ℂ (D.ι v) (D.ι (D.HK.act (Eab b a) w)) := by
  have k1 := isKC_Eab' h
  have k2 := isKC_Eab' (sameBlock_symm h)
  have h1 := skew D (X := Eab a b - Eab b a) (mem_upq_of_skew
    (fun x y hxy => by simp [k1 x y hxy, k2 x y hxy]) (by simp [Eab, Matrix.conjTranspose_single])) v w
  have h2 := skew D (X := Complex.I • (Eab a b + Eab b a)) (mem_upq_of_skew
    (fun x y hxy => by simp [k1 x y hxy, k2 x y hxy])
    (by
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add]
      simp only [Eab, Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, neg_smul]
      rw [add_comm])) v w
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2) * h1 + (Complex.I / 2) * h2 + (1/2) * (inner ℂ (D.ι (D.HK.act (Eab a b) v)) (D.ι w) + inner ℂ (D.ι (D.HK.act (Eab b a) v)) (D.ι w) - inner ℂ (D.ι v) (D.ι (D.HK.act (Eab b a) w)) - inner ℂ (D.ι v) (D.ι (D.HK.act (Eab a b) w))) * hI

/- English proof (translation)
Use `(Submodule.mem_iInf _).1 hv.2.1 a` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.
-/
theorem hw_wt {V : Type*} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} (hv : IsHW act μ v) (a : Ix p q) :
    act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  have := (Submodule.mem_iInf _).1 hv.2.1 a
  simpa [sub_eq_zero] using this

/- English proof (translation)
Use `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv.2.2 a) b) hab` as an intermediate fact. Simplify using `using this`.
-/
theorem hw_kill {V : Type*} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} (hv : IsHW act μ v) (a b : Ix p q) (hab : posC a b) :
    act (Eab a b) v = 0 := by
  have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv.2.2 a) b) hab
  simpa using this

open GlobalTheory.RealPar.HwGen in

/- English proof (translation)
Take `⟨W₀, hfin, hv₀, hW₀⟩` from `D.HK.kfin v`. Establish `hle : Submodule.span ℂ (Set.range (mono D.HK.act v)) ≤ W₀`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, rfl⟩`. Proceed by induction on `l with`.

Consider the case `nil => exact hv₀`. Consider the case `cons r l ih => exact hW₀ _ (isKC_Eab r.2) _ ih`. Use `⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨[], rfl⟩, mono_stable D.HK.lie (hw_wt hv) (hw_kill hv), fun ν w hw hν => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h0 : inner ℂ (D.ι v) (D.ι w) = 0`.

Take `⟨a, ha⟩` from `Function.ne_iff.1 hne`. Apply the tactic sequence `have h := adj_Eab D (a := a) (b := a) (by cases a <;> simp [sameBlock]) v w`. Rewrite `h` using `[hw_wt hv, hw_wt hν, map_smul, map_smul, inner_smul_left, inner_smul_right]`. Simplify using `only [map_ratCast] at h`. Establish `hc : ((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ) ≠ 0`.

Rewrite using `[sub_ne_zero]`. Conclude with `ha.symm` after adjusting the coercions. Conclude with `(mul_eq_zero.1 (by linear_combination h)).resolve_left hc`. Establish `hall : ∀ x ∈ Submodule.span ℂ (Set.range (mono D.HK.act v)), inner ℂ (D.ι x) (D.ι w) = 0`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, rfl⟩` from `hx`. Consider the cases of `l with`. Consider the case `nil => exact h0`.

Consider the case `cons r l`. Establish `hr` using `r.2`. Rewrite using `[mono, adj_Eab D (by`. Generalize the expression as in `r.1.1 = a at hr`. Generalize the expression as in `r.1.2 = b at hr`.

Apply the tactic sequence `cases a <;> cases b <;> simp_all [posC, sameBlock]), hw_kill hν _ _ r.2]`. Simplify using the standard rewrite rules. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [inner_add_left, hx, hy]`. Consider the case `smul c x _ hx => simp [inner_smul_left, hx]`.

Use `inner_self_eq_zero.1 (hall w hw)` as an intermediate fact. Conclude with `hν.1 (D.ι_inj (by rw [this, map_zero]))`.
-/
theorem ofType_of_isHW (D : DSRep T) {μ : Ix p q → ℚ} {v : D.HK.V} (hv : IsHW D.HK.act μ v) :
    OfType D.HK.act μ v := by
  obtain ⟨W₀, hfin, hv₀, hW₀⟩ := D.HK.kfin v
  have hle : Submodule.span ℂ (Set.range (mono D.HK.act v)) ≤ W₀ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact hv₀
    | cons r l ih => exact hW₀ _ (isKC_Eab r.2) _ ih
  refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨[], rfl⟩,
    mono_stable D.HK.lie (hw_wt hv) (hw_kill hv), fun ν w hw hν => ?_⟩
  by_contra hne
  have h0 : inner ℂ (D.ι v) (D.ι w) = 0 := by
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
    have h := adj_Eab D (a := a) (b := a) (by cases a <;> simp [sameBlock]) v w
    rw [hw_wt hv, hw_wt hν, map_smul, map_smul, inner_smul_left, inner_smul_right] at h
    simp only [map_ratCast] at h
    have hc : ((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast ha.symm
    exact (mul_eq_zero.1 (by linear_combination h)).resolve_left hc
  have hall : ∀ x ∈ Submodule.span ℂ (Set.range (mono D.HK.act v)), inner ℂ (D.ι x) (D.ι w) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      cases l with
      | nil => exact h0
      | cons r l =>
        have hr := r.2
        rw [mono, adj_Eab D (by
          generalize r.1.1 = a at hr
          generalize r.1.2 = b at hr
          cases a <;> cases b <;> simp_all [posC, sameBlock]), hw_kill hν _ _ r.2]
        simp
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul c x _ hx => simp [inner_smul_left, hx]
  have := inner_self_eq_zero.1 (hall w hw)
  exact hν.1 (D.ι_inj (by rw [this, map_zero]))

/- English proof (translation)
Simplify using `[pOf, Matrix.fromBlocks_conjTranspose]`.
-/
theorem pOf_herm (B : Matrix (Fin p) (Fin q) ℂ) : (pOf B)ᴴ = pOf B := by
  simp [pOf, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0`. Rewrite using `[pOf_herm, jm_eq, pOf]`. Simplify using `[Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]`. Introduce `a b hab`.

Apply the tactic sequence `cases a <;> cases b <;> simp_all [sameBlock, pOf]`.
-/
theorem pOf_mem (B : Matrix (Fin p) (Fin q) ℂ) : pOf B ∈ pR p q := by
  refine ⟨?_, ?_⟩
  · show (pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0
    rw [pOf_herm, jm_eq, pOf]
    simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock, pOf]

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem hsNorm_nonneg (Y : Mat p q) : 0 ≤ hsNorm Y := Real.sqrt_nonneg _

/- English proof (translation)
Use `conv_rhs => enter [1, 2]`. Rewrite using `[← hY]`. Simplify using `[Matrix.trace, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
theorem hsNorm_sq_trace {Y : Mat p q} (hY : Yᴴ = Y) :
    ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) = (Y * Y).trace := by
  conv_rhs => enter [1, 2]; rw [← hY]
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Unfold `hsNorm`. Use `congr 1`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[hsNorm_sq_trace hY, hsNorm_sq_trace hH, h]`. Establish `: (u : Mat p q) * H * ((u⁻¹ : GL (Ix p q) ℂ) : Mat p q) * ((u : Mat p q) * H * ((u⁻¹ : GL (Ix p q) ℂ) : Mat p q)) = (u : Mat p q) * (H * H) * ((u⁻¹ : GL (Ix p q) ℂ) : Mat p q)`.

Simplify using `only [Matrix.mul_assoc, Units.inv_mul_cancel_left]`. Rewrite using `[this, Matrix.trace_units_conj]`.
-/
theorem hsNorm_conj {Y H : Mat p q} (hY : Yᴴ = Y) (hH : Hᴴ = H) (u : GL (Ix p q) ℂ)
    (h : Y = (u : Mat p q) * H * ((u⁻¹ : GL (Ix p q) ℂ) : Mat p q)) : hsNorm Y = hsNorm H := by
  unfold hsNorm
  congr 1
  apply Complex.ofReal_injective
  rw [hsNorm_sq_trace hY, hsNorm_sq_trace hH, h]
  have : (u : Mat p q) * H * ((u⁻¹ : GL (Ix p q) ℂ) : Mat p q) *
      ((u : Mat p q) * H * ((u⁻¹ : GL (Ix p q) ℂ) : Mat p q)) =
      (u : Mat p q) * (H * H) * ((u⁻¹ : GL (Ix p q) ℂ) : Mat p q) := by
    simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
  rw [this, Matrix.trace_units_conj]

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (hsNorm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (hsNorm_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_hsNorm (B : Fin p → Fin q → ℂ) : ‖B‖ ≤ hsNorm (pOf (Matrix.of B)) := by
  refine (pi_norm_le_iff_of_nonneg (hsNorm_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (hsNorm_nonneg _)).2 fun j => ?_
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖B i j‖ ^ 2 = ‖pOf (Matrix.of B) (.inl i) (.inr j)‖ ^ 2 := by simp [pOf]
    _ ≤ ∑ b, ‖pOf (Matrix.of B) (.inl i) b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b => ‖pOf (Matrix.of B) (.inl i) b‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ _)
    _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b, ‖pOf (Matrix.of B) a b‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ _)

/- English proof (translation)
Establish `: pOf B = 0`. Establish `hB : B = 0`. Use extensionality with `i j`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `[pOf, hB]`. Simplify using `[hsNorm, this]`.
-/
theorem hsNorm_eq_zero (h : min p q = 0) (B : Matrix (Fin p) (Fin q) ℂ) : hsNorm (pOf B) = 0 := by
  have : pOf B = 0 := by
    have hB : B = 0 := by
      ext i j
      have := i.2; have := j.2; omega
    simp [pOf, hB]
  simp [hsNorm, this]

/- English proof (translation)
Use `set N := Module.finrank ℝ E + 1 with hN`. Establish `h` using `(integrable_one_add_norm (E := E) (μ := μ) (r := (N : ℝ)) (by simp [hN])).const_mul (Real.exp a * N.factorial / a ^ N)`. Use `h.mono' (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Establish `hx : 0 < 1 + ‖x‖` using `by positivity`. Establish `h1` using `Real.pow_div_factorial_le_exp (a * (1 + ‖x‖)) (by positivity) N`.

Rewrite using `[Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_neg hx.le, Real.rpow_natCast, Real.exp_neg]`. Rewrite `h1` using `[mul_add, mul_one, Real.exp_add, ← mul_one_add, mul_pow, div_le_iff₀ (by positivity)]`. Establish `he` using `Real.exp_pos (a * ‖x‖)`. Rewrite using `[← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity), inv_mul_le_iff₀ he]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem integrable_exp_neg_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E => Real.exp (-(a * ‖x‖))) μ := by
  set N := Module.finrank ℝ E + 1 with hN
  have h := (integrable_one_add_norm (E := E) (μ := μ) (r := (N : ℝ)) (by simp [hN])).const_mul
    (Real.exp a * N.factorial / a ^ N)
  refine h.mono' (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hx : 0 < 1 + ‖x‖ := by positivity
  have h1 := Real.pow_div_factorial_le_exp (a * (1 + ‖x‖)) (by positivity) N
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_neg hx.le, Real.rpow_natCast, Real.exp_neg]
  rw [mul_add, mul_one, Real.exp_add, ← mul_one_add, mul_pow, div_le_iff₀ (by positivity)] at h1
  have he := Real.exp_pos (a * ‖x‖)
  rw [← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity), inv_mul_le_iff₀ he]
  linarith

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (min p q) with h0 | h0` into its components or cases. Conclude with `⟨0, 1, one_pos, fun B => by simp [hsNorm_eq_zero h0]⟩`. Establish `hn : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ p + q)`. Establish `hm : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ)` using `by exact_mod_cast h0`. Unfold `rangeOfSeventhSum at hh`.

Generalize the expression as in `((p + q : ℕ) : ℝ) = n at *`. Generalize the expression as in `((min p q : ℕ) : ℝ) = m at *`. Establish `hm' : m ≤ m ^ ((3 : ℝ) / 2)` using `by conv_lhs => rw [← Real.rpow_one m]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hm (by norm_num)`. Establish `hnm : 120 * (n * m) ≤ h` using `by nlinarith`.

Establish `hnm1 : 1 ≤ n * m` using `by nlinarith`. Establish `hs : 0 < Real.sqrt (2 * m)` using `Real.sqrt_pos.2 (by linarith)`. Establish `hss : Real.sqrt (2 * m) * Real.sqrt (2 * m) = 2 * m` using `Real.mul_self_sqrt (by linarith)`. Generalize the expression as in `Real.sqrt (2 * m) = s at *`. Use `⟨h / 8 * (1 / s ^ 2), h / 8 / s - n * s, ?_, fun B => ?_⟩` and prove the remaining obligations.

Rewrite using `[sub_pos, lt_div_iff₀ hs]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hr` using `hsNorm_nonneg (pOf B)`. Generalize the expression as in `hsNorm (pOf B) = r at *`. Establish `key : r / s - 1 / s ^ 2 ≤ min (r ^ 2) (r / s)`.

Use `le_min ?_ (by have : 0 < 1 / s ^ 2 := by positivity linarith)` and prove the remaining obligations. Establish `e1 : r / s = r * (1 / s)` using `by ring`. Establish `e2 : 1 / s ^ 2 = (1 / s) ^ 2` using `by ring`. Rewrite using `[e1, e2]`. Use polynomial arithmetic with `[sq_nonneg (r - 1 / s), sq_nonneg r, sq_nonneg (1 / s)]`.

Establish `h8 : 0 ≤ h / 8` using `by linarith`. Use `mul_le_mul_of_nonneg_left key h8` as an intermediate fact. Establish `e3 : h / 8 / s * r = h / 8 * (r / s)` using `by ring`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exponent_le {h : ℝ} (hh : rangeOfSeventhSum p q ≤ h) : ∃ C a : ℝ, 0 < a ∧ ∀ B : Matrix (Fin p) (Fin q) ℂ,
    -(h / 8) * min (hsNorm (pOf B) ^ 2) (hsNorm (pOf B) / Real.sqrt (2 * (min p q : ℕ))) +
      ((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * hsNorm (pOf B) ≤ C - a * hsNorm (pOf B) := by
  rcases Nat.eq_zero_or_pos (min p q) with h0 | h0
  · exact ⟨0, 1, one_pos, fun B => by simp [hsNorm_eq_zero h0]⟩
  have hn : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ p + q)
  have hm : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ) := by exact_mod_cast h0
  unfold rangeOfSeventhSum at hh
  generalize ((p + q : ℕ) : ℝ) = n at *
  generalize ((min p q : ℕ) : ℝ) = m at *
  have hm' : m ≤ m ^ ((3 : ℝ) / 2) := by
    conv_lhs => rw [← Real.rpow_one m]
    exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hnm : 120 * (n * m) ≤ h := by nlinarith
  have hnm1 : 1 ≤ n * m := by nlinarith
  have hs : 0 < Real.sqrt (2 * m) := Real.sqrt_pos.2 (by linarith)
  have hss : Real.sqrt (2 * m) * Real.sqrt (2 * m) = 2 * m := Real.mul_self_sqrt (by linarith)
  generalize Real.sqrt (2 * m) = s at *
  refine ⟨h / 8 * (1 / s ^ 2), h / 8 / s - n * s, ?_, fun B => ?_⟩
  · rw [sub_pos, lt_div_iff₀ hs]; nlinarith
  have hr := hsNorm_nonneg (pOf B)
  generalize hsNorm (pOf B) = r at *
  have key : r / s - 1 / s ^ 2 ≤ min (r ^ 2) (r / s) := by
    refine le_min ?_ (by have : 0 < 1 / s ^ 2 := by positivity
                         linarith)
    have e1 : r / s = r * (1 / s) := by ring
    have e2 : 1 / s ^ 2 = (1 / s) ^ 2 := by ring
    rw [e1, e2]
    nlinarith [sq_nonneg (r - 1 / s), sq_nonneg r, sq_nonneg (1 / s)]
  have h8 : 0 ≤ h / 8 := by linarith
  have := mul_le_mul_of_nonneg_left key h8
  have e3 : h / 8 / s * r = h / 8 * (r / s) := by ring
  nlinarith

/- English proof (translation)
Use `haveI : SecondCountableTopology (Matrix (Ix p q) (Ix p q) ℂ) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))`. Use `haveI : SecondCountableTopology (Matrix (Ix p q) (Ix p q) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology ℂᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology`.

Conclude with `T.emb.secondCountableTopology`.
-/
theorem secondCountable_grp (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Matrix (Ix p q) (Ix p q) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Matrix (Ix p q) (Ix p q) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology ℂᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  exact T.emb.secondCountableTopology

/- English proof (translation)
Unfold `eFun mcoef`. Conclude with `continuous_const.mul (continuous_const.inner (D.U.cont _)).star`.
-/
theorem continuous_eFun (D : DSRep T) (v : D.HK.V) : Continuous (eFun D v) := by
  unfold eFun mcoef
  exact continuous_const.mul (continuous_const.inner (D.U.cont _)).star

/- English proof (translation)
Establish `hc` using `continuous_eFun (X.ds p q lam) v`. Use `⟨hc.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Take `⟨⟨c, mK, -, hprob, hK, -, hint⟩, hinv, hdec, hJ⟩` from `h6 p q`. Take `⟨C, a, ha, hC⟩` from `exponent_le hh`. Establish `hiso : (X.ds p q lam).ι v ∈ isoVec (X.ds p q lam) (blattner lam)` using `⟨v, ofType_of_isHW (X.ds p q lam) hv.1, rfl⟩`.

Establish `hd` using `(X.ds p q lam).fdeg_pos`. Rewrite using `[hasFiniteIntegral_iff_enorm, hint _ hc.enorm.measurable]`. Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_` and prove the remaining obligations. Use `haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`.

Establish `hI` using `((integrable_exp_neg_norm (volume : Measure (Fin p → Fin q → ℂ)) ha).const_mul ((X.ds p q lam).fdeg * Real.exp C)).2`. Rewrite `hI` using `[hasFiniteIntegral_iff_enorm]`. Use `lt_of_le_of_lt (lintegral_mono fun B => ?_) hI` and prove the remaining obligations. Use `set Y := pOf (Matrix.of B) with hY`. Establish `hYm : Y ∈ pR p q` using `pOf_mem _`.

Use `set E := Real.exp (-(h / 8) * min (hsNorm Y ^ 2) (hsNorm Y / Real.sqrt (2 * (min p q : ℕ)))) with hE`. Establish `hE0 : 0 < E` using `Real.exp_pos _`. Establish `b1 : ∫⁻ k, ‖eFun (X.ds p q lam) v (k * (X.grp p q).expt Y)‖ₑ ∂mK ≤ ENNReal.ofReal ((X.ds p q lam).fdeg * E)`. Establish `hae : ∀ᵐ k ∂mK, k ∈ (X.grp p q).Kset` using `hK`. Use `le_trans (lintegral_mono_ae (g := fun _ => ENNReal.ofReal ((X.ds p q lam).fdeg * E)) (hae.mono fun k hk => ?_)) (by simp)` and prove the remaining obligations.

Use `(h2 p q lam hl h hg hh).2 k hk Y hYm _ hiso _ hiso` as an intermediate fact. Rewrite `this` using `[hv.2, mul_one, mul_one]`. Rewrite using `[← ofReal_norm_eq_enorm]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[eFun, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hd.le]`.

Conclude with `mul_le_mul_of_nonneg_left this hd.le`. Establish `b2 : polJ Y ≤ Real.exp (((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * hsNorm Y)`. Take `⟨k, hk, t, ht⟩` from `hdec Y hYm`. Establish `e1 : hsNorm Y = hsNorm (aOf p q t)` using `hsNorm_conj (pOf_herm _) (pOf_herm _) _ ht`. Establish `e2 : polJ Y = polJ (aOf p q t)`.

Rewrite using `[ht]`. Conclude with `hinv k hk _ (pOf_mem _)`. Rewrite using `[e1, e2, hJ]`. Conclude with `GlobalTheory.T.polarJac_le_exp_hsNorm p q t`. Use `le_trans (mul_le_mul' b1 (ENNReal.ofReal_le_ofReal b2)) ?_` and prove the remaining obligations.

Rewrite using `[← ENNReal.ofReal_mul (by positivity), Real.enorm_of_nonneg (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[mul_assoc _ E, mul_assoc _ (Real.exp C), hE, ← Real.exp_add, ← Real.exp_add]`. Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hd.le` and prove the remaining obligations. Use `hC (Matrix.of B)` as an intermediate fact.

Establish `hb` using `mul_le_mul_of_nonneg_left (norm_le_hsNorm B) ha.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem integrable_eFun (X : ProvA) (h2 : DiscreteSeriesPositivity X) (h6 : CoverHaarIntegration X) (lam : Ix p q → ℚ) (hl : IsParam lam)
    (h : ℝ) (hg : GapGe lam h) (hh : rangeOfSeventhSum p q ≤ h) (v : (X.ds p q lam).HK.V)
    (hv : UnitHW (X.ds p q lam) (blattner lam) v) :
    Integrable (eFun (X.ds p q lam) v) (X.grp p q).haar := by
  have hc := continuous_eFun (X.ds p q lam) v
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  obtain ⟨⟨c, mK, -, hprob, hK, -, hint⟩, hinv, hdec, hJ⟩ := h6 p q
  obtain ⟨C, a, ha, hC⟩ := exponent_le hh
  have hiso : (X.ds p q lam).ι v ∈ isoVec (X.ds p q lam) (blattner lam) := ⟨v, ofType_of_isHW (X.ds p q lam) hv.1, rfl⟩
  have hd := (X.ds p q lam).fdeg_pos
  rw [hasFiniteIntegral_iff_enorm, hint _ hc.enorm.measurable]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hI := ((integrable_exp_neg_norm (volume : Measure (Fin p → Fin q → ℂ)) ha).const_mul
    ((X.ds p q lam).fdeg * Real.exp C)).2
  rw [hasFiniteIntegral_iff_enorm] at hI
  refine lt_of_le_of_lt (lintegral_mono fun B => ?_) hI
  set Y := pOf (Matrix.of B) with hY
  have hYm : Y ∈ pR p q := pOf_mem _
  set E := Real.exp (-(h / 8) * min (hsNorm Y ^ 2) (hsNorm Y / Real.sqrt (2 * (min p q : ℕ)))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have b1 : ∫⁻ k, ‖eFun (X.ds p q lam) v (k * (X.grp p q).expt Y)‖ₑ ∂mK ≤ ENNReal.ofReal ((X.ds p q lam).fdeg * E) := by
    have hae : ∀ᵐ k ∂mK, k ∈ (X.grp p q).Kset := hK
    refine le_trans (lintegral_mono_ae (g := fun _ => ENNReal.ofReal ((X.ds p q lam).fdeg * E))
      (hae.mono fun k hk => ?_)) (by simp)
    have := (h2 p q lam hl h hg hh).2 k hk Y hYm _ hiso _ hiso
    rw [hv.2, mul_one, mul_one] at this
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [eFun, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hd.le]
    exact mul_le_mul_of_nonneg_left this hd.le
  have b2 : polJ Y ≤ Real.exp (((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * hsNorm Y) := by
    obtain ⟨k, hk, t, ht⟩ := hdec Y hYm
    have e1 : hsNorm Y = hsNorm (aOf p q t) := hsNorm_conj (pOf_herm _) (pOf_herm _) _ ht
    have e2 : polJ Y = polJ (aOf p q t) := by
      rw [ht]; exact hinv k hk _ (pOf_mem _)
    rw [e1, e2, hJ]
    exact GlobalTheory.T.polarJac_le_exp_hsNorm p q t
  refine le_trans (mul_le_mul' b1 (ENNReal.ofReal_le_ofReal b2)) ?_
  rw [← ENNReal.ofReal_mul (by positivity), Real.enorm_of_nonneg (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_assoc _ E, mul_assoc _ (Real.exp C), hE, ← Real.exp_add, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hd.le
  have := hC (Matrix.of B)
  have hb := mul_le_mul_of_nonneg_left (norm_le_hsNorm B) ha.le
  linarith

/- English proof (translation)
Introduce `X h2 h6 p q lam hl h hg hh v hv`. Establish `hi` using `integrable_eFun X h2 h6 lam hl h hg hh v hv`. Use `haveI := secondCountable_grp (X.grp p q)`. Use `⟨hi, fun πU => ?_⟩` and prove the remaining obligations. Take `⟨hD1, hπ⟩` from `GlobalTheory.T.projector_of_integrable_discreteSeries_coefficient p q (X.grp p q) (X.ds p q lam) v hv.2 hi`.

Take `⟨hsa, hPP, hio⟩` from `hπ πU`. Establish `hvv : inner ℂ ((X.ds p q lam).ι v) ((X.ds p q lam).ι v) = 1`. Rewrite using `[inner_self_eq_norm_sq_to_K, hv.2]`. Simplify using the standard rewrite rules. Use `⟨fun x => ⟨?_, fun y hy => ?_⟩, hPP⟩` and prove the remaining obligations.

Establish `h1` using `hPP 1 x`. Simplify using `only [map_one, ContinuousLinearMap.one_apply, mcoef, hvv, one_smul] at h1`. Take `⟨io, hio1, hio2, -⟩` from `hio _ h1`. Conclude with `Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨io, hio1, hio2.symm⟩)`. Use `Submodule.inner_left_of_mem_orthogonal (K := ℂ ∙ (x - opE _ πU.π (eFun (X.ds p q lam) v) x)) (Submodule.mem_span_singleton_self _) ?_` and prove the remaining obligations.

Use `Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) (Submodule.isClosed_orthogonal _) hy` and prove the remaining obligations. Introduce and unpack `_ ⟨io, hio1, rfl⟩`. Establish `hfix : opE (X.grp p q) πU.π (eFun (X.ds p q lam) v) (io ((X.ds p q lam).ι v)) = io ((X.ds p q lam).ι v)`. Establish `hint : Integrable (fun g => eFun (X.ds p q lam) v g • (X.ds p q lam).U.π g ((X.ds p q lam).ι v)) (X.grp p q).haar`. Use `hi.norm.mono' ((continuous_eFun (X.ds p q lam) v).smul ((X.ds p q lam).U.cont _)).aestronglyMeasurable (ae_of_all _ fun g => ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul, (X.ds p q lam).U.isom, hv.2, mul_one]`. Establish `h1` using `hD1 ((X.ds p q lam).ι v)`. Rewrite `h1` using `[hvv, one_smul]`. Use `conv_rhs => rw [← h1]`. Unfold `opE`.

Rewrite using `[← io.integral_comp_comm hint]`. Use `integral_congr_ae (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Use `congrArg (fun A => A ((X.ds p q lam).ι v)) (hio1 g)` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply] at this`. Simplify using `only [map_smul, this]`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, ← hsa, hfix, sub_self]`.
-/
theorem discreteSeriesHighestVector_of_positivity : ∀ X : ProvA, DiscreteSeriesPositivity X → CoverHaarIntegration X → DiscreteSeriesHighestVector X := by
  intro X h2 h6 p q lam hl h hg hh v hv
  have hi := integrable_eFun X h2 h6 lam hl h hg hh v hv
  haveI := secondCountable_grp (X.grp p q)
  refine ⟨hi, fun πU => ?_⟩
  obtain ⟨hD1, hπ⟩ := GlobalTheory.T.projector_of_integrable_discreteSeries_coefficient p q (X.grp p q) (X.ds p q lam) v hv.2 hi
  obtain ⟨hsa, hPP, hio⟩ := hπ πU
  have hvv : inner ℂ ((X.ds p q lam).ι v) ((X.ds p q lam).ι v) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hv.2]; simp
  refine ⟨fun x => ⟨?_, fun y hy => ?_⟩, hPP⟩
  · have h1 := hPP 1 x
    simp only [map_one, ContinuousLinearMap.one_apply, mcoef, hvv, one_smul] at h1
    obtain ⟨io, hio1, hio2, -⟩ := hio _ h1
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨io, hio1, hio2.symm⟩)
  · refine Submodule.inner_left_of_mem_orthogonal (K := ℂ ∙ (x - opE _ πU.π (eFun (X.ds p q lam) v) x))
      (Submodule.mem_span_singleton_self _) ?_
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      (Submodule.isClosed_orthogonal _) hy
    rintro _ ⟨io, hio1, rfl⟩
    have hfix : opE (X.grp p q) πU.π (eFun (X.ds p q lam) v) (io ((X.ds p q lam).ι v)) = io ((X.ds p q lam).ι v) := by
      have hint : Integrable (fun g => eFun (X.ds p q lam) v g • (X.ds p q lam).U.π g ((X.ds p q lam).ι v)) (X.grp p q).haar := by
        refine hi.norm.mono' ((continuous_eFun (X.ds p q lam) v).smul ((X.ds p q lam).U.cont _)).aestronglyMeasurable
          (ae_of_all _ fun g => ?_)
        rw [norm_smul, (X.ds p q lam).U.isom, hv.2, mul_one]
      have h1 := hD1 ((X.ds p q lam).ι v)
      rw [hvv, one_smul] at h1
      conv_rhs => rw [← h1]
      unfold opE
      rw [← io.integral_comp_comm hint]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      have := congrArg (fun A => A ((X.ds p q lam).ι v)) (hio1 g)
      simp only [ContinuousLinearMap.comp_apply] at this
      simp only [map_smul, this]
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, ← hsa, hfix, sub_self]

end GlobalTheory.DSProj
