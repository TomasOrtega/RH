import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP

open scoped SchwartzMap ContDiff

noncomputable section

namespace GlobalTheory.SchrGrowth

open GlobalTheory.ArchUniq

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- English proof (translation)
Establish `hp : ContDiff ℝ ∞ (fun v => Complex.exp (ℓ v + c))` using `(Complex.contDiff_exp (𝕜 := ℝ)).comp (ℓ.contDiff.add contDiff_const)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro u`. Simplify using `[norm_iteratedFDeriv_zero]`.

Consider the case `succ i ih`. Introduce `u`. Rewrite using `[← norm_iteratedFDeriv_fderiv]`. Set `T : ℂ →L[ℝ] (V →L[ℝ] ℂ)` to `ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) ℓ`. Establish `hT : ∀ a : ℂ, T a = a • ℓ` using `fun a => rfl`.

Establish `hfd : fderiv ℝ (fun v => Complex.exp (ℓ v + c)) = T ∘ (fun v => Complex.exp (ℓ v + c))`. Use function extensionality and compare the values at `v`. Rewrite using `[Function.comp_apply, hT, (((ℓ.hasFDerivAt (x := v)).add_const c).cexp).fderiv]`. Rewrite using `[hfd]`. Use `(T.norm_iteratedFDeriv_comp_left hp.contDiffAt (by exact_mod_cast le_top)).trans ?_` and prove the remaining obligations.

Establish `hTn : ‖T‖ ≤ ‖ℓ‖`. Use `ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_` and prove the remaining obligations. Rewrite using `[hT, norm_smul, mul_comm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_iteratedFDeriv_exp_affine_le (ℓ : V →L[ℝ] ℂ) (c : ℂ) :
    ∀ (i : ℕ) (u : V), ‖iteratedFDeriv ℝ i (fun v => Complex.exp (ℓ v + c)) u‖ ≤
      ‖Complex.exp (ℓ u + c)‖ * ‖ℓ‖ ^ i := by
  have hp : ContDiff ℝ ∞ (fun v => Complex.exp (ℓ v + c)) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp (ℓ.contDiff.add contDiff_const)
  intro i
  induction i with
  | zero => intro u; simp [norm_iteratedFDeriv_zero]
  | succ i ih =>
    intro u
    rw [← norm_iteratedFDeriv_fderiv]
    let T : ℂ →L[ℝ] (V →L[ℝ] ℂ) := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) ℓ
    have hT : ∀ a : ℂ, T a = a • ℓ := fun a => rfl
    have hfd : fderiv ℝ (fun v => Complex.exp (ℓ v + c)) = T ∘ (fun v => Complex.exp (ℓ v + c)) := by
      funext v
      rw [Function.comp_apply, hT, (((ℓ.hasFDerivAt (x := v)).add_const c).cexp).fderiv]
    rw [hfd]
    refine (T.norm_iteratedFDeriv_comp_left hp.contDiffAt (by exact_mod_cast le_top)).trans ?_
    have hTn : ‖T‖ ≤ ‖ℓ‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_
      rw [hT, norm_smul, mul_comm]
    calc ‖T‖ * ‖iteratedFDeriv ℝ i (fun v => Complex.exp (ℓ v + c)) u‖
        ≤ ‖ℓ‖ * (‖Complex.exp (ℓ u + c)‖ * ‖ℓ‖ ^ i) :=
          mul_le_mul hTn (ih u) (norm_nonneg _) (norm_nonneg _)
      _ = ‖Complex.exp (ℓ u + c)‖ * ‖ℓ‖ ^ (i + 1) := by ring

variable [FiniteDimensional ℝ V]

def pairCLM {P : V → V → ℝ} (h : IsPairing P) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ P h.addL (fun c x y => by simpa [smul_eq_mul] using h.smulL c x y) h.addR
        (fun c x y => by simpa [smul_eq_mul] using h.smulR c x y))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairCLM_apply {P : V → V → ℝ} (h : IsPairing P) (x y : V) : pairCLM h x y = P x y := rfl

/- English proof (translation)
The claim follows from `|P x y| ≤ ‖pairCLM h‖ * ‖x‖ * ‖y‖ := by rw [← pairCLM_apply h, ← Real.norm_eq_abs] exact (pairCLM h).le_opNorm₂ x y`.
-/
theorem abs_pair_le {P : V → V → ℝ} (h : IsPairing P) (x y : V) :
    |P x y| ≤ ‖pairCLM h‖ * ‖x‖ * ‖y‖ := by
  rw [← pairCLM_apply h, ← Real.norm_eq_abs]
  exact (pairCLM h).le_opNorm₂ x y

def phase {P : V → V → ℝ} (h : IsPairing P) (b : V) : V →L[ℝ] ℂ :=
  (-(2 * Real.pi * Complex.I)) • (Complex.ofRealCLM.comp ((pairCLM h).flip b))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phase_apply {P : V → V → ℝ} (h : IsPairing P) (b y : V) :
    phase h b y = -(2 * Real.pi * Complex.I) * ((P y b : ℝ) : ℂ) := rfl

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_` and prove the remaining obligations. Rewrite using `[phase_apply, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]`. Establish `e : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi`. Simplify using `[abs_of_pos Real.pi_pos]`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_phase_le {P : V → V → ℝ} (h : IsPairing P) (b : V) :
    ‖phase h b‖ ≤ 2 * Real.pi * ‖pairCLM h‖ * ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [phase_apply, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have e : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [e]
  calc 2 * Real.pi * |P y b| ≤ 2 * Real.pi * (‖pairCLM h‖ * ‖y‖ * ‖b‖) := by
        gcongr; exact abs_pair_le h y b
    _ = 2 * Real.pi * ‖pairCLM h‖ * ‖b‖ * ‖y‖ := by ring

def cst (P : V → V → ℝ) (w : V × V) : ℂ := -(2 * Real.pi * Complex.I) * ((P w.1 w.2 / 2 : ℝ) : ℂ)

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [schrF, phase_apply, cst]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schrF_eq {P : V → V → ℝ} (h : IsPairing P) (w : V × V) (f : V → ℂ) :
    schrF P w f = fun y => Complex.exp (phase h w.2 y + cst P w) * f (y + w.1) := by
  funext y
  simp only [schrF, phase_apply, cst]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `e : phase h w.2 y + cst P w = (((-(2 * Real.pi)) * (P y w.2 + P w.1 w.2 / 2) : ℝ) : ℂ) * Complex.I`. Rewrite using `[phase_apply, cst]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_exp_phase {P : V → V → ℝ} (h : IsPairing P) (w : V × V) (y : V) :
    ‖Complex.exp (phase h w.2 y + cst P w)‖ = 1 := by
  have e : phase h w.2 y + cst P w = (((-(2 * Real.pi)) * (P y w.2 + P w.1 w.2 / 2) : ℝ) : ℂ) * Complex.I := by
    rw [phase_apply, cst]; push_cast; ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

end GlobalTheory.SchrGrowth

namespace GlobalTheory.SchrGrowth

open GlobalTheory.ArchUniq

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Use `set K₁ := 1 + 2 * Real.pi * ‖pairCLM h‖ with hK₁`. Use `set T := 1 + ‖w‖ with hT`. Use `set S := (Finset.Iic (N, N')).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hS`. Establish `hB0` using `norm_nonneg (pairCLM h)`. Establish `hw0` using `norm_nonneg w`.

Establish `hK1 : 1 ≤ K₁` using `by rw [hK₁]; have := Real.pi_pos; nlinarith`. Establish `hT1 : 1 ≤ T` using `by rw [hT]; linarith`. Establish `hS0 : 0 ≤ S` using `apply_nonneg _ _`. Establish `hKT : 1 ≤ K₁ * T` using `by nlinarith`. Rewrite using `[schrF_eq h]`.

Use `set χ : V → ℂ := fun y => Complex.exp (phase h w.2 y + cst P w) with hχdef`. Establish `hχ : ContDiff ℝ ∞ χ` using `(Complex.contDiff_exp (𝕜 := ℝ)).comp ((phase h w.2).contDiff.add contDiff_const)`. Establish `hτ : ContDiff ℝ ∞ (fun y => f (y + w.1))` using `(f.smooth ⊤).comp (contDiff_id.add contDiff_const)`. Establish `hmul` using `norm_iteratedFDeriv_mul_le (N := ∞) hχ hτ y (n := m) (by exact_mod_cast le_top)`. Establish `hphase : ‖phase h w.2‖ ≤ K₁ * T`.

Use `(norm_phase_le h w.2).trans ?_` and prove the remaining obligations. Establish `hb : ‖w.2‖ ≤ T` using `by rw [hT]; have := norm_snd_le w; linarith`. Establish `: 2 * Real.pi * ‖pairCLM h‖ ≤ K₁` using `by rw [hK₁]; linarith`. Conclude with `mul_le_mul this hb (norm_nonneg _) (by linarith)`. Establish `hy : ‖y‖ ^ k ≤ (1 + ‖y + w.1‖) ^ k * T ^ N`.

Establish `ha : ‖w.1‖ ≤ ‖w‖` using `norm_fst_le w`. Establish `h1 : ‖y‖ ≤ ‖y + w.1‖ + ‖w.1‖`. Use `norm_sub_le (y + w.1) w.1` as an intermediate fact. Simplify using `using this`. Establish `h2 : ‖y‖ ≤ (1 + ‖y + w.1‖) * T`.

Use `norm_nonneg (y + w.1)` as an intermediate fact. Use `norm_nonneg w.1` as an intermediate fact. Rewrite using `[hT]`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.

Establish `hterm : ∀ i ∈ Finset.range (m + 1), ‖y‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ * ‖iteratedFDeriv ℝ (m - i) (fun y => f (y + w.1)) y‖) ≤ (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S))`. Introduce `i hi`. Establish `hi' : i ≤ m` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `e1 : ‖iteratedFDeriv ℝ i χ y‖ ≤ (K₁ * T) ^ N'`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : ‖iteratedFDeriv ℝ (m - i) (fun y => f (y + w.1)) y‖ = ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖`. Rewrite using `[iteratedFDeriv_comp_add_right]`. Establish `e3 : (1 + ‖y + w.1‖) ^ k * ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖ ≤ 2 ^ N * S` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, N')) hk ((Nat.sub_le m i).trans hm) f _`. Rewrite using `[e2]`. Establish `hc0 : (0 : ℝ) ≤ m.choose i` using `Nat.cast_nonneg _`.

Establish `hd0` using `norm_nonneg (iteratedFDeriv ℝ (m - i) f (y + w.1))`. Establish `hx0 : 0 ≤ ‖iteratedFDeriv ℝ i χ y‖` using `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (m.choose i : ℝ) * ((K₁ * T) ^ N' * ((1 + ‖y + w.1‖) ^ k * T ^ N * ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖)) := by gcongr`.

Use `_ = (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N * ((1 + ‖y + w.1‖) ^ k * ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖)) := by ring`. Use `_ ≤ (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := by gcongr`. Establish `hfun : (fun y => Complex.exp (phase h w.2 y + cst P w) * f (y + w.1)) = fun y => χ y * (fun y => f (y + w.1)) y` using `rfl`. Rewrite using `[hfun]`. Establish `hA : 0 ≤ (K₁ * T) ^ N' * T ^ N * (2 ^ N * S)` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `_ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := Finset.sum_le_sum hterm`. Use `_ = 2 ^ m * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := by`. Rewrite using `[← Finset.sum_mul]`.

Establish `: (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m`. Conclude with `Nat.sum_range_choose m` after adjusting the coercions. Rewrite using `[this]`. Use `_ ≤ 2 ^ N' * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := by gcongr`. Evaluate the numerical expressions.

Use `_ = (2 ^ N' * K₁ ^ N' * 2 ^ N) * T ^ (N + N') * S := by`. Rewrite using `[mul_pow, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pointwise_le {P : V → V → ℝ} (h : IsPairing P) (N N' : ℕ) (w : V × V) (f : 𝓢(V, ℂ))
    {k m : ℕ} (hk : k ≤ N) (hm : m ≤ N') (y : V) :
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (schrF P w ⇑f) y‖ ≤
      (2 ^ N' * (1 + 2 * Real.pi * ‖pairCLM h‖) ^ N' * 2 ^ N) * (1 + ‖w‖) ^ (N + N') *
        (Finset.Iic (N, N')).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  set K₁ := 1 + 2 * Real.pi * ‖pairCLM h‖ with hK₁
  set T := 1 + ‖w‖ with hT
  set S := (Finset.Iic (N, N')).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hS
  have hB0 := norm_nonneg (pairCLM h)
  have hw0 := norm_nonneg w
  have hK1 : 1 ≤ K₁ := by rw [hK₁]; have := Real.pi_pos; nlinarith
  have hT1 : 1 ≤ T := by rw [hT]; linarith
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hKT : 1 ≤ K₁ * T := by nlinarith
  rw [schrF_eq h]
  set χ : V → ℂ := fun y => Complex.exp (phase h w.2 y + cst P w) with hχdef
  have hχ : ContDiff ℝ ∞ χ :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp ((phase h w.2).contDiff.add contDiff_const)
  have hτ : ContDiff ℝ ∞ (fun y => f (y + w.1)) := (f.smooth ⊤).comp (contDiff_id.add contDiff_const)
  have hmul := norm_iteratedFDeriv_mul_le (N := ∞) hχ hτ y (n := m) (by exact_mod_cast le_top)
  have hphase : ‖phase h w.2‖ ≤ K₁ * T := by
    refine (norm_phase_le h w.2).trans ?_
    have hb : ‖w.2‖ ≤ T := by rw [hT]; have := norm_snd_le w; linarith
    have : 2 * Real.pi * ‖pairCLM h‖ ≤ K₁ := by rw [hK₁]; linarith
    exact mul_le_mul this hb (norm_nonneg _) (by linarith)
  have hy : ‖y‖ ^ k ≤ (1 + ‖y + w.1‖) ^ k * T ^ N := by
    have ha : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have h1 : ‖y‖ ≤ ‖y + w.1‖ + ‖w.1‖ := by
      have := norm_sub_le (y + w.1) w.1
      simpa using this
    have h2 : ‖y‖ ≤ (1 + ‖y + w.1‖) * T := by
      have := norm_nonneg (y + w.1)
      have := norm_nonneg w.1
      rw [hT]; nlinarith
    calc ‖y‖ ^ k ≤ ((1 + ‖y + w.1‖) * T) ^ k := by gcongr
      _ = (1 + ‖y + w.1‖) ^ k * T ^ k := mul_pow _ _ _
      _ ≤ (1 + ‖y + w.1‖) ^ k * T ^ N := by gcongr
  have hterm : ∀ i ∈ Finset.range (m + 1),
      ‖y‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun y => f (y + w.1)) y‖) ≤
        (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : ‖iteratedFDeriv ℝ i χ y‖ ≤ (K₁ * T) ^ N' := by
      calc ‖iteratedFDeriv ℝ i χ y‖ ≤ ‖Complex.exp (phase h w.2 y + cst P w)‖ * ‖phase h w.2‖ ^ i :=
            norm_iteratedFDeriv_exp_affine_le _ _ i y
        _ = ‖phase h w.2‖ ^ i := by rw [norm_exp_phase, one_mul]
        _ ≤ (K₁ * T) ^ i := by gcongr
        _ ≤ (K₁ * T) ^ N' := pow_le_pow_right₀ hKT (hi'.trans hm)
    have e2 : ‖iteratedFDeriv ℝ (m - i) (fun y => f (y + w.1)) y‖ = ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖ := by
      rw [iteratedFDeriv_comp_add_right]
    have e3 : (1 + ‖y + w.1‖) ^ k * ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖ ≤ 2 ^ N * S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, N')) hk ((Nat.sub_le m i).trans hm) f _
    rw [e2]
    have hc0 : (0 : ℝ) ≤ m.choose i := Nat.cast_nonneg _
    have hd0 := norm_nonneg (iteratedFDeriv ℝ (m - i) f (y + w.1))
    have hx0 : 0 ≤ ‖iteratedFDeriv ℝ i χ y‖ := norm_nonneg _
    calc ‖y‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ * ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖)
        = (m.choose i : ℝ) * (‖iteratedFDeriv ℝ i χ y‖ * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖)) := by
          ring
      _ ≤ (m.choose i : ℝ) * ((K₁ * T) ^ N' * ((1 + ‖y + w.1‖) ^ k * T ^ N *
            ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖)) := by gcongr
      _ = (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N *
            ((1 + ‖y + w.1‖) ^ k * ‖iteratedFDeriv ℝ (m - i) f (y + w.1)‖)) := by ring
      _ ≤ (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := by gcongr
  have hfun : (fun y => Complex.exp (phase h w.2 y + cst P w) * f (y + w.1)) =
      fun y => χ y * (fun y => f (y + w.1)) y := rfl
  rw [hfun]
  have hA : 0 ≤ (K₁ * T) ^ N' * T ^ N * (2 ^ N * S) := by positivity
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y => χ y * (fun y => f (y + w.1)) y) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i χ y‖ * ‖iteratedFDeriv ℝ (m - i) (fun y => f (y + w.1)) y‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (m + 1), ‖y‖ ^ k * ((m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i χ y‖ * ‖iteratedFDeriv ℝ (m - i) (fun y => f (y + w.1)) y‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ m * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
          exact_mod_cast Nat.sum_range_choose m
        rw [this]
    _ ≤ 2 ^ N' * ((K₁ * T) ^ N' * T ^ N * (2 ^ N * S)) := by
        gcongr
        · norm_num
    _ = (2 ^ N' * K₁ ^ N' * 2 ^ N) * T ^ (N + N') * S := by
        rw [mul_pow, pow_add]; ring

/- English proof (translation)
Introduce `V _ _ _ P hP s₀`. Use `⟨s₀.sup Prod.fst + s₀.sup Prod.snd, Finset.Iic (s₀.sup Prod.fst, s₀.sup Prod.snd), 2 ^ (s₀.sup Prod.snd) * (1 + 2 * Real.pi * ‖pairCLM hP‖) ^ (s₀.sup Prod.snd) * 2 ^ (s₀.sup Prod.fst), by positivity, fun w f => ?_⟩` and prove the remaining obligations. Set `g : 𝓢(V, ℂ)` to `{ toFun := schrF P w ⇑f smooth' := by`. Rewrite using `[schrF_eq hP]`. Conclude with `((Complex.contDiff_exp (𝕜 := ℝ)).comp ((phase hP w.2).contDiff.add contDiff_const)).mul ((f.smooth ⊤).comp (contDiff_id.add contDiff_const))`.

Use the proof step `decay' := fun k n => ⟨_, fun y => pointwise_le hP k n w f le_rfl le_rfl y⟩ }`. Use `⟨g, rfl, ?_⟩` and prove the remaining obligations. Use `Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_` and prove the remaining obligations. Use `show SchwartzMap.seminorm ℂ p.1 p.2 g ≤ _`. Conclude with `SchwartzMap.seminorm_le_bound ℂ p.1 p.2 g (by positivity) fun y => pointwise_le hP _ _ w f (Finset.le_sup (f := Prod.fst) hp) (Finset.le_sup (f := Prod.snd) hp) y`.
-/
theorem schrF_seminorm_growth : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), IsPairing P → ∀ (s₀ : Finset (ℕ × ℕ)), ∃ (M : ℕ) (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (w : V × V) (h : 𝓢(V, ℂ)), ∃ g : 𝓢(V, ℂ), ⇑g = schrF P w ⇑h ∧
        (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  intro V _ _ _ P hP s₀
  refine ⟨s₀.sup Prod.fst + s₀.sup Prod.snd, Finset.Iic (s₀.sup Prod.fst, s₀.sup Prod.snd),
    2 ^ (s₀.sup Prod.snd) * (1 + 2 * Real.pi * ‖pairCLM hP‖) ^ (s₀.sup Prod.snd) * 2 ^ (s₀.sup Prod.fst),
    by positivity, fun w f => ?_⟩
  let g : 𝓢(V, ℂ) :=
    { toFun := schrF P w ⇑f
      smooth' := by
        rw [schrF_eq hP]
        exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp ((phase hP w.2).contDiff.add contDiff_const)).mul
          ((f.smooth ⊤).comp (contDiff_id.add contDiff_const))
      decay' := fun k n => ⟨_, fun y => pointwise_le hP k n w f le_rfl le_rfl y⟩ }
  refine ⟨g, rfl, ?_⟩
  refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
  show SchwartzMap.seminorm ℂ p.1 p.2 g ≤ _
  exact SchwartzMap.seminorm_le_bound ℂ p.1 p.2 g (by positivity) fun y =>
    pointwise_le hP _ _ w f (Finset.le_sup (f := Prod.fst) hp) (Finset.le_sup (f := Prod.snd) hp) y

end GlobalTheory.SchrGrowth
