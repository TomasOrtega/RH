import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.PhaseLipschitz

def psi (k : ℝ) : ℝ → ℂ := fun t =>
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) - 1

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [psi, Function.comp_apply, eChar_apply, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eChar_sub_one_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (k : ℝ) :
    (fun y => eChar (L y + k) - 1) = psi k ∘ ⇑L := by
  funext y
  simp only [psi, Function.comp_apply, eChar_apply, ← Complex.exp_add]
  congr 2; push_cast; ring

/- English proof (translation)
Establish `ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ))` using `Complex.ofRealCLM.contDiff`. Unfold `psi`. Use `fun_prop`.
-/
theorem contDiff_psi (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi k) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold psi; fun_prop

/- English proof (translation)
Establish `e : psi k t = Complex.exp (Complex.I * ((2 * Real.pi * (t + k) : ℝ) : ℂ)) - 1`. Simplify using `only [psi, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]`.
-/
theorem norm_psi_le (k t : ℝ) : ‖psi k t‖ ≤ 2 * Real.pi * |t + k| := by
  have e : psi k t = Complex.exp (Complex.I * ((2 * Real.pi * (t + k) : ℝ) : ℂ)) - 1 := by
    simp only [psi, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

/- English proof (translation)
Rewrite using `[iteratedDeriv_succ']`. Establish `hd : deriv (psi k) = deriv (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))`. Unfold `psi`. Conclude with `deriv_sub_const_fun _`. Rewrite using `[hd, ← iteratedDeriv_succ', GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp]`.
-/
theorem iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (psi k) = fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * (2 * Real.pi * Complex.I) ^ (j + 1) *
        Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  rw [iteratedDeriv_succ']
  have hd : deriv (psi k) = deriv (fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) := by
    unfold psi; exact deriv_sub_const_fun _
  rw [hd, ← iteratedDeriv_succ', GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp]

/- English proof (translation)
Rewrite using `[iteratedDeriv_psi_succ]`. Establish `h1 : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1`. Introduce `r`. Rewrite using `[show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]`. Simplify using `only [norm_mul, norm_pow, h1]`.

Simplify using `[abs_of_pos Real.pi_pos]`.
-/
theorem norm_iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv (j + 1) (psi k) t‖ = (2 * Real.pi) ^ (j + 1) := by
  rw [iteratedDeriv_psi_succ]
  have h1 : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  simp only [norm_mul, norm_pow, h1]
  simp [abs_of_pos Real.pi_pos]

/- English proof (translation)
Establish `hpi : (1 : ℝ) ≤ 2 * Real.pi` using `by linarith [Real.pi_gt_three]`. Establish `hL` using `norm_nonneg L`. Establish `hx` using `norm_nonneg x`. Establish `hk` using `abs_nonneg k`. Establish `h1N : (1 : ℝ) ≤ (1 + ‖L‖) ^ N` using `one_le_pow₀ (by linarith)`.

Break down `i with _ | j` into its components or cases. Rewrite using `[norm_iteratedFDeriv_zero, Function.comp_apply]`. Use `(norm_psi_le k (L x)).trans ?_` and prove the remaining obligations. Establish `h2 : |L x + k| ≤ (‖L‖ + |k|) * (1 + ‖x‖)`. Establish `h3 : |L x| ≤ ‖L‖ * ‖x‖` using `by simpa [Real.norm_eq_abs] using L.le_opNorm x`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 2 * Real.pi ≤ (2 * Real.pi) ^ (N + 1)` using `le_self_pow₀ hpi (by omega)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one]`. Rewrite using `[← mul_assoc]`.

Use `gcongr`. Use `_ ≤ _ := by gcongr`. Rewrite using `[L.iteratedFDeriv_comp_right (contDiff_psi k) x (i := j + 1) (by exact_mod_cast le_top)]`. Establish `h5 : (2 * Real.pi) ^ (j + 1) ≤ (2 * Real.pi) ^ (N + 1)` using `pow_le_pow_right₀ hpi (by omega)`. Establish `h6 : ‖L‖ ^ (j + 1) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N`.

Rewrite using `[pow_succ']`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_psi_succ]`. Simplify using the standard rewrite rules. Use `_ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * 1 := by`. Rewrite using `[mul_one]`. Use `gcongr`.

Use `_ ≤ _ := by gcongr; linarith`.
-/
theorem norm_iteratedFDeriv_psi_comp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) {N i : ℕ} (hi : i ≤ N) (x : V) :
    ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ ≤
      (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * (1 + ‖x‖) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL := norm_nonneg L
  have hx := norm_nonneg x
  have hk := abs_nonneg k
  have h1N : (1 : ℝ) ≤ (1 + ‖L‖) ^ N := one_le_pow₀ (by linarith)
  rcases i with _ | j
  · rw [norm_iteratedFDeriv_zero, Function.comp_apply]
    refine (norm_psi_le k (L x)).trans ?_
    have h2 : |L x + k| ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by
      have h3 : |L x| ≤ ‖L‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using L.le_opNorm x
      calc |L x + k| ≤ |L x| + |k| := abs_add_le _ _
        _ ≤ ‖L‖ * ‖x‖ + |k| := by linarith
        _ ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by nlinarith
    have h4 : 2 * Real.pi ≤ (2 * Real.pi) ^ (N + 1) := le_self_pow₀ hpi (by omega)
    calc 2 * Real.pi * |L x + k| ≤ 2 * Real.pi * ((‖L‖ + |k|) * (1 + ‖x‖)) := by gcongr
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * 1) * (1 + ‖x‖) := by
          rw [mul_one]; rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr
  · rw [L.iteratedFDeriv_comp_right (contDiff_psi k) x (i := j + 1) (by exact_mod_cast le_top)]
    have h5 : (2 * Real.pi) ^ (j + 1) ≤ (2 * Real.pi) ^ (N + 1) := pow_le_pow_right₀ hpi (by omega)
    have h6 : ‖L‖ ^ (j + 1) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by
      rw [pow_succ']
      gcongr
      · linarith
      · calc ‖L‖ ^ j ≤ (1 + ‖L‖) ^ j := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ N := pow_le_pow_right₀ (by linarith) (by omega)
    calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (psi k) (L x)‖ * ∏ _j : Fin (j + 1), ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = (2 * Real.pi) ^ (j + 1) * ‖L‖ ^ (j + 1) := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_psi_succ]; simp
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * 1 := by
          rw [mul_one]; gcongr
      _ ≤ _ := by gcongr; linarith

/- English proof (translation)
The claim follows from `hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))`.
-/
theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) : Function.HasTemperateGrowth (fun y => eChar (L y + k)) :=
  hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L k), smul_eq_mul, ← congrFun (eChar_sub_one_eq L k) y]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coe_smulLeft_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    ⇑(SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) = fun y => (psi k ∘ ⇑L) y * f y := by
  funext y
  rw [SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L k), smul_eq_mul,
    ← congrFun (eChar_sub_one_eq L k) y]
  ring

/- English proof (translation)
Use `set S := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hS`. Use `set P := (‖L‖ + |k|) * (1 + ‖L‖) ^ N with hP`. Establish `hS0 : 0 ≤ S` using `apply_nonneg _ _`. Establish `hP0 : 0 ≤ P` using `by positivity`. Use `SchwartzMap.seminorm_le_bound ℂ a n _ (by positivity) fun x => ?_` and prove the remaining obligations.

Rewrite using `[coe_smulLeft_sub]`. Establish `hmul` using `norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) ((contDiff_psi k).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)`. Establish `hx` using `norm_nonneg x`. Establish `hf : ∀ j ≤ N, ‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ 2 ^ (A + 1) * S`. Introduce `j hj`.

Establish `h` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (A + 1, N)) (k := a + 1) (n := j) (by simp; omega) hj f x`. Establish `h' : ‖x‖ ^ a * (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (a + 1)`. Rewrite using `[pow_succ]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Establish `hterm : ∀ i ∈ Finset.range (n + 1), ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)`. Introduce `i hi`. Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `h1` using `norm_iteratedFDeriv_psi_comp_le L k (N := N) (i := i) (by omega) x`.

Establish `h2` using `hf (n - i) (by omega)`. Establish `hc : (n.choose i : ℝ) ≤ 2 ^ N` using `(by exact_mod_cast Nat.choose_le_two_pow n i : (n.choose i : ℝ) ≤ 2 ^ n).trans (pow_le_pow_right₀ (by norm_num) hn)`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Use `_ ≤ ∑ _i ∈ Finset.range (n + 1), 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) := Finset.sum_le_sum hterm`. Use `_ = ((n : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by simp`. Use `_ ≤ ((N : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by gcongr`. Use `_ = _ := by ring`.
-/
theorem seminorm_smulLeft_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A N a n : ℕ} (ha : a ≤ A) (hn : n ≤ N) (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ a n (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤
      ((N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1)) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) *
        (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  set S := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hS
  set P := (‖L‖ + |k|) * (1 + ‖L‖) ^ N with hP
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hP0 : 0 ≤ P := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ a n _ (by positivity) fun x => ?_
  rw [coe_smulLeft_sub]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_psi k).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx := norm_nonneg x
  have hf : ∀ j ≤ N, ‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ 2 ^ (A + 1) * S := by
    intro j hj
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (A + 1, N)) (k := a + 1) (n := j)
      (by simp; omega) hj f x
    have h' : ‖x‖ ^ a * (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (a + 1) := by
      rw [pow_succ]; gcongr; linarith
    calc _ ≤ (1 + ‖x‖) ^ (a + 1) * ‖iteratedFDeriv ℝ j f x‖ := by gcongr
      _ ≤ _ := h
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_psi_comp_le L k (N := N) (i := i) (by omega) x
    have h2 := hf (n - i) (by omega)
    have hc : (n.choose i : ℝ) ≤ 2 ^ N :=
      (by exact_mod_cast Nat.choose_le_two_pow n i : (n.choose i : ℝ) ≤ 2 ^ n).trans
        (pow_le_pow_right₀ (by norm_num) hn)
    calc ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        ≤ ‖x‖ ^ a * ((2 ^ N : ℝ) * ((2 * Real.pi) ^ (N + 1) * P * (1 + ‖x‖)) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) *
          (‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ _ := by gcongr
  calc ‖x‖ ^ a * ‖iteratedFDeriv ℝ n (fun y => (psi k ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ a * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ a * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by simp
    _ ≤ ((N : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by
        gcongr
    _ = _ := by ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sup_empty]`. Conclude with `continuous_const`. Consider the case `insert i s _ ih`.

Rewrite using `[Finset.sup_insert]`. Conclude with `((hp i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm`.
-/
theorem continuous_finset_sup_seminorm {E ι : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {p : ι → Seminorm ℂ E} (hp : ∀ i, Continuous (p i)) (s : Finset ι) :
    Continuous ⇑(s.sup p : Seminorm ℂ E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact ((hp i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm

/- English proof (translation)
Introduce `V _ _ p hp`. Take `⟨s, C, -, hC⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp`. Use `set A := s.sup Prod.fst with hA`. Use `set N := s.sup Prod.snd with hN`. Use `set K : ℝ := (N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1) with hK`.

Establish `hK0 : 0 ≤ K` using `by positivity`. Use `set Q : Seminorm ℂ (SchwartzMap V ℂ) := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) with hQ`. Use `⟨(C * ⟨K, hK0⟩ : NNReal) • Q, N, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_finset_sup_seminorm (fun i => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i) _).const_smul _`. Introduce `L k f set g := SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f`.

Establish `hP0 : 0 ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N` using `by positivity`. Establish `hQ0 : 0 ≤ Q f` using `apply_nonneg _ _`. Establish `hs : (s.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f`. Use `Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_` and prove the remaining obligations. Conclude with `seminorm_smulLeft_sub_le (Finset.le_sup (f := Prod.fst) hi) (Finset.le_sup (f := Prod.snd) hi) L k f`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`. Use `_ ≤ (C : ℝ) * (K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f) := by gcongr`. Use `_ = (‖L‖ + |k|) * (1 + ‖L‖) ^ N * (((C * ⟨K, hK0⟩ : NNReal) • Q) f) := by`. Rewrite using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`.

Express the relevant statement in the definitionally equal form `(C : ℝ) * _ = _ * (((C : ℝ) * K) * Q f)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem seminorm_smulLeft_eChar_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
      p (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f) ≤
        (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set A := s.sup Prod.fst with hA
  set N := s.sup Prod.snd with hN
  set K : ℝ := (N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set Q : Seminorm ℂ (SchwartzMap V ℂ) :=
    (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) with hQ
  refine ⟨(C * ⟨K, hK0⟩ : NNReal) • Q, N, ?_, ?_⟩
  · exact (continuous_finset_sup_seminorm
      (fun i => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i) _).const_smul _
  · intro L k f
    set g := SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f
    have hP0 : 0 ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by positivity
    have hQ0 : 0 ≤ Q f := apply_nonneg _ _
    have hs : (s.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      exact seminorm_smulLeft_sub_le (Finset.le_sup (f := Prod.fst) hi) (Finset.le_sup (f := Prod.snd) hi) L k f
    calc p g ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) g := hC g
      _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) g := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
      _ ≤ (C : ℝ) * (K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f) := by gcongr
      _ = (‖L‖ + |k|) * (1 + ‖L‖) ^ N * (((C * ⟨K, hK0⟩ : NNReal) • Q) f) := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
          change (C : ℝ) * _ = _ * (((C : ℝ) * K) * Q f)
          ring

end GlobalTheory.PhaseLipschitz
