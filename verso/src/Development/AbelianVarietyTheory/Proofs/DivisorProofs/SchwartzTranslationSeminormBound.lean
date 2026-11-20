import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

open scoped SchwartzMap NNReal ContDiff
open GlobalTheory.Published.Metaplectic

namespace GlobalTheory.SchwartzTranslateLip

/- English proof (translation)
Use `set B := 2 ^ K * ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f with hB`. Establish `hB0 : 0 ≤ B` using `by rw [hB]; positivity`. Use `SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_` and prove the remaining obligations. Establish `c0 : ContDiff ℝ ∞ f` using `f.smooth'`. Establish `hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`.

Establish `ct : ContDiff ℝ ∞ (fun z => f (z + a))` using `c0.comp (contDiff_id.add contDiff_const)`. Establish `efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) = (fun z => f (z + a)) - ⇑f`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Establish `eit : iteratedFDeriv ℝ n ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) x = iteratedFDeriv ℝ n f (x + a) - iteratedFDeriv ℝ n f x`.

Rewrite using `[efun, iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt, iteratedFDeriv_comp_add_right]`. Establish `hd : Differentiable ℝ (iteratedFDeriv ℝ n f)` using `c0.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)`. Establish `hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a)) (‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a) s`. Introduce `s`. Establish `hl : HasDerivAt (fun s : ℝ => x + s • a) a s`.

Simplify using `using ((hasDerivAt_id s).smul_const a).const_add x`. Conclude with `((hd (x + s • a)).hasFDerivAt.comp_hasDerivAt s hl).const_smul (‖x‖ ^ k)`. Establish `hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a‖ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B`. Introduce `s hs`. Use `set y := x + s • a with hy`.

Establish `hsa : ‖s • a‖ ≤ ‖a‖`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) hs.2`. Establish `hx : ‖x‖ ≤ ‖y‖ + ‖a‖`. Establish `h4` using `norm_sub_le y (s • a)`.

Rewrite `h4` using `[show y - s • a = x by simp [hy]]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx2 : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖y‖)`. Use polynomial arithmetic with `[norm_nonneg a, norm_nonneg y, mul_nonneg (norm_nonneg a) (norm_nonneg y)]`. Establish `ha1 : 1 ≤ 1 + ‖a‖` using `by linarith [norm_nonneg a]`.

Establish `hxk : ‖x‖ ^ k ≤ (1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k`. Combine the equalities or inequalities in the displayed calculation. Establish `hop : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖`. Rewrite using `[← norm_fderiv_iteratedFDeriv]`. Conclude with `(fderiv ℝ (iteratedFDeriv ℝ n f) y).le_opNorm a`.

Establish `hS` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, N + 1)) (k := k) (n := n + 1) hk (by simp; omega) f y`. Rewrite using `[norm_smul, Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `key` using `(convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (x := 0) (y := 1) (fun s _ => (hderiv s).hasDerivWithinAt) hbound (by simp) (by simp)`. Simplify using `only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one] at key`.

Rewrite `key` using `[← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]`. Rewrite using `[eit]`. Conclude with `key`.
-/
theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K N k n : ℕ) (hk : k ≤ K) (hn : n ≤ N) (a : V) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K *
        ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) := by
  set B := 2 ^ K * ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) = (fun z => f (z + a)) - ⇑f := by
    funext z; simp
  have eit : iteratedFDeriv ℝ n ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) x
      = iteratedFDeriv ℝ n f (x + a) - iteratedFDeriv ℝ n f x := by
    rw [efun, iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    c0.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
      (‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => x + s • a) a s := by
      simpa using ((hasDerivAt_id s).smul_const a).const_add x
    exact ((hd (x + s • a)).hasFDerivAt.comp_hasDerivAt s hl).const_smul (‖x‖ ^ k)
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a‖ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by
    intro s hs
    set y := x + s • a with hy
    have hsa : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    have hx : ‖x‖ ≤ ‖y‖ + ‖a‖ := by
      have h4 := norm_sub_le y (s • a)
      rw [show y - s • a = x by simp [hy]] at h4
      linarith
    have hx2 : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg a, norm_nonneg y, mul_nonneg (norm_nonneg a) (norm_nonneg y)]
    have ha1 : 1 ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    have hxk : ‖x‖ ^ k ≤ (1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k := by
      calc ‖x‖ ^ k ≤ ((1 + ‖a‖) * (1 + ‖y‖)) ^ k := pow_le_pow_left₀ (norm_nonneg _) hx2 k
        _ = (1 + ‖a‖) ^ k * (1 + ‖y‖) ^ k := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have hop : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖ := by
      rw [← norm_fderiv_iteratedFDeriv]; exact (fderiv ℝ (iteratedFDeriv ℝ n f) y).le_opNorm a
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, N + 1)) (k := k)
      (n := n + 1) hk (by simp; omega) f y
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖x‖ ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖
        ≤ ((1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k) * (‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖) := by gcongr
      _ = ‖a‖ * (1 + ‖a‖) ^ K * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f y‖) := by ring
      _ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by gcongr
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := 1) (fun s _ => (hderiv s).hasDerivWithinAt) hbound (by simp) (by simp)
  simp only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one] at key
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key

/- English proof (translation)
Introduce `V _ _ p hp`. Take `⟨s, C, -, hC⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp`. Use `set K := s.sup Prod.fst`. Use `set N := s.sup Prod.snd`. Use `⟨(C * 2 ^ K) • (Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2, K, ?_, fun a f => ?_⟩` and prove the remaining obligations.

Establish `h : Continuous ⇑((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2)` using `Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i`. Rewrite using `[Seminorm.coe_smul]`. Conclude with `h.const_smul _`. Use `set S := ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f`. Establish `hS0 : 0 ≤ S` using `apply_nonneg _ _`.

Establish `h1 : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S)`. Use `Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_` and prove the remaining obligations. Conclude with `seminorm_translate_sub_le K N i.1 i.2 (Finset.le_sup (f := Prod.fst) hi) (Finset.le_sup (f := Prod.snd) hi) a f`. Establish `h2` using `hC (SchwartzMap.compSubConstCLM ℂ (-a) f - f)`. Rewrite `h2` using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`.

Rewrite using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem translate_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
      p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set K := s.sup Prod.fst
  set N := s.sup Prod.snd
  refine ⟨(C * 2 ^ K) • (Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2,
    K, ?_, fun a f => ?_⟩
  · have h : Continuous ⇑((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) :=
      Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
    rw [Seminorm.coe_smul]
    exact h.const_smul _
  set S := ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have h1 : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S) := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    exact seminorm_translate_sub_le K N i.1 i.2 (Finset.le_sup (f := Prod.fst) hi)
      (Finset.le_sup (f := Prod.snd) hi) a f
  have h2 := hC (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  push_cast
  calc p (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f) := h2
    _ ≤ (C : ℝ) * (‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S)) := by gcongr
    _ = _ := by ring

end GlobalTheory.SchwartzTranslateLip
