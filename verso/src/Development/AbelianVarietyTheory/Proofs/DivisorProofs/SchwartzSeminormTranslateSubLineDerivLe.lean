import Mathlib

open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzTranslate

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `F _ _ g hg x m`. Simplify using `only [iteratedFDeriv_zero_apply]`. Consider the case `succ n ih`.

Introduce `F _ _ g hg x m`. Establish `hg1 : ContDiff ℝ ∞ (fderiv ℝ g)` using `hg.fderiv_right (by simp)`. Establish `hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (fderiv ℝ g))` using `hg1.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)`. Establish `hsym : (fun y => fderiv ℝ (fun z => fderiv ℝ g z a) y) = fun y => fderiv ℝ (fderiv ℝ g) y a`. Use function extensionality and compare the values at `y`.

Use extensionality with `w`. Rewrite using `[fderiv_clm_apply ((hg1.differentiable (by simp)) y) (differentiableAt_const _)]`. Simplify using the standard rewrite rules. Establish `h2le : minSmoothness ℝ 2 ≤ ∞` using `by simp; exact WithTop.coe_le_coe.mpr le_top`. Conclude with `(ContDiffAt.isSymmSndFDerivAt (hg.contDiffAt (x := y)) h2le) w a`.

Repeatedly rewrite using `[iteratedFDeriv_succ_apply_right]`. Rewrite using `[fderiv_clm_apply ((hdiff x).continuousMultilinear_apply_const _) (differentiableAt_const _)]`. Simplify using the standard rewrite rules. Rewrite using `[ih (fderiv ℝ g) hg1 x (Fin.init m), hsym]`.
-/
private theorem fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (a : V) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : V → F), ContDiff ℝ ∞ g →
      ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m := by
  induction n with
  | zero =>
    intro F _ _ g hg x m
    simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro F _ _ g hg x m
    have hg1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (fderiv ℝ g)) :=
      hg1.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
    have hsym : (fun y => fderiv ℝ (fun z => fderiv ℝ g z a) y)
        = fun y => fderiv ℝ (fderiv ℝ g) y a := by
      funext y
      ext w
      rw [fderiv_clm_apply ((hg1.differentiable (by simp)) y) (differentiableAt_const _)]
      simp
      have h2le : minSmoothness ℝ 2 ≤ ∞ := by simp; exact WithTop.coe_le_coe.mpr le_top
      exact (ContDiffAt.isSymmSndFDerivAt (hg.contDiffAt (x := y)) h2le) w a
    simp_rw [iteratedFDeriv_succ_apply_right]
    rw [fderiv_clm_apply ((hdiff x).continuousMultilinear_apply_const _) (differentiableAt_const _)]
    simp
    rw [ih (fderiv ℝ g) hg1 x (Fin.init m), hsym]

/- English proof (translation)
Introduce `g hg x m` and use `fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv a n g hg x m`.
-/
theorem fderiv_iteratedFDeriv_apply_comm {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) :
    ∀ (g : V → F), ContDiff ℝ ∞ g → ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m :=
  fun g hg x m => fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv a n g hg x m

/- English proof (translation)
Establish `hline : HasDerivAt (fun s : ℝ => x + s • a) a s`. Simplify using `using ((hasDerivAt_id s).smul_const a).const_add x`. Establish `hd : Differentiable ℝ (iteratedFDeriv ℝ n g)` using `hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)`. Establish `key : fderiv ℝ (iteratedFDeriv ℝ n g) (x + s • a) a = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a)`. Use extensionality with `m`.

Rewrite using `[← fderiv_continuousMultilinear_apply_const_apply (hd _)]`. Conclude with `fderiv_iteratedFDeriv_apply_comm a n g hg _ m`. Rewrite using `[← key]`. Conclude with `(hd _).hasFDerivAt.comp_hasDerivAt s hline`.
-/
theorem hasDerivAt_iteratedFDeriv_line {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) (g : V → F) (hg : ContDiff ℝ ∞ g)
    (x : V) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • a))
      (iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a)) s := by
  have hline : HasDerivAt (fun s : ℝ => x + s • a) a s := by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
  have key : fderiv ℝ (iteratedFDeriv ℝ n g) (x + s • a) a
      = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a) := by
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply (hd _)]
    exact fderiv_iteratedFDeriv_apply_comm a n g hg _ m
  rw [← key]
  exact (hd _).hasFDerivAt.comp_hasDerivAt s hline

/- English proof (translation)
Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 0 (by simp))`. Establish `hd1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ' s - φ' 0‖ ≤ M * |s|`. Introduce `s hs`. Establish `h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1` using `by norm_num`. Use `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'') (s := Set.Icc (-1) 1) (fun x _ => (h2 x).hasDerivWithinAt) (fun x hx => hM x (abs_le.mpr hx)) (convex_Icc _ _) h0 hs` as an intermediate fact.

Simplify `this` using `[Real.norm_eq_abs]`. Establish `hψ : ∀ s, HasDerivAt (fun s => φ s - s • φ' 0) (φ' s - φ' 0) s`. Introduce `s`. Apply the tactic sequence `convert (h1 s).sub ((hasDerivAt_id s).smul_const (φ' 0)) using 1 <;> first | rfl | simp`. Establish `ht' : t ∈ Set.Icc (-|t|) |t|` using `⟨neg_abs_le t, le_abs_self t⟩`.

Establish `h0' : (0 : ℝ) ∈ Set.Icc (-|t|) |t|` using `⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩`. Establish `hbound : ∀ x ∈ Set.Icc (-|t|) |t|, ‖φ' x - φ' 0‖ ≤ M * |t|`. Introduce `x hx`. Establish `hx1 : |x| ≤ |t|` using `abs_le.mpr hx`. Conclude with `(hd1 x (abs_le.mp (hx1.trans ht))).trans (mul_le_mul_of_nonneg_left hx1 hM0)`.

Establish `key` using `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => φ s - s • φ' 0) (f' := fun s => φ' s - φ' 0) (fun x _ => (hψ x).hasDerivWithinAt) hbound (convex_Icc _ _) h0' ht'`. Establish `e : φ t - φ 0 - t • φ' 0 = (φ t - t • φ' 0) - (φ 0 - (0 : ℝ) • φ' 0)`. Rewrite using `[zero_smul, sub_zero, sub_right_comm]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem taylor_two {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (φ φ' φ'' : ℝ → G)
    (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) (M : ℝ)
    (hM : ∀ s, |s| ≤ 1 → ‖φ'' s‖ ≤ M) (t : ℝ) (ht : |t| ≤ 1) :
    ‖φ t - φ 0 - t • φ' 0‖ ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hd1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ' s - φ' 0‖ ≤ M * |s| := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'')
      (s := Set.Icc (-1) 1) (fun x _ => (h2 x).hasDerivWithinAt)
      (fun x hx => hM x (abs_le.mpr hx)) (convex_Icc _ _) h0 hs
    simpa [Real.norm_eq_abs] using this
  have hψ : ∀ s, HasDerivAt (fun s => φ s - s • φ' 0) (φ' s - φ' 0) s := by
    intro s
    convert (h1 s).sub ((hasDerivAt_id s).smul_const (φ' 0)) using 1 <;> first | rfl | simp
  have ht' : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  have h0' : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have hbound : ∀ x ∈ Set.Icc (-|t|) |t|, ‖φ' x - φ' 0‖ ≤ M * |t| := by
    intro x hx
    have hx1 : |x| ≤ |t| := abs_le.mpr hx
    exact (hd1 x (abs_le.mp (hx1.trans ht))).trans (mul_le_mul_of_nonneg_left hx1 hM0)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => φ s - s • φ' 0) (f' := fun s => φ' s - φ' 0)
    (fun x _ => (hψ x).hasDerivWithinAt) hbound (convex_Icc _ _) h0' ht'
  have e : φ t - φ 0 - t • φ' 0 = (φ t - t • φ' 0) - (φ 0 - (0 : ℝ) • φ' 0) := by
    rw [zero_smul, sub_zero, sub_right_comm]
  rw [e]
  calc _ ≤ M * |t| * ‖t - 0‖ := key
    _ = M * t ^ 2 := by rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, sq]

/- English proof (translation)
Use `set f1 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1def`. Use `set f2 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2def`. Establish `hf1 : (⇑f1 : V → ℂ) = fun y => fderiv ℝ f y a` using `rfl`. Establish `hf2 : (⇑f2 : V → ℂ) = fun y => fderiv ℝ f1 y a` using `rfl`. Establish `hsm : ∀ g : 𝓢(V, ℂ), ContDiff ℝ ∞ ⇑g` using `fun g => g.smooth ⊤`.

Establish `hsmn : ∀ g : 𝓢(V, ℂ), ContDiff ℝ n ⇑g` using `fun g => (g.smooth ⊤).of_le (mod_cast le_top)`. Take `⟨S, hS⟩ : ∃ S : ℝ, S = (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f2` from `⟨_, rfl⟩`. Establish `hL : ∀ y, (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ n f2 y‖ ≤ 2 ^ k * S` using `fun y => by`. Rewrite using `[hS]`. Conclude with `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl le_rfl f2 y`.

Establish `hS0 : 0 ≤ 2 ^ k * S` using `le_trans (by positivity) (hL 0)`. Use `⟨(1 + ‖a‖) ^ k * (2 ^ k * S), fun t ht => ?_⟩` and prove the remaining obligations. Establish `hC0 : 0 ≤ (1 + ‖a‖) ^ k * (2 ^ k * S)` using `mul_nonneg (by positivity) hS0`. Use `SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg hC0 (sq_nonneg t)) fun x => ?_` and prove the remaining obligations. Establish `hcoe : (⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) : V → ℂ) = (fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1`.

Use function extensionality and compare the values at `y`. Simplify using `[sub_neg_eq_add]`. Establish `hshift : ContDiff ℝ n (fun y => f (y + t • a))` using `(hsmn f).comp (contDiff_id.add contDiff_const)`. Establish `hD : iteratedFDeriv ℝ n ((fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1) x = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x - (t : ℂ) • iteratedFDeriv ℝ n f1 x`. Rewrite using `[iteratedFDeriv_sub_apply, iteratedFDeriv_sub_apply, iteratedFDeriv_const_smul_apply, iteratedFDeriv_comp_add_right]`.

Apply the tactic sequence `all_goals first`. Consider the case `exact hshift.contDiffAt`. Consider the case `exact (hsmn f).contDiffAt`. Consider the case `exact (hsmn f1).contDiffAt`. Consider the case `exact (hshift.sub (hsmn f)).contDiffAt`.

Consider the case `exact ((hsmn f1).const_smul (t : ℂ)).contDiffAt`. Establish `hre : (t : ℂ) • iteratedFDeriv ℝ n f1 x = t • iteratedFDeriv ℝ n f1 x`. Use extensionality with `m`. Simplify using `[Complex.real_smul]`. Rewrite using `[hcoe, hD, hre]`.

Take `⟨c, hc⟩ : ∃ c : ℝ, c = ‖x‖ ^ k` from `⟨_, rfl⟩`. Rewrite using `[← hc]`. Establish `hc0 : 0 ≤ c` using `by rw [hc]; positivity`. Establish `hdf : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a)) (c • iteratedFDeriv ℝ n f1 (x + s • a)) s`. Introduce `s`.

Use `hasDerivAt_iteratedFDeriv_line a n f (hsm f) x s` as an intermediate fact. Rewrite `this` using `[← hf1]`. Conclude with `this.const_smul c`. Establish `hdf1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a)) (c • iteratedFDeriv ℝ n f2 (x + s • a)) s`. Introduce `s`.

Use `hasDerivAt_iteratedFDeriv_line a n f1 (hsm f1) x s` as an intermediate fact. Rewrite `this` using `[← hf2]`. Conclude with `this.const_smul c`. Establish `hbd : ∀ s : ℝ, |s| ≤ 1 → ‖c • iteratedFDeriv ℝ n f2 (x + s • a)‖ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S)`. Introduce `s hs`.

Establish `h2 : ‖s • a‖ ≤ ‖a‖`. Rewrite using `[norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) hs`. Establish `hxy : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x + s • a‖)`. Establish `h3 : ‖x‖ ≤ ‖x + s • a‖ + ‖s • a‖`.

Use `norm_sub_le (x + s • a) (s • a)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Use polynomial arithmetic with `[norm_nonneg (x + s • a), norm_nonneg a]`. Establish `hpow : c ≤ (1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k`. Rewrite using `[hc, ← mul_pow]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) hxy k`. Rewrite using `[norm_smul, Real.norm_of_nonneg hc0]`. Combine the equalities or inequalities in the displayed calculation. Establish `hT` using `taylor_two (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a)) (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a)) (fun s : ℝ => c • iteratedFDeriv ℝ n f2 (x + s • a)) hdf hdf1 _ hbd t ht`. Simplify using `only [zero_smul, add_zero] at hT`.

Establish `e : c • iteratedFDeriv ℝ n f (x + t • a) - c • iteratedFDeriv ℝ n f x - t • c • iteratedFDeriv ℝ n f1 x = c • (iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x - t • iteratedFDeriv ℝ n f1 x)`. Rewrite using `[smul_sub, smul_sub, smul_comm t c]`. Rewrite `hT` using `[e, norm_smul, Real.norm_of_nonneg hc0]`. Conclude with `hT`.
-/
theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (f : 𝓢(V, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  set f1 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1def
  set f2 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2def
  have hf1 : (⇑f1 : V → ℂ) = fun y => fderiv ℝ f y a := rfl
  have hf2 : (⇑f2 : V → ℂ) = fun y => fderiv ℝ f1 y a := rfl
  have hsm : ∀ g : 𝓢(V, ℂ), ContDiff ℝ ∞ ⇑g := fun g => g.smooth ⊤
  have hsmn : ∀ g : 𝓢(V, ℂ), ContDiff ℝ n ⇑g := fun g => (g.smooth ⊤).of_le (mod_cast le_top)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f2 :=
    ⟨_, rfl⟩
  have hL : ∀ y, (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ n f2 y‖ ≤ 2 ^ k * S := fun y => by
    rw [hS]; exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl le_rfl f2 y
  have hS0 : 0 ≤ 2 ^ k * S := le_trans (by positivity) (hL 0)
  refine ⟨(1 + ‖a‖) ^ k * (2 ^ k * S), fun t ht => ?_⟩
  have hC0 : 0 ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_nonneg (by positivity) hS0
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg hC0 (sq_nonneg t)) fun x => ?_
  have hcoe : (⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) : V → ℂ)
      = (fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1 := by
    funext y; simp [sub_neg_eq_add]
  have hshift : ContDiff ℝ n (fun y => f (y + t • a)) :=
    (hsmn f).comp (contDiff_id.add contDiff_const)
  have hD : iteratedFDeriv ℝ n ((fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1) x
      = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - (t : ℂ) • iteratedFDeriv ℝ n f1 x := by
    rw [iteratedFDeriv_sub_apply, iteratedFDeriv_sub_apply, iteratedFDeriv_const_smul_apply,
      iteratedFDeriv_comp_add_right]
    all_goals first
      | exact hshift.contDiffAt
      | exact (hsmn f).contDiffAt
      | exact (hsmn f1).contDiffAt
      | exact (hshift.sub (hsmn f)).contDiffAt
      | exact ((hsmn f1).const_smul (t : ℂ)).contDiffAt
  have hre : (t : ℂ) • iteratedFDeriv ℝ n f1 x = t • iteratedFDeriv ℝ n f1 x := by
    ext m; simp [Complex.real_smul]
  rw [hcoe, hD, hre]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖x‖ ^ k := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hdf : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
      (c • iteratedFDeriv ℝ n f1 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f (hsm f) x s
    rw [← hf1] at this
    exact this.const_smul c
  have hdf1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
      (c • iteratedFDeriv ℝ n f2 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f1 (hsm f1) x s
    rw [← hf2] at this
    exact this.const_smul c
  have hbd : ∀ s : ℝ, |s| ≤ 1 →
      ‖c • iteratedFDeriv ℝ n f2 (x + s • a)‖ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := by
    intro s hs
    have h2 : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) hs
    have hxy : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x + s • a‖) := by
      have h3 : ‖x‖ ≤ ‖x + s • a‖ + ‖s • a‖ := by
        have := norm_sub_le (x + s • a) (s • a)
        rwa [add_sub_cancel_right] at this
      nlinarith [norm_nonneg (x + s • a), norm_nonneg a]
    have hpow : c ≤ (1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k := by
      rw [hc, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hxy k
    rw [norm_smul, Real.norm_of_nonneg hc0]
    calc c * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖
        ≤ ((1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k) * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (1 + ‖a‖) ^ k * ((1 + ‖x + s • a‖) ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖) := by ring
      _ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_le_mul_of_nonneg_left (hL _) (by positivity)
  have hT := taylor_two (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f2 (x + s • a)) hdf hdf1 _ hbd t ht
  simp only [zero_smul, add_zero] at hT
  have e : c • iteratedFDeriv ℝ n f (x + t • a) - c • iteratedFDeriv ℝ n f x
      - t • c • iteratedFDeriv ℝ n f1 x
      = c • (iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - t • iteratedFDeriv ℝ n f1 x) := by
    rw [smul_sub, smul_sub, smul_comm t c]
  rw [e, norm_smul, Real.norm_of_nonneg hc0] at hT
  exact hT

end GlobalTheory.SchwartzTranslate
