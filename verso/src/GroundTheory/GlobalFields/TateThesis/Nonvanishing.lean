import Mathlib
import GroundTheory.GlobalFields.TateThesis.NonvanishingLandau

open NumberField IsDedekindDomain Complex Topology Filter Asymptotics

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

/- English proof (translation)
Assume the negation of the conclusion as `hu`. Take `⟨x, hx⟩` from `ideleModule_surjective (K := K) ⟨Real.exp (Real.pi / u), Real.exp_pos _⟩`. Establish `h1` using `h x`. Rewrite `h1` using `[hx]`. Express the relevant statement in the definitionally equal form `((Real.exp (Real.pi / u) : ℝ) : ℂ) ^ ((u : ℂ) * I) = 1 at h1`.

Rewrite `h1` using `[ofReal_exp, cpow_def_of_ne_zero (exp_ne_zero _), Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]`. Establish `e : ((Real.pi / u : ℝ) : ℂ) * ((u : ℂ) * I) = Real.pi * I`. Use `push_cast`. Clear denominators, using `[ofReal_ne_zero.2 hu]` for the nonvanishing conditions. Rewrite `h1` using `[e, exp_pi_mul_I]`.

Evaluate the numerical expressions using `at h1`.
-/
theorem eq_zero_of_forall_ideleModule_cpow_eq_one {u : ℝ}
    (h : ∀ x : IdeleGroup K, ((ideleModule K x : ℝ) : ℂ) ^ ((u : ℂ) * I) = 1) : u = 0 := by
  by_contra hu
  obtain ⟨x, hx⟩ := ideleModule_surjective (K := K) ⟨Real.exp (Real.pi / u), Real.exp_pos _⟩
  have h1 := h x
  rw [hx] at h1
  change ((Real.exp (Real.pi / u) : ℝ) : ℂ) ^ ((u : ℂ) * I) = 1 at h1
  rw [ofReal_exp, cpow_def_of_ne_zero (exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])] at h1
  have e : ((Real.pi / u : ℝ) : ℂ) * ((u : ℂ) * I) = Real.pi * I := by
    push_cast
    field_simp [ofReal_ne_zero.2 hu]
  rw [e, exp_pi_mul_I] at h1
  norm_num at h1

/- English proof (translation)
Establish `hφ : Tendsto (fun x : ℝ ↦ (x : ℂ) + p) (𝓝[>] 0) (𝓝 p)`. Establish `: Tendsto (fun x : ℝ ↦ (x : ℂ) + p) (𝓝 0) (𝓝 ((0 : ℝ) + p))` using `((continuous_ofReal.add continuous_const).tendsto 0)`. Rewrite `this` using `[ofReal_zero, zero_add]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `tendsto_nhds_unique_of_eventuallyEq (h₁.tendsto.comp hφ) (h₂.tendsto.comp hφ) ?_` and prove the remaining obligations.

Use `filter_upwards [hφ.eventually h, self_mem_nhdsWithin] with x hx hxpos`. Conclude with `hx (by simpa using hxpos)`.
-/
theorem eq_of_continuousAt_of_eventually {f₁ f₂ : ℂ → ℂ} {p : ℂ} (h₁ : ContinuousAt f₁ p)
    (h₂ : ContinuousAt f₂ p) (h : ∀ᶠ s in 𝓝 p, p.re < s.re → f₁ s = f₂ s) : f₁ p = f₂ p := by
  have hφ : Tendsto (fun x : ℝ ↦ (x : ℂ) + p) (𝓝[>] 0) (𝓝 p) := by
    have : Tendsto (fun x : ℝ ↦ (x : ℂ) + p) (𝓝 0) (𝓝 ((0 : ℝ) + p)) :=
      ((continuous_ofReal.add continuous_const).tendsto 0)
    rw [ofReal_zero, zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique_of_eventuallyEq (h₁.tendsto.comp hφ) (h₂.tendsto.comp hφ) ?_
  filter_upwards [hφ.eventually h, self_mem_nhdsWithin] with x hx hxpos
  exact hx (by simpa using hxpos)

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

/- English proof (translation)
Introduce `h0`. Use `set p : ℂ := 1 + t * I with hp`. Use `set q : ℂ := 1 + 2 * t * I with hq`. Choose the witnesses or unpack the hypotheses as in `⟨G₂, hG₂, hG₂L⟩ : ∃ G₂ : ℂ → ℂ, DifferentiableAt ℂ G₂ q ∧ ∀ s : ℂ, 1 < s.re → G₂ s = (χ ^ 2).LFunction s := by`. Distinguish the cases in `hτ : ∃ τ : ℝ, ∀ x : IdeleGroup K, ((χ ^ 2).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)`.

Take `⟨τ, hτ⟩` from `hτ`. Take `⟨G₂, hd, hL, -⟩` from `(χ ^ 2).exists_LFunction_continuation_of_forall hτ`. Establish `hne : q ≠ 1 - (τ : ℂ) * I`. Introduce `hqτ`. Establish `him` using `congrArg im hqτ`.

Simplify using `[hq] at him`. Apply `hsq` to reduce the goal to its premises. Introduce `x`. Establish `hm : ((ideleModule K x : ℝ) : ℂ) ≠ 0` using `ofReal_ne_zero.2 (ideleModule K x).2.ne'`. Rewrite using `[mul_pow, ← Circle.coe_pow, ← pow_toIdele, hτ x, ← cpow_nat_mul, ← cpow_add _ _ hm]`.

Rewrite using `[show (τ : ℂ) * I + ((2 : ℕ) : ℂ) * ((t : ℂ) * I) = ((τ + 2 * t : ℝ) : ℂ) * I by push_cast; ring]`. Rewrite using `[show τ + 2 * t = 0 by linarith, ofReal_zero, zero_mul, cpow_zero]`. Conclude with `⟨G₂, hd.differentiableAt (isOpen_compl_singleton.mem_nhds hne), hL⟩`. Take `⟨G₂, hd, hL⟩` from `(χ ^ 2).exists_LFunction_continuation hτ`. Conclude with `⟨G₂, hd q, hL⟩`.

Establish `hφ : ∀ c : ℂ, Tendsto (fun x : ℝ ↦ (x : ℂ) + c) (𝓝 0) (𝓝 c)` using `fun c ↦ by`. Establish `: Tendsto (fun x : ℝ ↦ (x : ℂ) + c) (𝓝 0) (𝓝 ((0 : ℝ) + c))` using `((continuous_ofReal.add continuous_const).tendsto 0)`. Rewrite `this` using `[ofReal_zero, zero_add]`. Then use the resulting hypothesis. Establish `hev : ∀ᶠ x : ℝ in 𝓝[>] 0, g (x + p) = χ.LFunction (x + p)` using `by filter_upwards [((hφ p).eventually hgL).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxpos`. Conclude with `hx (by simpa [hp] using hxpos)`.

Establish `H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0] fun x : ℝ ↦ dedekindZeta K ((1 + x : ℝ) : ℂ) ^ 3 * g (x + p) ^ 4 * G₂ (x + q)`. Use `IsBigO.of_bound' ?_` and prove the remaining obligations. Use `filter_upwards [hev, self_mem_nhdsWithin] with x hx hxpos`. Establish `hxpos' : 0 < x` using `hxpos`. Establish `e1 : ((1 + x : ℝ) : ℂ) + t * I = x + p` using `by rw [hp]; push_cast; ring`.

Establish `e2 : ((1 + x : ℝ) : ℂ) + 2 * t * I = x + q` using `by rw [hq]; push_cast; ring`. Establish `hre : 1 < ((x : ℂ) + q).re` using `by simp [hq, hxpos']`. Use `χ.one_le_norm_dedekindZeta_pow_mul (σ := 1 + x) (by linarith) t` as an intermediate fact. Rewrite `this` using `[e1, e2]`. Rewrite using `[norm_one, hx, hG₂L _ hre]`.

Conclude with `this`. Establish `HZ : (fun x : ℝ ↦ dedekindZeta K ((1 + x : ℝ) : ℂ)) =O[𝓝[>] 0] fun x ↦ (1 : ℂ) / x`. Establish `hmap : Tendsto (fun x : ℝ ↦ 1 + x) (𝓝[>] 0) (𝓝[>] 1)`. Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_` and prove the remaining obligations. Establish `: Tendsto (fun x : ℝ ↦ 1 + x) (𝓝 0) (𝓝 (1 + 0))` using `tendsto_const_nhds.add tendsto_id`.

Rewrite `this` using `[add_zero]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Simplify using `using hx`. Establish `h` using `(tendsto_sub_one_mul_dedekindZeta_nhdsGT K).comp hmap`.

Establish `hb : (fun x : ℝ ↦ (x : ℂ) * dedekindZeta K ((1 + x : ℝ) : ℂ)) =O[𝓝[>] 0] fun _ ↦ (1 : ℂ)`. Use `(h.isBigO_one ℂ).congr_left fun x ↦ ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `(isBigO_mul_iff_isBigO_div ?_).1 hb` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Conclude with `ofReal_ne_zero.2 (ne_of_gt hx)`. Establish `HL : (fun x : ℝ ↦ g (x + p)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ)`. Establish `hd : DifferentiableAt ℂ (fun z ↦ g (z + p)) 0`.

Establish `: DifferentiableAt ℂ g (0 + p)` using `by rwa [zero_add]`. Conclude with `this.comp (0 : ℂ) (differentiableAt_id.add_const p)`. Establish `h1` using `hd.isBigO_sub`. Rewrite `h1` using `[← ofReal_zero]`. Establish `h2` using `(isBigO_comp_ofReal_nhds h1).mono (nhdsWithin_le_nhds (s := Set.Ioi 0))`.

Simplify `h2` using `only [ofReal_zero, zero_add, h0, sub_zero]`. Establish `H₂ : (fun x : ℝ ↦ G₂ (x + q)) =O[𝓝[>] 0] fun _ ↦ (1 : ℂ)` using `((hG₂.continuousAt.tendsto.comp (hφ q)).isBigO_one ℂ).mono nhdsWithin_le_nhds`. Establish `help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x`. Break down `eq_or_ne x 0 with rfl | h` into its components or cases. Rewrite using `[ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]`.

Rewrite using `[one_div, inv_pow, pow_succ _ 3, ← mul_assoc, inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]`. Establish `H` using `((HZ.pow 3).mul (HL.pow 4)).mul H₂`. Simplify using `only [help] at H`. Use `replace H := (H₀.trans H).norm_right`. Simplify using `only [norm_real] at H`.

Conclude with `isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <| H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds`.
-/
theorem continuation_ne_zero_of_not_sq (t : ℝ)
    (hsq : ¬ ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1)
    {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g (1 + t * I))
    (hgL : ∀ᶠ s in 𝓝 (1 + t * I), 1 < s.re → g s = χ.LFunction s) :
    g (1 + t * I) ≠ 0 := by
  intro h0
  set p : ℂ := 1 + t * I with hp
  set q : ℂ := 1 + 2 * t * I with hq

  obtain ⟨G₂, hG₂, hG₂L⟩ : ∃ G₂ : ℂ → ℂ, DifferentiableAt ℂ G₂ q ∧
      ∀ s : ℂ, 1 < s.re → G₂ s = (χ ^ 2).LFunction s := by
    by_cases hτ : ∃ τ : ℝ, ∀ x : IdeleGroup K,
        ((χ ^ 2).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)
    · obtain ⟨τ, hτ⟩ := hτ
      obtain ⟨G₂, hd, hL, -⟩ := (χ ^ 2).exists_LFunction_continuation_of_forall hτ
      have hne : q ≠ 1 - (τ : ℂ) * I := by
        intro hqτ
        have him := congrArg im hqτ
        simp [hq] at him
        apply hsq
        intro x
        have hm : ((ideleModule K x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (ideleModule K x).2.ne'
        rw [mul_pow, ← Circle.coe_pow, ← pow_toIdele, hτ x, ← cpow_nat_mul, ← cpow_add _ _ hm]
        rw [show (τ : ℂ) * I + ((2 : ℕ) : ℂ) * ((t : ℂ) * I) = ((τ + 2 * t : ℝ) : ℂ) * I by
          push_cast; ring]
        rw [show τ + 2 * t = 0 by linarith, ofReal_zero, zero_mul, cpow_zero]
      exact ⟨G₂, hd.differentiableAt (isOpen_compl_singleton.mem_nhds hne), hL⟩
    · obtain ⟨G₂, hd, hL⟩ := (χ ^ 2).exists_LFunction_continuation hτ
      exact ⟨G₂, hd q, hL⟩

  have hφ : ∀ c : ℂ, Tendsto (fun x : ℝ ↦ (x : ℂ) + c) (𝓝 0) (𝓝 c) := fun c ↦ by
    have : Tendsto (fun x : ℝ ↦ (x : ℂ) + c) (𝓝 0) (𝓝 ((0 : ℝ) + c)) :=
      ((continuous_ofReal.add continuous_const).tendsto 0)
    rwa [ofReal_zero, zero_add] at this
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 0, g (x + p) = χ.LFunction (x + p) := by
    filter_upwards [((hφ p).eventually hgL).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with x hx hxpos
    exact hx (by simpa [hp] using hxpos)

  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0] fun x : ℝ ↦
      dedekindZeta K ((1 + x : ℝ) : ℂ) ^ 3 * g (x + p) ^ 4 * G₂ (x + q) := by
    refine IsBigO.of_bound' ?_
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hxpos
    have hxpos' : 0 < x := hxpos
    have e1 : ((1 + x : ℝ) : ℂ) + t * I = x + p := by rw [hp]; push_cast; ring
    have e2 : ((1 + x : ℝ) : ℂ) + 2 * t * I = x + q := by rw [hq]; push_cast; ring
    have hre : 1 < ((x : ℂ) + q).re := by simp [hq, hxpos']
    have := χ.one_le_norm_dedekindZeta_pow_mul (σ := 1 + x) (by linarith) t
    rw [e1, e2] at this
    rw [norm_one, hx, hG₂L _ hre]
    exact this

  have HZ : (fun x : ℝ ↦ dedekindZeta K ((1 + x : ℝ) : ℂ)) =O[𝓝[>] 0] fun x ↦ (1 : ℂ) / x := by
    have hmap : Tendsto (fun x : ℝ ↦ 1 + x) (𝓝[>] 0) (𝓝[>] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun x : ℝ ↦ 1 + x) (𝓝 0) (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_id
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    have h := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).comp hmap
    have hb : (fun x : ℝ ↦ (x : ℂ) * dedekindZeta K ((1 + x : ℝ) : ℂ)) =O[𝓝[>] 0]
        fun _ ↦ (1 : ℂ) := by
      refine (h.isBigO_one ℂ).congr_left fun x ↦ ?_
      simp only [Function.comp_apply]
      push_cast
      ring
    refine (isBigO_mul_iff_isBigO_div ?_).1 hb
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ofReal_ne_zero.2 (ne_of_gt hx)

  have HL : (fun x : ℝ ↦ g (x + p)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
    have hd : DifferentiableAt ℂ (fun z ↦ g (z + p)) 0 := by
      have : DifferentiableAt ℂ g (0 + p) := by rwa [zero_add]
      exact this.comp (0 : ℂ) (differentiableAt_id.add_const p)
    have h1 := hd.isBigO_sub
    rw [← ofReal_zero] at h1
    have h2 := (isBigO_comp_ofReal_nhds h1).mono (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa only [ofReal_zero, zero_add, h0, sub_zero] using h2

  have H₂ : (fun x : ℝ ↦ G₂ (x + q)) =O[𝓝[>] 0] fun _ ↦ (1 : ℂ) :=
    ((hG₂.continuousAt.tendsto.comp (hφ q)).isBigO_one ℂ).mono nhdsWithin_le_nhds
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  have H := ((HZ.pow 3).mul (HL.pow 4)).mul H₂
  simp only [help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

/- English proof (translation)
Distinguish the cases in `hsq : ∀ x : IdeleGroup K, ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1`. Establish `hnot : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)`. Introduce and unpack `⟨τ, hτ⟩`. Establish `hm : ∀ x : IdeleGroup K, ((ideleModule K x : ℝ) : ℂ) ≠ 0` using `fun x ↦ ofReal_ne_zero.2 (ideleModule K x).2.ne'`. Establish `htw : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I) = ((ideleModule K x : ℝ) : ℂ) ^ (((τ + t : ℝ) : ℂ) * I)` using `fun x ↦ by`.

Rewrite using `[hτ x, ← cpow_add _ _ (hm x)]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `h2 : τ + t = 0`. Establish `h2' : 2 * (τ + t) = 0`.

Use `eq_zero_of_forall_ideleModule_cpow_eq_one (K := K) fun x ↦ ?_` and prove the remaining obligations. Use `hsq x` as an intermediate fact. Rewrite `this` using `[htw x, ← cpow_nat_mul]`. Rewrite using `[← this]`. Use `push_cast`.

Put the polynomial expressions in normal form. Combine the linear equalities and inequalities to obtain the conclusion. Apply `hχ` to reduce the goal to its premises. Introduce `x`. Rewrite using `[htw x, h2, ofReal_zero, zero_mul, cpow_zero]`.

Take `⟨G, hG, hGL⟩` from `χ.exists_LFunction_continuation hnot`. Establish `hGg : G (1 + t * I) = g (1 + t * I)`. Use `eq_of_continuousAt_of_eventually (hG _).continuousAt hg.continuousAt ?_` and prove the remaining obligations. Use `filter_upwards [hgL] with s hs hre`. Establish `hre' : 1 < s.re` using `by simpa using hre`.

Rewrite using `[hGL s hre', hs hre']`. Rewrite using `[← hGg]`. Conclude with `χ.continuation_ne_zero_of_sq_eq_one t hsq hG hGL`. Conclude with `χ.continuation_ne_zero_of_not_sq t hsq hg hgL`.
-/
theorem LFunction_continuation_ne_zero (t : ℝ)
    (hχ : ¬ ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I) = 1)
    {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g (1 + t * I))
    (hgL : ∀ᶠ s in 𝓝 (1 + t * I), 1 < s.re → g s = χ.LFunction s) :
    g (1 + t * I) ≠ 0 := by
  by_cases hsq : ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1
  ·
    have hnot : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
        (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
      rintro ⟨τ, hτ⟩
      have hm : ∀ x : IdeleGroup K, ((ideleModule K x : ℝ) : ℂ) ≠ 0 := fun x ↦
        ofReal_ne_zero.2 (ideleModule K x).2.ne'
      have htw : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I) =
          ((ideleModule K x : ℝ) : ℂ) ^ (((τ + t : ℝ) : ℂ) * I) := fun x ↦ by
        rw [hτ x, ← cpow_add _ _ (hm x)]
        push_cast
        ring_nf
      have h2 : τ + t = 0 := by
        have h2' : 2 * (τ + t) = 0 := by
          refine eq_zero_of_forall_ideleModule_cpow_eq_one (K := K) fun x ↦ ?_
          have := hsq x
          rw [htw x, ← cpow_nat_mul] at this
          rw [← this]
          push_cast
          ring_nf
        linarith
      apply hχ
      intro x
      rw [htw x, h2, ofReal_zero, zero_mul, cpow_zero]
    obtain ⟨G, hG, hGL⟩ := χ.exists_LFunction_continuation hnot
    have hGg : G (1 + t * I) = g (1 + t * I) := by
      refine eq_of_continuousAt_of_eventually (hG _).continuousAt hg.continuousAt ?_
      filter_upwards [hgL] with s hs hre
      have hre' : 1 < s.re := by simpa using hre
      rw [hGL s hre', hs hre']
    rw [← hGg]
    exact χ.continuation_ne_zero_of_sq_eq_one t hsq hG hGL
  · exact χ.continuation_ne_zero_of_not_sq t hsq hg hgL

/- English proof (translation)
Establish `hm : ((ideleModule K x : ℝ) : ℂ) ≠ 0` using `ofReal_ne_zero.2 (ideleModule K x).2.ne'`. Establish `e : ((-t : ℝ) : ℂ) * I = -((t : ℂ) * I)` using `by push_cast; ring`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← cpow_add _ _ hm, add_neg_cancel, cpow_zero, mul_one]`.

Use `_ = _ := by rw [← mul_assoc, hχ x, one_mul]`.
-/
theorem toIdele_eq_cpow_of_forall (t : ℝ)
    (hχ : ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I) = 1)
    (x : IdeleGroup K) :
    (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ (((-t : ℝ) : ℂ) * I) := by
  have hm : ((ideleModule K x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (ideleModule K x).2.ne'
  have e : ((-t : ℝ) : ℂ) * I = -((t : ℂ) * I) := by push_cast; ring
  rw [e]
  calc (χ.toIdele x : ℂ) = (χ.toIdele x : ℂ) * (((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I) *
        ((ideleModule K x : ℝ) : ℂ) ^ (-((t : ℂ) * I))) := by
        rw [← cpow_add _ _ hm, add_neg_cancel, cpow_zero, mul_one]
    _ = _ := by rw [← mul_assoc, hχ x, one_mul]

/- English proof (translation)
Break down `hs.lt_or_eq with hs | hs` into its components or cases. Rewrite using `[hGL s hs]`. Conclude with `χ.LFunction_ne_zero hs`. Establish `hse : s = 1 + (s.im : ℂ) * I`. Apply the tactic sequence `apply Complex.ext <;> simp [hs.symm]`.

Rewrite using `[hse]`. Use `χ.LFunction_continuation_ne_zero s.im ?_ (hG _) (Eventually.of_forall fun z hz ↦ hGL z hz)` and prove the remaining obligations. Introduce `h`. Conclude with `hχ ⟨-s.im, χ.toIdele_eq_cpow_of_forall s.im h⟩`.
-/
theorem continuation_ne_zero_of_one_le_re
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGL : ∀ s : ℂ, 1 < s.re → G s = χ.LFunction s)
    {s : ℂ} (hs : 1 ≤ s.re) : G s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · rw [hGL s hs]
    exact χ.LFunction_ne_zero hs
  have hse : s = 1 + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hs.symm]
  rw [hse]
  refine χ.LFunction_continuation_ne_zero s.im ?_ (hG _)
    (Eventually.of_forall fun z hz ↦ hGL z hz)
  intro h
  exact hχ ⟨-s.im, χ.toIdele_eq_cpow_of_forall s.im h⟩

end HeckeCharacter

end

end GroundTheory.Global
