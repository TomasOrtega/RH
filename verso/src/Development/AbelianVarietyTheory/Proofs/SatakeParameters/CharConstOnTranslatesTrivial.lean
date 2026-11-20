import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCharUnitsComplexStatement

open Filter Topology

namespace GlobalTheory.ArchChar

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `conv : ∀ {Y : ℕ → ι → ℂˣ} {v : ι → ℂˣ}, (∀ i, Tendsto (fun m => (Y m i : ℂ)) atTop (𝓝 (v i : ℂ))) → Tendsto Y atTop (𝓝 v)`. Introduce `Y v hY`. Rewrite using `[tendsto_pi_nhds]`. Introduce `i`. Conclude with `Units.isEmbedding_val₀.isInducing.tendsto_nhds_iff.2 (hY i)`.

Establish `h1` using `(hψ.tendsto w).comp (conv hX)`. Establish `h2` using `(hψ.tendsto w').comp (conv hX')`. Establish `h3 : (ψ ∘ X) = (ψ ∘ X')` using `funext h`. Rewrite `h1` using `[h3]`. Conclude with `tendsto_nhds_unique h1 h2`.
-/
lemma eq_of_tendsto (ψ : (ι → ℂˣ) →* ℂˣ) (hψ : Continuous ψ) {X X' : ℕ → ι → ℂˣ} {w w' : ι → ℂˣ}
    (h : ∀ m, ψ (X m) = ψ (X' m))
    (hX : ∀ i, Tendsto (fun m => (X m i : ℂ)) atTop (𝓝 (w i : ℂ)))
    (hX' : ∀ i, Tendsto (fun m => (X' m i : ℂ)) atTop (𝓝 (w' i : ℂ))) : ψ w = ψ w' := by
  have conv : ∀ {Y : ℕ → ι → ℂˣ} {v : ι → ℂˣ},
      (∀ i, Tendsto (fun m => (Y m i : ℂ)) atTop (𝓝 (v i : ℂ))) → Tendsto Y atTop (𝓝 v) := by
    intro Y v hY
    rw [tendsto_pi_nhds]
    intro i
    exact Units.isEmbedding_val₀.isInducing.tendsto_nhds_iff.2 (hY i)
  have h1 := (hψ.tendsto w).comp (conv hX)
  have h2 := (hψ.tendsto w').comp (conv hX')
  have h3 : (ψ ∘ X) = (ψ ∘ X') := funext h
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/- English proof (translation)
Establish `hev : ∀ᶠ m in l, 0 < μ m` using `hμ.eventually_gt_atTop 0`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hbound : Tendsto (fun m => (C + ‖θ‖) / μ m) l (𝓝 0)` using `tendsto_const_nhds.div_atTop hμ`. Use `squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_ hbound` and prove the remaining obligations. Use `filter_upwards [hev] with m hm`.

Establish `hμc : (μ m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hid : ((a m : ℂ) + θ) / (μ m : ℂ) - (r : ℂ) = (((a m - μ m * r : ℝ) : ℂ) + θ) / (μ m : ℂ)`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Combine the linear relations using `[h m]`.
-/
lemma tendsto_div {α : Type} {l : Filter α} (θ : ℂ) (r C : ℝ) {a μ : α → ℝ}
    (hμ : Tendsto μ l atTop) (h : ∀ m, |a m - μ m * r| ≤ C) :
    Tendsto (fun m => ((a m : ℂ) + θ) / (μ m : ℂ)) l (𝓝 (r : ℂ)) := by
  have hev : ∀ᶠ m in l, 0 < μ m := hμ.eventually_gt_atTop 0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun m => (C + ‖θ‖) / μ m) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hμ
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_ hbound
  filter_upwards [hev] with m hm
  have hμc : (μ m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hid : ((a m : ℂ) + θ) / (μ m : ℂ) - (r : ℂ) = (((a m - μ m * r : ℝ) : ℂ) + θ) / (μ m : ℂ) := by
    field_simp
    push_cast
    ring
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  gcongr
  calc ‖((a m - μ m * r : ℝ) : ℂ) + θ‖ ≤ ‖((a m - μ m * r : ℝ) : ℂ)‖ + ‖θ‖ := norm_add_le _ _
    _ ≤ C + ‖θ‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith [h m]

/- English proof (translation)
Introduce `h`. Apply `hθ` to reduce the goal to its premises. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `using this`.
-/
lemma add_ne {θ : ℂ} (hθ : θ.im ≠ 0) (t : ℝ) : (t : ℂ) + θ ≠ 0 := by
  intro h
  apply hθ
  have := congrArg Complex.im h
  simpa using this

/- English proof (translation)
Conclude with `h.ne'` after adjusting the coercions.
-/
lemma ofReal_ne {ρ : ℝ} (h : 0 < ρ) : (ρ : ℂ) ≠ 0 := by
  exact_mod_cast h.ne'

noncomputable def shift (θ : ι → ℂ) (hθ : ∀ i, (θ i).im ≠ 0) (a : ι → ℝ) : ι → ℂˣ :=
  fun i => Units.mk0 _ (add_ne (hθ i) (a i))

noncomputable def realUnits (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ι → ℂˣ :=
  fun i => Units.mk0 _ (ofReal_ne (hr i))

/- English proof (translation)
Use `norm_le_pi_norm (a - y) i` as an intermediate fact. Rewrite `this` using `[Pi.sub_apply, Real.norm_eq_abs]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma abs_coord_le {a y : ι → ℝ} {C : ℝ} (h : ‖a - y‖ ≤ C) (i : ι) : |a i - y i| ≤ C := by
  have := norm_le_pi_norm (a - y) i
  rw [Pi.sub_apply, Real.norm_eq_abs] at this
  linarith

/- English proof (translation)
Conclude with `tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop`.
-/
lemma tendsto_succ : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/- English proof (translation)
Check the signs of the components of the expression.
-/
lemma succ_pos (m : ℕ) : 0 < (m : ℝ) + 1 := by
  positivity

/- English proof (translation)
Set `D : ℕ → ι → ℂˣ` to `fun m => realUnits (fun _ => (m : ℝ) + 1) (fun _ => succ_pos m)`. Establish `key : ∀ (q : ι → ℝ) (hq : ∀ i, 0 < q i), ∃ X : ℕ → ι → ℂˣ, (∀ m, ψ (X m) = c * (ψ (D m))⁻¹) ∧ ∀ i, Tendsto (fun m => (X m i : ℂ)) atTop (𝓝 (realUnits q hq i : ℂ))`. Introduce `q hq`. Use `choose A hA hAd using fun m : ℕ => hT (fun i => ((m : ℝ) + 1) * q i)`. Use `⟨fun m => shift θ hθ (A m) * (D m)⁻¹, fun m => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_inv, hc _ (hA m)]`. Use `tendsto_div (θ i) (q i) C tendsto_succ (a := fun m => A m i) (fun m => abs_coord_le (hAd m) i)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Simplify using `[shift, realUnits, D, div_eq_mul_inv]`.

Simplify using `[realUnits]`. Take `⟨X, hX, hXl⟩` from `key r hr`. Take `⟨X', hX', hX'l⟩` from `key (fun _ => 1) (fun _ => one_pos)`. Establish `heq` using `eq_of_tendsto ψ hψ (fun m => (hX m).trans (hX' m).symm) hXl hX'l`. Rewrite using `[heq]`.

Establish `h1 : realUnits (fun _ : ι => (1 : ℝ)) (fun _ => one_pos) = 1`. Use function extensionality and compare the values at `i`. Use `ext`. Simplify using `[realUnits]`. Rewrite using `[h1, map_one]`.
-/
lemma real_trivial (ψ : (ι → ℂˣ) →* ℂˣ) (hψ : Continuous ψ) (θ : ι → ℂ) (hθ : ∀ i, (θ i).im ≠ 0)
    (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ) (hT : ∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C)
    (hc : ∀ a ∈ T, ψ (shift θ hθ a) = c) (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ψ (realUnits r hr) = 1 := by
  let D : ℕ → ι → ℂˣ := fun m => realUnits (fun _ => (m : ℝ) + 1) (fun _ => succ_pos m)
  have key : ∀ (q : ι → ℝ) (hq : ∀ i, 0 < q i), ∃ X : ℕ → ι → ℂˣ,
      (∀ m, ψ (X m) = c * (ψ (D m))⁻¹) ∧
      ∀ i, Tendsto (fun m => (X m i : ℂ)) atTop (𝓝 (realUnits q hq i : ℂ)) := by
    intro q hq
    choose A hA hAd using fun m : ℕ => hT (fun i => ((m : ℝ) + 1) * q i)
    refine ⟨fun m => shift θ hθ (A m) * (D m)⁻¹, fun m => ?_, fun i => ?_⟩
    · rw [map_mul, map_inv, hc _ (hA m)]
    · have := tendsto_div (θ i) (q i) C tendsto_succ (a := fun m => A m i)
        (fun m => abs_coord_le (hAd m) i)
      convert this using 1
      · funext m
        simp [shift, realUnits, D, div_eq_mul_inv]
      · simp [realUnits]
  obtain ⟨X, hX, hXl⟩ := key r hr
  obtain ⟨X', hX', hX'l⟩ := key (fun _ => 1) (fun _ => one_pos)
  have heq := eq_of_tendsto ψ hψ (fun m => (hX m).trans (hX' m).symm) hXl hX'l
  rw [heq]
  have h1 : realUnits (fun _ : ι => (1 : ℝ)) (fun _ => one_pos) = 1 := by
    funext i
    ext
    simp [realUnits]
  rw [h1, map_one]

/- English proof (translation)
Establish `hD : ∀ m : ℕ, ψ (realUnits (fun _ : ι => (m : ℝ) + 1) (fun _ => succ_pos m)) = 1` using `fun m => real_trivial ψ hψ θ hθ T C c hT hc _ _`. Use `choose A hA hAd using fun m : ℕ => hT (fun _ : ι => ((m : ℝ) + 1) * 1)`. Take `⟨a₀, ha₀, -⟩` from `hT 0`. Establish `hlim : ∀ i, Tendsto (fun m => ((shift θ hθ (A m) * (realUnits (fun _ : ι => (m : ℝ) + 1) (fun _ => succ_pos m))⁻¹) i : ℂ)) atTop (𝓝 ((1 : ι → ℂˣ) i : ℂ))`. Introduce `i`.

Use `tendsto_div (θ i) 1 C tendsto_succ (a := fun m => A m i) (fun m => abs_coord_le (hAd m) i)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Simplify using `[shift, realUnits, div_eq_mul_inv]`. Simplify using the standard rewrite rules.

Establish `heq` using `eq_of_tendsto ψ hψ (X' := fun _ => shift θ hθ a₀) (w' := shift θ hθ a₀) (fun m => by rw [map_mul, map_inv, hD, hc _ (hA m), hc _ ha₀, inv_one, mul_one]) hlim (fun i => tendsto_const_nhds)`. Rewrite `heq` using `[map_one, hc _ ha₀]`. Conclude with `heq.symm`.
-/
lemma const_eq_one (ψ : (ι → ℂˣ) →* ℂˣ) (hψ : Continuous ψ) (θ : ι → ℂ) (hθ : ∀ i, (θ i).im ≠ 0)
    (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ) (hT : ∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C)
    (hc : ∀ a ∈ T, ψ (shift θ hθ a) = c) : c = 1 := by
  have hD : ∀ m : ℕ, ψ (realUnits (fun _ : ι => (m : ℝ) + 1) (fun _ => succ_pos m)) = 1 :=
    fun m => real_trivial ψ hψ θ hθ T C c hT hc _ _
  choose A hA hAd using fun m : ℕ => hT (fun _ : ι => ((m : ℝ) + 1) * 1)
  obtain ⟨a₀, ha₀, -⟩ := hT 0
  have hlim : ∀ i, Tendsto (fun m => ((shift θ hθ (A m) *
      (realUnits (fun _ : ι => (m : ℝ) + 1) (fun _ => succ_pos m))⁻¹) i : ℂ)) atTop
      (𝓝 ((1 : ι → ℂˣ) i : ℂ)) := by
    intro i
    have := tendsto_div (θ i) 1 C tendsto_succ (a := fun m => A m i)
      (fun m => abs_coord_le (hAd m) i)
    convert this using 1
    · funext m
      simp [shift, realUnits, div_eq_mul_inv]
    · simp
  have heq := eq_of_tendsto ψ hψ (X' := fun _ => shift θ hθ a₀) (w' := shift θ hθ a₀)
    (fun m => by rw [map_mul, map_inv, hD, hc _ (hA m), hc _ ha₀, inv_one, mul_one]) hlim
    (fun i => tendsto_const_nhds)
  rw [map_one, hc _ ha₀] at heq
  exact heq.symm

/- English proof (translation)
Set `y : ℕ → ι → ℝ` to `fun m j => if j = i then R else ((m : ℝ) + 1) * 1`. Use `choose A hA hAd using fun m => hT (y m)`. Establish `hAi : ∀ m, A m i ∈ Set.Icc (R - C) (R + C)`. Introduce `m`. Establish `h : |A m i - R| ≤ C` using `by simpa [y] using abs_coord_le (hAd m) i`.

Rewrite `h` using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [h.1, h.2]`. Take `⟨t, ht, φ, hφ, hlim⟩` from `isCompact_Icc.tendsto_subseq hAi`. Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith [ht.1, ht.2]`. Apply the tactic sequence `let D : ℕ → ι → ℂˣ := fun m => realUnits (fun j => if j = i then 1 else (m : ℝ) + 1) (fun j => by split_ifs <;> [exact one_pos; exact succ_pos m])`. Establish `hD : ∀ m, ψ (D m) = 1` using `fun m => real_trivial ψ hψ θ hθ T C 1 hT hc _ _`. Establish `hconv : ∀ j, Tendsto (fun m => ((shift θ hθ (A (φ m)) * (D (φ m))⁻¹) j : ℂ)) atTop (𝓝 ((Pi.mulSingle i (Units.mk0 _ (add_ne (hθ i) t)) : ι → ℂˣ) j : ℂ))`. Introduce `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[shift, D, realUnits]`. Conclude with `((Complex.continuous_ofReal.tendsto t).comp hlim).add_const _`. Establish `h1` using `tendsto_div (θ j) 1 C tendsto_succ (a := fun m => A m j) (fun m => by`.

Simplify `abs_coord_le (hAd m) j)` using `[y, hj]`. Establish `h2` using `h1.comp hφ.tendsto_atTop`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Simplify using `[shift, D, realUnits, hj, div_eq_mul_inv]`.

Simplify using `[hj]`. Establish `heq` using `eq_of_tendsto ψ hψ (X' := fun _ => 1) (w' := 1) (fun m => by rw [map_mul, map_inv, hc _ (hA _), hD, inv_one, mul_one, map_one]) hconv (fun j => by simp)`. Rewrite using `[heq, map_one]`.
-/
lemma exists_near (ψ : (ι → ℂˣ) →* ℂˣ) (hψ : Continuous ψ) (θ : ι → ℂ) (hθ : ∀ i, (θ i).im ≠ 0)
    (T : Set (ι → ℝ)) (C : ℝ) (hT : ∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C)
    (hc : ∀ a ∈ T, ψ (shift θ hθ a) = 1) (i : ι) (R : ℝ) :
    ∃ t : ℝ, |t - R| ≤ C ∧ ψ (Pi.mulSingle i (Units.mk0 _ (add_ne (hθ i) t))) = 1 := by
  let y : ℕ → ι → ℝ := fun m j => if j = i then R else ((m : ℝ) + 1) * 1
  choose A hA hAd using fun m => hT (y m)
  have hAi : ∀ m, A m i ∈ Set.Icc (R - C) (R + C) := by
    intro m
    have h : |A m i - R| ≤ C := by simpa [y] using abs_coord_le (hAd m) i
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  obtain ⟨t, ht, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hAi
  refine ⟨t, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  · let D : ℕ → ι → ℂˣ := fun m => realUnits (fun j => if j = i then 1 else (m : ℝ) + 1)
      (fun j => by split_ifs <;> [exact one_pos; exact succ_pos m])
    have hD : ∀ m, ψ (D m) = 1 := fun m => real_trivial ψ hψ θ hθ T C 1 hT hc _ _
    have hconv : ∀ j, Tendsto (fun m => ((shift θ hθ (A (φ m)) * (D (φ m))⁻¹) j : ℂ)) atTop
        (𝓝 ((Pi.mulSingle i (Units.mk0 _ (add_ne (hθ i) t)) : ι → ℂˣ) j : ℂ)) := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp [shift, D, realUnits]
        exact ((Complex.continuous_ofReal.tendsto t).comp hlim).add_const _
      · have h1 := tendsto_div (θ j) 1 C tendsto_succ (a := fun m => A m j) (fun m => by
            simpa [y, hj] using abs_coord_le (hAd m) j)
        have h2 := h1.comp hφ.tendsto_atTop
        convert h2 using 1
        · funext m
          simp [shift, D, realUnits, hj, div_eq_mul_inv]
        · simp [hj]
    have heq := eq_of_tendsto ψ hψ (X' := fun _ => 1) (w' := 1)
      (fun m => by rw [map_mul, map_inv, hc _ (hA _), hD, inv_one, mul_one, map_one]) hconv
      (fun j => by simp)
    rw [heq, map_one]

/- English proof (translation)
Take `⟨s, n, hform⟩` from `GlobalTheory.T.continuous_units_complex_hom_eq_exp_mul_arg_pow e he`. Establish `hs0 : ∀ x : ℝ, Complex.exp (s * x) = 1`. Introduce `x`. Establish `h` using `hform (Units.mk0 _ (ofReal_ne (Real.exp_pos x)))`. Rewrite `h` using `[hpos _ (Real.exp_pos x)]`.

Simplify using `at h`. Conclude with `h.symm`. Establish `hs : s = 0`. Assume the negation of the conclusion as `hsne`. Take `⟨k, hk⟩` from `Complex.exp_eq_one_iff.1 (hs0 (1 / (‖s‖ + 1)))`.

Establish `hpos' : (0 : ℝ) < ‖s‖ + 1` using `by positivity`. Establish `hnorm : ‖s * ((1 / (‖s‖ + 1) : ℝ) : ℂ)‖ < 1`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Rewrite using `[show ‖s‖ * (1 / (‖s‖ + 1)) = ‖s‖ / (‖s‖ + 1) by ring, div_lt_one hpos']`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hk0 : k = 0`. Assume the negation of the conclusion as `hk0`. Rewrite `hnorm` using `[hk]`. Establish `hn2 : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ = |(k : ℝ)| * (2 * Real.pi)`. Rewrite using `[norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast]`.

Simplify using `[abs_of_pos Real.pi_pos]`. Establish `hk1 : (1 : ℝ) ≤ |(k : ℝ)|` using `by exact_mod_cast Int.one_le_abs hk0`. Rewrite `hnorm` using `[hn2]`. Use polynomial arithmetic with `[Real.pi_gt_three]`. Rewrite `hk` using `[hk0]`.

Simplify using `at hk`. Break down `hk with h | h` into its components or cases. Conclude with `hsne h`. Conclude with `(by exact_mod_cast hpos'.ne' : ((‖s‖ : ℂ) + 1) ≠ 0) h`. Substitute `hs` using the available equality.

Establish `hform' : ∀ z : ℂˣ, (e z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n`. Introduce `z`. Rewrite using `[hform]`. Simplify using the standard rewrite rules. Distinguish the cases in `hn : n = 0`.

Use `MonoidHom.ext fun z => ?_` and prove the remaining obligations. Use `ext`. Rewrite using `[hform', hn, zpow_zero]`. Simplify using the standard rewrite rules. It suffices to derive a contradiction.

Set `u : ℝ → ℂ` to `fun t => ((t : ℂ) + θ) / (‖(t : ℂ) + θ‖ : ℂ)`. Establish `uinj : ∀ t t' : ℝ, u t = u t' → t = t'`. Introduce `t t' h`. Establish `hA : ((t : ℂ) + θ) ≠ 0` using `add_ne hθ t`. Establish `hB : ((t' : ℂ) + θ) ≠ 0` using `add_ne hθ t'`.

Establish `hnA : (‖(t : ℂ) + θ‖ : ℂ) ≠ 0` using `by exact_mod_cast (norm_pos_iff.2 hA).ne'`. Establish `hnB : (‖(t' : ℂ) + θ‖ : ℂ) ≠ 0` using `by exact_mod_cast (norm_pos_iff.2 hB).ne'`. Simplify using `only [u] at h`. Rewrite `h` using `[div_eq_div_iff hnA hnB]`. Establish `him` using `congrArg Complex.im h`.

Simplify using `at him`. Establish `hnorm : ‖(t' : ℂ) + θ‖ = ‖(t : ℂ) + θ‖` using `him.resolve_right hθ`. Rewrite `h` using `[hnorm]`. Establish `h'` using `mul_right_cancel₀ hnA h`. Establish `hre` using `congrArg Complex.re h'`.

Simplify using `using hre`. Establish `hk : 0 < n.natAbs` using `Int.natAbs_pos.2 hn`. Establish `hS : {t : ℝ | u t ^ n.natAbs = 1}.Finite`. Establish `hfin : {z : ℂ | z ^ n.natAbs = 1}.Finite`. Apply `(Polynomial.nthRoots n.natAbs (1 : ℂ)).toFinset.finite_toSet.subset` to reduce the goal to its premises.

Introduce `z hz`. Simplify `hz` using `[Polynomial.mem_nthRoots hk]`. Conclude with `hfin.preimage (fun t _ t' _ h => uinj t t' h)`. Take `⟨M, hM⟩` from `hS.bddAbove`. Take `⟨t, ht, he1⟩` from `hnear (M + C + 1)`.

Establish `hmem : t ∈ {t : ℝ | u t ^ n.natAbs = 1}`. Establish `h` using `congrArg Units.val he1`. Rewrite `h` using `[hform']`. Simplify using `only [Units.val_mk0, Units.val_one] at h`. Use `show u t ^ n.natAbs = 1`.

Break down `Int.natAbs_eq n with h' | h'` into its components or cases. Rewrite `h` using `[h', zpow_natCast]`. Conclude with `h`. Rewrite `h` using `[h', zpow_neg, zpow_natCast, inv_eq_one]`. Conclude with `h`.

Establish `htM` using `hM hmem`. Rewrite `ht` using `[abs_le]`. Combine the linear relations using `[ht.1]`.
-/
lemma char_trivial (e : ℂˣ →* ℂˣ) (he : Continuous e) (θ : ℂ) (hθ : θ.im ≠ 0) (C : ℝ)
    (hpos : ∀ (ρ : ℝ) (h : 0 < ρ), e (Units.mk0 _ (ofReal_ne h)) = 1)
    (hnear : ∀ R : ℝ, ∃ t : ℝ, |t - R| ≤ C ∧ e (Units.mk0 _ (add_ne hθ t)) = 1) : e = 1 := by
  obtain ⟨s, n, hform⟩ := GlobalTheory.T.continuous_units_complex_hom_eq_exp_mul_arg_pow e he
  have hs0 : ∀ x : ℝ, Complex.exp (s * x) = 1 := by
    intro x
    have h := hform (Units.mk0 _ (ofReal_ne (Real.exp_pos x)))
    rw [hpos _ (Real.exp_pos x)] at h
    simp at h
    exact h.symm
  have hs : s = 0 := by
    by_contra hsne
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (hs0 (1 / (‖s‖ + 1)))
    have hpos' : (0 : ℝ) < ‖s‖ + 1 := by positivity
    have hnorm : ‖s * ((1 / (‖s‖ + 1) : ℝ) : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [show ‖s‖ * (1 / (‖s‖ + 1)) = ‖s‖ / (‖s‖ + 1) by ring, div_lt_one hpos']
      linarith
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hnorm
      have hn2 : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast]
        simp [abs_of_pos Real.pi_pos]
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [hn2] at hnorm
      nlinarith [Real.pi_gt_three]
    rw [hk0] at hk
    simp at hk
    rcases hk with h | h
    · exact hsne h
    · exact (by exact_mod_cast hpos'.ne' : ((‖s‖ : ℂ) + 1) ≠ 0) h
  subst hs
  have hform' : ∀ z : ℂˣ, (e z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n := by
    intro z
    rw [hform]
    simp
  by_cases hn : n = 0
  · refine MonoidHom.ext fun z => ?_
    ext
    rw [hform', hn, zpow_zero]
    simp
  · exfalso
    let u : ℝ → ℂ := fun t => ((t : ℂ) + θ) / (‖(t : ℂ) + θ‖ : ℂ)
    have uinj : ∀ t t' : ℝ, u t = u t' → t = t' := by
      intro t t' h
      have hA : ((t : ℂ) + θ) ≠ 0 := add_ne hθ t
      have hB : ((t' : ℂ) + θ) ≠ 0 := add_ne hθ t'
      have hnA : (‖(t : ℂ) + θ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hA).ne'
      have hnB : (‖(t' : ℂ) + θ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hB).ne'
      simp only [u] at h
      rw [div_eq_div_iff hnA hnB] at h
      have him := congrArg Complex.im h
      simp at him
      have hnorm : ‖(t' : ℂ) + θ‖ = ‖(t : ℂ) + θ‖ := him.resolve_right hθ
      rw [hnorm] at h
      have h' := mul_right_cancel₀ hnA h
      have hre := congrArg Complex.re h'
      simpa using hre
    have hk : 0 < n.natAbs := Int.natAbs_pos.2 hn
    have hS : {t : ℝ | u t ^ n.natAbs = 1}.Finite := by
      have hfin : {z : ℂ | z ^ n.natAbs = 1}.Finite := by
        apply (Polynomial.nthRoots n.natAbs (1 : ℂ)).toFinset.finite_toSet.subset
        intro z hz
        simpa [Polynomial.mem_nthRoots hk] using hz
      exact hfin.preimage (fun t _ t' _ h => uinj t t' h)
    obtain ⟨M, hM⟩ := hS.bddAbove
    obtain ⟨t, ht, he1⟩ := hnear (M + C + 1)
    have hmem : t ∈ {t : ℝ | u t ^ n.natAbs = 1} := by
      have h := congrArg Units.val he1
      rw [hform'] at h
      simp only [Units.val_mk0, Units.val_one] at h
      show u t ^ n.natAbs = 1
      rcases Int.natAbs_eq n with h' | h'
      · rw [h', zpow_natCast] at h
        exact h
      · rw [h', zpow_neg, zpow_natCast, inv_eq_one] at h
        exact h
    have htM := hM hmem
    rw [abs_le] at ht
    linarith [ht.1]

end GlobalTheory.ArchChar

/- English proof (translation)
Introduce `ι _ _ ψ θ T C c hψ hθ hT hc`. Establish `hc' : ∀ a ∈ T, ψ (GlobalTheory.ArchChar.shift θ hθ a) = c` using `fun a ha => hc a ha _ (fun i => rfl)`. Establish `h1` using `GlobalTheory.ArchChar.const_eq_one ψ hψ θ hθ T C c hT hc'`. Substitute `h1` using the available equality. Establish `hcomp : ∀ i, ψ.comp (MonoidHom.mulSingle (fun _ : ι => ℂˣ) i) = 1`.

Introduce `i`. Use `GlobalTheory.ArchChar.char_trivial _ (by exact hψ.comp (continuous_mulSingle (A := fun _ : ι => ℂˣ) i)) (θ i) (hθ i) C ?_ ?_` and prove the remaining obligations. Introduce `ρ hρ`. Establish `hr : ∀ j, 0 < Function.update (fun _ : ι => (1 : ℝ)) i ρ j`. Introduce `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hρ`. Simplify using `[Function.update_of_ne hj]`. Establish `h` using `GlobalTheory.ArchChar.real_trivial ψ hψ θ hθ T C 1 hT hc' _ hr`.

Establish `hu : GlobalTheory.ArchChar.realUnits _ hr = Pi.mulSingle i (Units.mk0 _ (GlobalTheory.ArchChar.ofReal_ne hρ))`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Use `ext`.

Simplify using `[GlobalTheory.ArchChar.realUnits]`. Use `ext`. Simplify using `[GlobalTheory.ArchChar.realUnits, hj]`. Rewrite `h` using `[hu]`. Simplify using `using h`.

Introduce `R`. Take `⟨t, ht, h⟩` from `GlobalTheory.ArchChar.exists_near ψ hψ θ hθ T C hT hc' i R`. Conclude with `⟨t, ht, by simpa using h⟩`. Use `MonoidHom.ext fun z => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← Finset.univ_prod_mulSingle z]`.

Rewrite using `[map_prod, MonoidHom.one_apply]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Use `DFunLike.congr_fun (hcomp i) (z i)` as an intermediate fact. Simplify using `using this`.
-/
theorem GlobalTheory.charConstOnTranslates_trivial : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (ψ : (ι → ℂˣ) →* ℂˣ) (θ : ι → ℂ) (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ), Continuous ψ →
    (∀ i, (θ i).im ≠ 0) → (∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C) →
    (∀ a ∈ T, ∀ z : ι → ℂˣ, (∀ i, (z i : ℂ) = a i + θ i) → ψ z = c) → ψ = 1 := by
  intro ι _ _ ψ θ T C c hψ hθ hT hc
  have hc' : ∀ a ∈ T, ψ (GlobalTheory.ArchChar.shift θ hθ a) = c :=
    fun a ha => hc a ha _ (fun i => rfl)
  have h1 := GlobalTheory.ArchChar.const_eq_one ψ hψ θ hθ T C c hT hc'
  subst h1
  have hcomp : ∀ i, ψ.comp (MonoidHom.mulSingle (fun _ : ι => ℂˣ) i) = 1 := by
    intro i
    refine GlobalTheory.ArchChar.char_trivial _ (by exact hψ.comp (continuous_mulSingle (A := fun _ : ι => ℂˣ) i)) (θ i) (hθ i) C ?_ ?_
    · intro ρ hρ
      have hr : ∀ j, 0 < Function.update (fun _ : ι => (1 : ℝ)) i ρ j := by
        intro j
        by_cases hj : j = i
        · subst hj; simpa using hρ
        · simp [Function.update_of_ne hj]
      have h := GlobalTheory.ArchChar.real_trivial ψ hψ θ hθ T C 1 hT hc' _ hr
      have hu : GlobalTheory.ArchChar.realUnits _ hr = Pi.mulSingle i (Units.mk0 _ (GlobalTheory.ArchChar.ofReal_ne hρ)) := by
        funext j
        by_cases hj : j = i
        · subst hj; ext; simp [GlobalTheory.ArchChar.realUnits]
        · ext; simp [GlobalTheory.ArchChar.realUnits, hj]
      rw [hu] at h
      simpa using h
    · intro R
      obtain ⟨t, ht, h⟩ := GlobalTheory.ArchChar.exists_near ψ hψ θ hθ T C hT hc' i R
      exact ⟨t, ht, by simpa using h⟩
  refine MonoidHom.ext fun z => ?_
  conv_lhs => rw [← Finset.univ_prod_mulSingle z]
  rw [map_prod, MonoidHom.one_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  have := DFunLike.congr_fun (hcomp i) (z i)
  simpa using this
