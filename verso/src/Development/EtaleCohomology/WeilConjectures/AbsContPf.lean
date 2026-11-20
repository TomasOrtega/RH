import Development.EtaleCohomology.WeilConjectures.ContinCut

namespace LateralTheory.EWeil.AbsContPf

universe u v

open LateralTheory.EWeil.ContinCut

namespace AbsoluteContinuitySecondLemma

/- English proof (translation)
Rewrite using `[Algebra.smul_def, norm_mul]`. Both sides reduce to the same expression.
-/
theorem goal1 (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]; rfl

end AbsoluteContinuitySecondLemma

/- English proof (translation)
The claim follows from `AbsoluteContinuitySecondLemma.goal1 l a q`.
-/
theorem norm_smul_le (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ :=
  AbsoluteContinuitySecondLemma.goal1 l a q

namespace AbsoluteContinuityFirstLemma

namespace AbsoluteContinuitySmulBound

/- English proof (translation)
Rewrite using `[Algebra.smul_def, norm_mul]`. Establish `h : ‖(algebraMap ℤ_[l] ℚ_[l] a)‖ ≤ 1`. Establish `e : algebraMap ℤ_[l] ℚ_[l] a = (a : ℚ_[l])` using `rfl`. Rewrite using `[e, ← PadicInt.norm_def]`. Conclude with `PadicInt.norm_le_one a`.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma smul_bound (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ ≤ ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]
  have h : ‖(algebraMap ℤ_[l] ℚ_[l] a)‖ ≤ 1 := by
    have e : algebraMap ℤ_[l] ℚ_[l] a = (a : ℚ_[l]) := rfl
    rw [e, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one a
  calc ‖algebraMap ℤ_[l] ℚ_[l] a‖ * ‖q‖ ≤ 1 * ‖q‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖q‖ := one_mul _

end AbsoluteContinuitySmulBound

/- English proof (translation)
Take `⟨s, hs⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] M).FG)`. Use `⟨∑ x ∈ s, ‖φ x‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩` and prove the remaining obligations. Introduce `m`. Establish `hm : m ∈ Submodule.span ℤ_[l] (s : Set M)` using `by rw [hs]; trivial`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem x hx`. Conclude with `Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) hx`. Consider the case `zero => simpa using Finset.sum_nonneg (fun (x : M) (_ : x ∈ s) => norm_nonneg (φ x))`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `(Padic.nonarchimedean _ _).trans (max_le hx hy)`. Consider the case `smul a x _ hx`. Rewrite using `[map_smul]`. Conclude with `(AbsoluteContinuitySmulBound.smul_bound l a (φ x)).trans hx`.
-/
theorem goal1 (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] M).FG)
  refine ⟨∑ x ∈ s, ‖φ x‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro m
  have hm : m ∈ Submodule.span ℤ_[l] (s : Set M) := by rw [hs]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
      exact Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) hx
  | zero => simpa using Finset.sum_nonneg (fun (x : M) (_ : x ∈ s) => norm_nonneg (φ x))
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (Padic.nonarchimedean _ _).trans (max_le hx hy)
  | smul a x _ hx =>
      rw [map_smul]
      exact (AbsoluteContinuitySmulBound.smul_bound l a (φ x)).trans hx

end AbsoluteContinuityFirstLemma

/- English proof (translation)
The claim follows from `AbsoluteContinuityFirstLemma.goal1 l M φ`.
-/
theorem bdd (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C :=
  AbsoluteContinuityFirstLemma.goal1 l M φ

/- English proof (translation)
Introduce `l _ G _ _ _ M _ _ _ ρ K hK h0 hopen φ x`. Take `⟨C, hC0, hCb⟩` from `bdd l M φ`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hlpos : (0 : ℝ) < l` using `by linarith`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g₀`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0:ℝ) < C + 1)) (inv_lt_one_of_one_lt₀ hl1)`. Take `⟨k, hk⟩` from `hC l M K hK h0 N`.

Use `set y := ρ g₀ x`. Establish `hU : IsOpen {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}}` using `(hopen y k).preimage (continuous_id.mul continuous_const)`. Establish `hmem : g₀ ∈ {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}}`. Simplify using `[y]`. Use `filter_upwards [hU.mem_nhds hmem] with g hg`.

Express the relevant statement in the definitionally equal form `ρ (g * g₀⁻¹) y - y ∈ K k at hg`. Establish `hd : ρ g x - ρ g₀ x ∈ K k`. Establish `: ρ (g * g₀⁻¹) y = ρ g x`. Simplify using `only [y]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]`.

Rewrite `hg` using `[this]`. Conclude with `hg`. Take `⟨z, hz⟩` from `hk _ hd`. Rewrite using `[dist_eq_norm, ← map_sub, hz, map_smul, norm_smul_le, PadicInt.norm_p_pow]`. Establish `hzC` using `hCb z`.

Establish `hpow : (l : ℝ) ^ (-(N : ℤ)) = (l : ℝ)⁻¹ ^ N`. Rewrite using `[zpow_neg, zpow_natCast, inv_pow]`. Rewrite using `[hpow]`. Establish `hp0 : 0 ≤ (l : ℝ)⁻¹ ^ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem AbsCont_of (hC : Chev.{u}) : AbsCont.{u, v} := by
  intro l _ G _ _ _ M _ _ _ ρ K hK h0 hopen φ x
  obtain ⟨C, hC0, hCb⟩ := bdd l M φ
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0:ℝ) < C + 1))
    (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨k, hk⟩ := hC l M K hK h0 N
  set y := ρ g₀ x
  have hU : IsOpen {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} :=
    (hopen y k).preimage (continuous_id.mul continuous_const)
  have hmem : g₀ ∈ {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} := by
    simp [y]
  filter_upwards [hU.mem_nhds hmem] with g hg
  change ρ (g * g₀⁻¹) y - y ∈ K k at hg
  have hd : ρ g x - ρ g₀ x ∈ K k := by
    have : ρ (g * g₀⁻¹) y = ρ g x := by
      simp only [y]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [this] at hg; exact hg
  obtain ⟨z, hz⟩ := hk _ hd
  rw [dist_eq_norm, ← map_sub, hz, map_smul, norm_smul_le, PadicInt.norm_p_pow]
  have hzC := hCb z
  have hpow : (l : ℝ) ^ (-(N : ℤ)) = (l : ℝ)⁻¹ ^ N := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hpow]
  have hp0 : 0 ≤ (l : ℝ)⁻¹ ^ N := by positivity
  calc (l : ℝ)⁻¹ ^ N * ‖φ z‖ ≤ (l : ℝ)⁻¹ ^ N * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hp0
    _ < ε / (C + 1) * (C + 1) := mul_lt_mul_of_pos_right hN (by linarith)
    _ = ε := div_mul_cancel₀ _ (by linarith)

end LateralTheory.EWeil.AbsContPf
