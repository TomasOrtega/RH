import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterLeSuccAndSqSumLePow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormEigenLePowMulNormSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasEigenvalueSummand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirResolventCircleBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevSubspaceMono
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumEigenprojectorLeOfResolventBound

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖`. Introduce `x hx`. Establish `hnorm : ∀ i, ‖(lam i : ℂ) - (-((bv / 16 : ℝ) : ℂ))‖ = |lam i + bv / 16|`. Introduce `i`. Rewrite using `[sub_neg_eq_add, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]`.

Use `GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound H (Fin n) VV T p (fun i => (lam i : ℂ)) (univ.filter (fun a : Fin n => a.val + 1 < kk)) (-((bv / 16 : ℝ) : ℂ)) (9 * bv / 16) (32 / (13 * bv)) hfd (by positivity) (by positivity) (fun x _ => hsum x) hp ?_ ?_ ?_ x hx` as an intermediate fact. Establish `e : 9 * bv / 16 * (32 / (13 * bv)) = 18 / 13` using `by field_simp; norm_num`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `i hi`. Use `(hpos i).1 (mem_filter.1 hi).2` as an intermediate fact.

Rewrite using `[hnorm, abs_lt]`. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Introduce `i hi`. Establish `hi' : kk ≤ i.val + 1`. Assume the negation of the conclusion as `h`.

Conclude with `hi (mem_filter.2 ⟨mem_univ _, not_le.1 h⟩)`. Use `(hpos i).2 hi'` as an intermediate fact. Rewrite using `[hnorm, lt_abs]`. Use `left`. Combine the linear relations using `[this.1, this.2]`.

Introduce `ζ hζ y hy`. Rewrite `hζ` using `[sub_neg_eq_add]`. Establish `h` using `hres ζ hζ y hy`. Establish `e : ‖y‖ = 32 / (13 * bv) * (13 * bv / 32 * ‖y‖)` using `by field_simp`. Rewrite using `[e]`.

Conclude with `mul_le_mul_of_nonneg_left h (by positivity)`. Introduce `x hx`. Use `⟨h1 x hx, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hsN : s ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1)` using `mem_filter.2 ⟨mem_univ _, hs⟩`. Use `GlobalTheory.norm_node_projector_le H (Fin n) VV T p (fun i => (lam i : ℂ)) (univ.filter (fun a : Fin n => kk ≤ a.val + 1)) s (6 * bv) 3 hsN (by positivity) hp ?_ ?_ ?_ ?_ x hx` as an intermediate fact.

Rewrite `this` using `[card_erase_of_mem hsN, hcard]`. Establish `e : n + 1 - kk - 1 = n - kk` using `by omega`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `y hy`. Rewrite using `[← hsum y, map_sum]`.

Conclude with `VV.sum_mem fun i _ => by rw [(hp i y hy).2]; exact VV.smul_mem _ (hp i y hy).1`. Introduce `i hi`. Rewrite using `[← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `hgap s i (ne_of_mem_erase hi).symm`. Introduce `i hi y hy`.

Establish `hi'` using `(hpos i).2 (mem_filter.1 (mem_of_mem_erase hi)).2`. Establish `h2 : |lam i| ≤ 3 * bv`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith [hi'.1, hi'.2]`. Combine the equalities or inequalities in the displayed calculation. Use `add_le_add (hT y hy) ?_` and prove the remaining obligations.

Rewrite using `[norm_smul, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `mul_le_mul_of_nonneg_right h2 (norm_nonneg _)`. Use `_ = 6 * bv * ‖y‖ := by ring`. Introduce `y hy`. Establish `h3` using `sum_filter_add_sum_filter_not univ (fun a : Fin n => a.val + 1 < kk) (fun i => p i y)`.

Rewrite `h3` using `[hsum y]`. Simplify using `only [not_lt] at h3`. Establish `h4 : ∑ i ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1), p i y = y - ∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y`. Rewrite using `[eq_sub_iff_add_eq, add_comm]`. Conclude with `h3`.

Rewrite using `[h4]`. Use `h1 y hy` as an intermediate fact. Establish `h5` using `norm_sub_le y (∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y)`. Combine the linear relations using `[norm_nonneg y]`.
-/
theorem cloud_node_projector_bound (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (n kk : ℕ) (bv : ℝ)
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : Fin n → H →ₗ[ℂ] H) (lam : Fin n → ℝ)
    (hfd : FiniteDimensional ℂ VV) (hb : 0 < bv)
    (hsum : ∀ x, ∑ i, p i x = x)
    (hp : ∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = (lam i : ℂ) • p i x)
    (hpos : ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ lam a ∧ lam a ≤ bv / 32) ∧
      (kk ≤ a.val + 1 → bv - bv / 32 ≤ lam a ∧ lam a ≤ 2 * bv + bv / 32))
    (hgap : ∀ a c : Fin n, a ≠ c → 1 ≤ |lam a - lam c|)
    (hcard : (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk)
    (hres : ∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → ∀ x ∈ VV, 13 * bv / 32 * ‖x‖ ≤ ‖ζ • x - T x‖)
    (hT : ∀ x ∈ VV, ‖T x‖ ≤ 3 * bv * ‖x‖) :
    ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ ∧
      ∀ s : Fin n, kk ≤ s.val + 1 → ‖p s x‖ ≤ 3 * (6 * bv) ^ (n - kk) * ‖x‖ := by
  have h1 : ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ := by
    intro x hx
    have hnorm : ∀ i, ‖(lam i : ℂ) - (-((bv / 16 : ℝ) : ℂ))‖ = |lam i + bv / 16| := by
      intro i
      rw [sub_neg_eq_add, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    have := GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound H (Fin n) VV T p (fun i => (lam i : ℂ)) (univ.filter (fun a : Fin n => a.val + 1 < kk))
      (-((bv / 16 : ℝ) : ℂ)) (9 * bv / 16) (32 / (13 * bv)) hfd (by positivity) (by positivity)
      (fun x _ => hsum x) hp ?_ ?_ ?_ x hx
    · have e : 9 * bv / 16 * (32 / (13 * bv)) = 18 / 13 := by field_simp; norm_num
      rwa [e] at this
    · intro i hi
      have := (hpos i).1 (mem_filter.1 hi).2
      rw [hnorm, abs_lt]
      constructor <;> linarith [this.1, this.2]
    · intro i hi
      have hi' : kk ≤ i.val + 1 := by
        by_contra h
        exact hi (mem_filter.2 ⟨mem_univ _, not_le.1 h⟩)
      have := (hpos i).2 hi'
      rw [hnorm, lt_abs]
      left
      linarith [this.1, this.2]
    · intro ζ hζ y hy
      rw [sub_neg_eq_add] at hζ
      have h := hres ζ hζ y hy
      have e : ‖y‖ = 32 / (13 * bv) * (13 * bv / 32 * ‖y‖) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
  intro x hx
  refine ⟨h1 x hx, fun s hs => ?_⟩
  have hsN : s ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1) := mem_filter.2 ⟨mem_univ _, hs⟩
  have := GlobalTheory.norm_node_projector_le H (Fin n) VV T p (fun i => (lam i : ℂ))
    (univ.filter (fun a : Fin n => kk ≤ a.val + 1)) s (6 * bv) 3 hsN (by positivity) hp ?_ ?_ ?_ ?_ x hx
  · rw [card_erase_of_mem hsN, hcard] at this
    have e : n + 1 - kk - 1 = n - kk := by omega
    rwa [e] at this
  · intro y hy
    rw [← hsum y, map_sum]
    exact VV.sum_mem fun i _ => by rw [(hp i y hy).2]; exact VV.smul_mem _ (hp i y hy).1
  · intro i hi
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap s i (ne_of_mem_erase hi).symm
  · intro i hi y hy
    have hi' := (hpos i).2 (mem_filter.1 (mem_of_mem_erase hi)).2
    have h2 : |lam i| ≤ 3 * bv := by
      rw [abs_le]; constructor <;> linarith [hi'.1, hi'.2]
    calc ‖T y - (lam i : ℂ) • y‖ ≤ ‖T y‖ + ‖(lam i : ℂ) • y‖ := norm_sub_le _ _
      _ ≤ 3 * bv * ‖y‖ + 3 * bv * ‖y‖ := by
          refine add_le_add (hT y hy) ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = 6 * bv * ‖y‖ := by ring
  · intro y hy
    have h3 := sum_filter_add_sum_filter_not univ (fun a : Fin n => a.val + 1 < kk) (fun i => p i y)
    rw [hsum y] at h3
    simp only [not_lt] at h3
    have h4 : ∑ i ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1), p i y =
        y - ∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h3
    rw [h4]
    have := h1 y hy
    have h5 := norm_sub_le y (∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y)
    linarith [norm_nonneg y]

/- English proof (translation)
Introduce `M _ _ n ε E N _ _ F io pr μ kk j bv w hM hF hA hS hj hw c`. Take `⟨hb, -, hpos⟩` from `GlobalTheory.shape_position n kk j ε μ bv hS (by omega)`. Take `⟨L0, Ladd, Lsmul, -⟩` from `GlobalTheory.lev_subspace_mono M n ε E μ hM.1 hM.2.1`. Establish `hcomp` using `GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hM.2.1 (fun s => (hF s).2.1) hA hw`. Establish `heig` using `GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hM hF hA`.

Establish `hnb : (n : ℝ) ≤ bv`. Establish `h1 : (1 : ℝ) ≤ n` using `by exact_mod_cast (by have := hS.2.1; omega : 1 ≤ n)`. Establish `h2 : (n : ℝ) ≤ (n : ℝ) ^ 7` using `le_self_pow₀ h1 (by norm_num)`. Establish `h3` using `hS.2.2.2.2.2`. Establish `h4 : (0 : ℝ) ≤ (n : ℝ) ^ 7` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard` using `(GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv hS.1 hS.2.1 hnb).1`. Set `e : PiLp 2 (fun _ : Fin n => M) ≃ₗ[ℂ] (Fin n → M)` to `WithLp.linearEquiv 2 ℂ (Fin n → M)`. Establish `hn : ∀ x : PiLp 2 (fun _ : Fin n => M), ‖x‖ ^ 2 = ∑ d, ‖e x d‖ ^ 2` using `fun x => PiLp.norm_sq_eq_of_L2 _ x`. Set `T0 : (Fin n → M) →ₗ[ℂ] (Fin n → M)` to `LinearMap.pi fun b => -∑ a, (E b a) ∘ₗ (LinearMap.proj a : (Fin n → M) →ₗ[ℂ] M)`.

Establish `hT0 : ∀ x, T0 x = splitCas E x`. Introduce `x`. Use function extensionality and compare the values at `b`. Simplify using `[T0, splitCas]`. Set `T : PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M)` to `e.symm.toLinearMap ∘ₗ T0 ∘ₗ e.toLinearMap`.

Establish `hT : ∀ x, e (T x) = splitCas E (e x)`. Introduce `x`. Rewrite using `[← hT0]`. Conclude with `e.apply_symm_apply _`. Set `p : Fin n → PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M)` to `fun s => e.symm.toLinearMap ∘ₗ io s ∘ₗ pr s ∘ₗ e.toLinearMap`.

Establish `hp : ∀ s x, e (p s x) = io s (pr s (e x))` using `fun s x => e.apply_symm_apply _`. Set `x₀ : PiLp 2 (fun _ : Fin n => M)` to `e.symm (Pi.single c w)`. Establish `hx₀ : e x₀ = Pi.single c w` using `e.apply_symm_apply _`. Establish `hx₀n : ‖x₀‖ ^ 2 = ‖w‖ ^ 2`. Rewrite using `[hn, hx₀, Finset.sum_eq_single c]`.

Simplify using the standard rewrite rules. Introduce `d _ hd`. Simplify using `[hd]`. Simplify using the standard rewrite rules. Set `VV : Submodule ℂ (PiLp 2 (fun _ : Fin n => M))` to `Submodule.span ℂ (Set.range fun s => p s x₀)`.

Establish `hfd : FiniteDimensional ℂ VV` using `FiniteDimensional.span_of_finite ℂ (Set.finite_range _)`. Establish `hsum : ∀ x, ∑ i, p i x = x`. Introduce `x`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_sum]`.

Simplify using `only [hp]`. Conclude with `hA.sum_io_pr _`. Establish `hx₀V : x₀ ∈ VV`. Rewrite using `[← hsum x₀]`. Conclude with `VV.sum_mem fun i _ => Submodule.subset_span ⟨i, rfl⟩`.

Establish `hpV : ∀ i, ∀ x ∈ VV, p i x ∈ VV`. Introduce `i x hx`. Establish `: VV ≤ VV.comap (p i)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`.

Use `show p i (p s x₀) ∈ VV`. Distinguish the cases in `h : i = s`. Substitute `h` using the available equality. Establish `: p i (p i x₀) = p i x₀`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[hp, hp, hA.pr_io]`. Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `: p i (p s x₀) = 0`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[hp, hp, hA.pr_io_ne i s h, map_zero, map_zero]`. Rewrite using `[this]`. Conclude with `VV.zero_mem`. Conclude with `this hx`. Establish `hlev : ∀ x ∈ VV, ∀ d, Lev ε E μ (j + 2) (e x d)`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, rfl⟩` from `hx`. Introduce `d`.

Rewrite using `[hp, hx₀]`. Conclude with `hcomp s c d`. Consider the case `zero => intro d`. Rewrite using `[map_zero]`. Conclude with `L0 _`.

Consider the case `add x y _ _ hx hy => intro d`. Rewrite using `[map_add]`. Conclude with `Ladd _ _ _ (hx d) (hy d)`. Consider the case `smul a x _ hx => intro d`. Rewrite using `[map_smul]`.

Conclude with `Lsmul _ _ _ (hx d)`. Establish `hres` using `fun x (hx : x ∈ VV) => GlobalTheory.T.splitCasimir_resolvent_circle_bounds M n ε E μ kk (j + 2) bv (e x) hM hS (by omega) (hlev x hx)`. Establish `key` using `cloud_node_projector_bound (PiLp 2 (fun _ : Fin n => M)) n kk bv VV T p (fun s => -μ s + (1 - (n : ℝ)) / 2) hfd hb hsum ?_ hpos ?_ hcard ?_ ?_ x₀ hx₀V`. Use `⟨?_, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h` using `pow_le_pow_left₀ (norm_nonneg _) key.1 2`.

Rewrite `h` using `[mul_pow, hx₀n, hn, map_sum]`. Simplify using `only [hp, hx₀] at h`. Conclude with `h`. Establish `h` using `pow_le_pow_left₀ (norm_nonneg _) (key.2 s hs) 2`. Rewrite `h` using `[mul_pow, hx₀n, hn, hp, hx₀]`.

Conclude with `h`. Introduce `i x hx`. Use `⟨hpV i x hx, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hT, map_smul, hp, heig]`.

Introduce `a b hab`. Rewrite using `[le_abs]`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Use `right`. Use `hS.2.2.1 a b h` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `left`. Use `hS.2.2.1 b a h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `ζ hζ x hx`.

Establish `h` using `(hres x hx).1 ζ hζ`. Use `(pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[mul_pow, hn, hn, map_sub, map_smul, hT]`. Conclude with `h`. Introduce `x hx`.

Establish `h` using `(hres x hx).2`. Use `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[mul_pow, hn, hn, hT]`. Conclude with `h`.
-/
theorem cloud_node_projection_norm : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hM hF hA hS hj hw c
  obtain ⟨hb, -, hpos⟩ := GlobalTheory.shape_position n kk j ε μ bv hS (by omega)
  obtain ⟨L0, Ladd, Lsmul, -⟩ := GlobalTheory.lev_subspace_mono M n ε E μ hM.1 hM.2.1
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hM.2.1 (fun s => (hF s).2.1) hA hw
  have heig := GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hM hF hA
  have hnb : (n : ℝ) ≤ bv := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by have := hS.2.1; omega : 1 ≤ n)
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ h1 (by norm_num)
    have h3 := hS.2.2.2.2.2
    have h4 : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    linarith
  have hcard := (GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv hS.1 hS.2.1 hnb).1
  let e : PiLp 2 (fun _ : Fin n => M) ≃ₗ[ℂ] (Fin n → M) := WithLp.linearEquiv 2 ℂ (Fin n → M)
  have hn : ∀ x : PiLp 2 (fun _ : Fin n => M), ‖x‖ ^ 2 = ∑ d, ‖e x d‖ ^ 2 := fun x => PiLp.norm_sq_eq_of_L2 _ x
  let T0 : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
    LinearMap.pi fun b => -∑ a, (E b a) ∘ₗ (LinearMap.proj a : (Fin n → M) →ₗ[ℂ] M)
  have hT0 : ∀ x, T0 x = splitCas E x := by
    intro x
    funext b
    simp [T0, splitCas]
  let T : PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := e.symm.toLinearMap ∘ₗ T0 ∘ₗ e.toLinearMap
  have hT : ∀ x, e (T x) = splitCas E (e x) := by
    intro x
    rw [← hT0]
    exact e.apply_symm_apply _
  let p : Fin n → PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := fun s =>
    e.symm.toLinearMap ∘ₗ io s ∘ₗ pr s ∘ₗ e.toLinearMap
  have hp : ∀ s x, e (p s x) = io s (pr s (e x)) := fun s x => e.apply_symm_apply _
  let x₀ : PiLp 2 (fun _ : Fin n => M) := e.symm (Pi.single c w)
  have hx₀ : e x₀ = Pi.single c w := e.apply_symm_apply _
  have hx₀n : ‖x₀‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [hn, hx₀, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [hd]
    · simp
  let VV : Submodule ℂ (PiLp 2 (fun _ : Fin n => M)) := Submodule.span ℂ (Set.range fun s => p s x₀)
  have hfd : FiniteDimensional ℂ VV := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hsum : ∀ x, ∑ i, p i x = x := by
    intro x
    apply e.injective
    rw [map_sum]
    simp only [hp]
    exact hA.sum_io_pr _
  have hx₀V : x₀ ∈ VV := by
    rw [← hsum x₀]
    exact VV.sum_mem fun i _ => Submodule.subset_span ⟨i, rfl⟩
  have hpV : ∀ i, ∀ x ∈ VV, p i x ∈ VV := by
    intro i x hx
    have : VV ≤ VV.comap (p i) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      show p i (p s x₀) ∈ VV
      by_cases h : i = s
      · subst h
        have : p i (p i x₀) = p i x₀ := by
          apply e.injective
          rw [hp, hp, hA.pr_io]
        rw [this]
        exact Submodule.subset_span ⟨i, rfl⟩
      · have : p i (p s x₀) = 0 := by
          apply e.injective
          rw [hp, hp, hA.pr_io_ne i s h, map_zero, map_zero]
        rw [this]
        exact VV.zero_mem
    exact this hx
  have hlev : ∀ x ∈ VV, ∀ d, Lev ε E μ (j + 2) (e x d) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      intro d
      rw [hp, hx₀]
      exact hcomp s c d
    | zero => intro d; rw [map_zero]; exact L0 _
    | add x y _ _ hx hy => intro d; rw [map_add]; exact Ladd _ _ _ (hx d) (hy d)
    | smul a x _ hx => intro d; rw [map_smul]; exact Lsmul _ _ _ (hx d)
  have hres := fun x (hx : x ∈ VV) =>
    GlobalTheory.T.splitCasimir_resolvent_circle_bounds M n ε E μ kk (j + 2) bv (e x) hM hS (by omega) (hlev x hx)
  have key := cloud_node_projector_bound (PiLp 2 (fun _ : Fin n => M)) n kk bv VV T p
    (fun s => -μ s + (1 - (n : ℝ)) / 2) hfd hb hsum ?_ hpos ?_ hcard ?_ ?_ x₀ hx₀V
  · refine ⟨?_, fun s hs => ?_⟩
    · have h := pow_le_pow_left₀ (norm_nonneg _) key.1 2
      rw [mul_pow, hx₀n, hn, map_sum] at h
      simp only [hp, hx₀] at h
      exact h
    · have h := pow_le_pow_left₀ (norm_nonneg _) (key.2 s hs) 2
      rw [mul_pow, hx₀n, hn, hp, hx₀] at h
      exact h
  · intro i x hx
    refine ⟨hpV i x hx, ?_⟩
    apply e.injective
    rw [hT, map_smul, hp, heig]
  · intro a b hab
    rw [le_abs]
    rcases lt_or_gt_of_ne hab with h | h
    · right
      have := hS.2.2.1 a b h
      linarith
    · left
      have := hS.2.2.1 b a h
      linarith
  · intro ζ hζ x hx
    have h := (hres x hx).1 ζ hζ
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, map_sub, map_smul, hT]
    exact h
  · intro x hx
    have h := (hres x hx).2
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, hT]
    exact h

end GlobalTheory
