import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
open UpperTheory.V.Lit.Geo.Cs GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTSmooth
open GlobalTheory.ThetaPull (invL invL_smooth)
open scoped ContDiff Topology

/- English proof (translation)
Introduce `i hi`. Consider the cases of `i with`. Consider the case `zero => simpa using h0`. Consider the case `succ i`. Rewrite using `[← norm_iteratedFDeriv_fderiv]`.

Conclude with `h1 i (Nat.le_of_succ_le_succ hi)`.
-/
private theorem sz_succ {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {f : V → F} {p : V} {b : ℝ} (h0 : ‖f p‖ ≤ b) (h1 : Sz k (fderiv ℝ f) p b) : Sz (k + 1) f p b := by
  intro i hi
  cases i with
  | zero => simpa using h0
  | succ i =>
    rw [← norm_iteratedFDeriv_fderiv]
    exact h1 i (Nat.le_of_succ_le_succ hi)

/- English proof (translation)
Introduce `E _ _ _ a k ρ hρ`. Establish `h1 : oneL E a ∈ invSet E a` using `isUnit_one`. Establish `hval : ∀ (φ : Sm E a), (∀ l : List (Lie E a), ∃ C : ℝ, ∀ g, ‖((l.map (lie E a)).prod φ).1 g‖ ≤ C * ρ g) → ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖chart φ.1 g (oneL E a)‖ ≤ C * ρ g`. Introduce `φ hφ`. Take `⟨C, hC⟩` from `hφ []`.

Use `⟨max C 0, le_max_right _ _, fun g => ?_⟩` and prove the remaining obligations. Establish `e` using `chart_val φ.1 g 1`. Rewrite `e` using `[map_one, mul_one]`. Establish `e' : chart φ.1 g (oneL E a) = φ.1 g` using `e`. Rewrite using `[e']`.

Conclude with `(hC g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ g))`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `φ hφ`. Take `⟨C, hC0, hC⟩` from `hval φ hφ`.

Use `⟨C, hC0, fun g i hi => ?_⟩` and prove the remaining obligations. Take `rfl : i = 0` from `Nat.le_zero.1 hi`. Simplify using `using hC g`. Consider the case `succ k ih`. Introduce `φ hφ`.

Take `⟨C₀, hC0, hC⟩` from `hval φ hφ`. Establish `hi : ∀ i : Ix E a, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, Sz k (chart (lie E a (bs E a i) φ).1 g) (oneL E a) (C * ρ g)`. Introduce `i`. Use `ih _ fun l => ?_` and prove the remaining obligations. Take `⟨C, hC⟩` from `hφ (l ++ [bs E a i])`.

Use `⟨C, fun g => ?_⟩` and prove the remaining obligations. Use `hC g` as an intermediate fact. Rewrite `this` using `[List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply]`. Then use the resulting hypothesis. Use `choose D hD0 hD using hi`. Set `Θ : Ix E a → Lie E a → (ℂ →L[ℝ] (Lie E a →L[ℝ] ℂ))` to `fun i y => ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL y))`.

Establish `hΘ : ∀ i, ContDiffAt ℝ ∞ (Θ i) (oneL E a)` using `fun i => (ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ).contDiff.contDiffAt.comp _ ((coordL i).contDiff.contDiffAt.comp _ ((invL_smooth (E := E) (a := a)).1 _ h1))`. Use `choose B hB using fun i => exists_sz k (Θ i) (oneL E a)`. Establish `hS0 : 0 ≤ ∑ i, 2 ^ k * B i * D i` using `Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB i).nonneg) (hD0 i)`. Use `⟨C₀ + ∑ i, 2 ^ k * B i * D i, add_nonneg hC0 hS0, fun g => sz_succ ?_ ?_⟩` and prove the remaining obligations. Conclude with `(hC g).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS0) (hρ g))`.

Establish `hc : ∀ i, ContDiffAt ℝ ∞ (chart (lie E a (bs E a i) φ).1 g) (oneL E a)` using `fun i => contDiffAt_chart (lie E a (bs E a i) φ).2 g h1`. Establish `key` using `(appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).2.2 (Ix E a) Finset.univ (fun i y => Θ i y (chart (lie E a (bs E a i) φ).1 g y)) (fun i => 2 ^ k * B i * (D i * ρ g)) (fun i _ => (hΘ i).clm_apply (hc i)) (fun i _ => (appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).1 _ _ _ _ ( …`. Use `(key.congr ?_).mono ?_` and prove the remaining obligations. Use `filter_upwards [isOpen_invSet.mem_nhds h1] with y hy`. Conclude with `(fderiv_chart_eq φ g hy).symm`.

Rewrite using `[add_mul, Finset.sum_mul]`. Use `le_add_of_nonneg_of_le (mul_nonneg hC0 (hρ g)) (le_of_eq ?_)` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem UpperTheory.V.Lit.Geo.Cs.chartSz :
    ChartSz := by
  intro E _ _ _ a k ρ hρ
  have h1 : oneL E a ∈ invSet E a := isUnit_one
  have hval : ∀ (φ : Sm E a), (∀ l : List (Lie E a), ∃ C : ℝ, ∀ g, ‖((l.map (lie E a)).prod φ).1 g‖ ≤ C * ρ g) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖chart φ.1 g (oneL E a)‖ ≤ C * ρ g := by
    intro φ hφ
    obtain ⟨C, hC⟩ := hφ []
    refine ⟨max C 0, le_max_right _ _, fun g => ?_⟩
    have e := chart_val φ.1 g 1
    rw [map_one, mul_one] at e
    have e' : chart φ.1 g (oneL E a) = φ.1 g := e
    rw [e']
    exact (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ g))
  induction k with
  | zero =>
    intro φ hφ
    obtain ⟨C, hC0, hC⟩ := hval φ hφ
    refine ⟨C, hC0, fun g i hi => ?_⟩
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    simpa using hC g
  | succ k ih =>
    intro φ hφ
    obtain ⟨C₀, hC0, hC⟩ := hval φ hφ
    have hi : ∀ i : Ix E a, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, Sz k (chart (lie E a (bs E a i) φ).1 g) (oneL E a) (C * ρ g) := by
      intro i
      refine ih _ fun l => ?_
      obtain ⟨C, hC⟩ := hφ (l ++ [bs E a i])
      refine ⟨C, fun g => ?_⟩
      have := hC g
      rwa [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply] at this
    choose D hD0 hD using hi
    let Θ : Ix E a → Lie E a → (ℂ →L[ℝ] (Lie E a →L[ℝ] ℂ)) := fun i y =>
      ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL y))
    have hΘ : ∀ i, ContDiffAt ℝ ∞ (Θ i) (oneL E a) := fun i =>
      (ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ).contDiff.contDiffAt.comp _
        ((coordL i).contDiff.contDiffAt.comp _ ((invL_smooth (E := E) (a := a)).1 _ h1))
    choose B hB using fun i => exists_sz k (Θ i) (oneL E a)
    have hS0 : 0 ≤ ∑ i, 2 ^ k * B i * D i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB i).nonneg) (hD0 i)
    refine ⟨C₀ + ∑ i, 2 ^ k * B i * D i, add_nonneg hC0 hS0, fun g => sz_succ ?_ ?_⟩
    · exact (hC g).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS0) (hρ g))
    · have hc : ∀ i, ContDiffAt ℝ ∞ (chart (lie E a (bs E a i) φ).1 g) (oneL E a) := fun i =>
        contDiffAt_chart (lie E a (bs E a i) φ).2 g h1
      have key := (appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).2.2 (Ix E a) Finset.univ
        (fun i y => Θ i y (chart (lie E a (bs E a i) φ).1 g y)) (fun i => 2 ^ k * B i * (D i * ρ g))
        (fun i _ => (hΘ i).clm_apply (hc i))
        (fun i _ => (appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).1 _ _ _ _ (hΘ i) (hc i) (hB i) (hD i g))
      refine (key.congr ?_).mono ?_
      · filter_upwards [isOpen_invSet.mem_nhds h1] with y hy
        exact (fderiv_chart_eq φ g hy).symm
      · rw [add_mul, Finset.sum_mul]
        refine le_add_of_nonneg_of_le (mul_nonneg hC0 (hρ g)) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => by ring
