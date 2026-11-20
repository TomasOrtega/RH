import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← Fin.prod_const n (∑ x, MvPolynomial.C (t x) * MvPolynomial.X x), Finset.prod_univ_sum, map_sum]`. Use `Finset.sum_congr (by simp) fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, ← map_prod, MvPolynomial.C_mul', map_smul, smul_eq_mul]`.
-/
theorem linForm_pow_expand {ι : Type} [Fintype ι] (n : ℕ) (Λ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (t : ι → ℝ) :
    Λ ((∑ x, MvPolynomial.C (t x) * MvPolynomial.X x) ^ n) =
      ∑ s : Fin n → ι, (∏ i, t (s i)) * Λ (∏ i, MvPolynomial.X (s i)) := by
  rw [← Fin.prod_const n (∑ x, MvPolynomial.C (t x) * MvPolynomial.X x), Finset.prod_univ_sum,
    map_sum]
  refine Finset.sum_congr (by simp) fun s _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.C_mul', map_smul, smul_eq_mul]

/- English proof (translation)
Establish `hlow : Filter.Tendsto (fun N : ℕ => y - 1 / (N : ℝ)) Filter.atTop (nhds y)`. Establish `h0` using `(tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => y) Filter.atTop (nhds y)).sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))`. Simplify using `using h0`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_gt_atTop 0] with N hN`.

Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`. Rewrite using `[le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']`. Use `Int.sub_one_lt_floor ((N : ℝ) * y)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `filter_upwards [Filter.eventually_gt_atTop 0] with N hN`.

Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`. Rewrite using `[div_le_iff₀ hN']`. Use `Int.floor_le ((N : ℝ) * y)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tendsto_intFloor_mul_div (y : ℝ) :
    Filter.Tendsto (fun N : ℕ => ((⌊(N : ℝ) * y⌋ : ℤ) : ℝ) / N) Filter.atTop (nhds y) := by
  have hlow : Filter.Tendsto (fun N : ℕ => y - 1 / (N : ℝ)) Filter.atTop (nhds y) := by
    have h0 := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => y) Filter.atTop (nhds y)).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']
    have := Int.sub_one_lt_floor ((N : ℝ) * y)
    linarith
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    have := Int.floor_le ((N : ℝ) * y)
    linarith

/- English proof (translation)
Introduce `ι _ n Λ₁ Λ₂ h t`. Set `g : (ι → ℝ) → ℝ` to `fun t => (Λ₁ - Λ₂) ((∑ x, MvPolynomial.C (t x) * MvPolynomial.X x) ^ n)`. Establish `hg : ∀ t, g t = ∑ s : Fin n → ι, (∏ i, t (s i)) * (Λ₁ - Λ₂) (∏ i, MvPolynomial.X (s i))` using `fun t => linForm_pow_expand n (Λ₁ - Λ₂) t`. Establish `hcont : Continuous g`. Establish `: g = fun t => ∑ s : Fin n → ι, (∏ i, t (s i)) * (Λ₁ - Λ₂) (∏ i, MvPolynomial.X (s i))`.

Use function extensionality and compare the values at `hg`. Rewrite using `[this]`. Use `fun_prop`. Establish `hhom : ∀ (c : ℝ) (t : ι → ℝ), g (fun x => c * t x) = c ^ n * g t`. Introduce `c t`.

Rewrite using `[hg, hg, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Establish `hZ : ∀ a : ι → ℤ, g (fun x => (a x : ℝ)) = 0`.

Introduce `a`. Simplify using `only [g, LinearMap.sub_apply, h a, sub_self]`. Establish `hlim : Filter.Tendsto (fun N : ℕ => fun x => ((N : ℝ))⁻¹ * ((⌊(N : ℝ) * t x⌋ : ℤ) : ℝ)) Filter.atTop (nhds t)`. Rewrite using `[tendsto_pi_nhds]`. Introduce `x`.

Simplify `tendsto_intFloor_mul_div (t x)` using `[div_eq_inv_mul]`. Establish `hzero : g t = 0`. Establish `h1` using `(hcont.tendsto t).comp hlim`. Establish `h2 : (g ∘ fun N : ℕ => fun x => ((N : ℝ))⁻¹ * ((⌊(N : ℝ) * t x⌋ : ℤ) : ℝ)) = fun _ => 0`. Use function extensionality and compare the values at `N`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[hhom, hZ (fun x => ⌊(N : ℝ) * t x⌋), mul_zero]`. Rewrite `h1` using `[h2]`. Conclude with `tendsto_nhds_unique h1 tendsto_const_nhds`. Use `hzero` as an intermediate fact.

Simplify using `only [g, LinearMap.sub_apply, sub_eq_zero] at this`. Conclude with `this`.
-/
theorem linForm_pow_ext_of_int : ∀ {ι : Type} [Fintype ι] (n : ℕ) (Λ₁ Λ₂ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ a : ι → ℤ, Λ₁ ((∑ x, MvPolynomial.C (a x : ℝ) * MvPolynomial.X x) ^ n) = Λ₂ ((∑ x, MvPolynomial.C (a x : ℝ) * MvPolynomial.X x) ^ n)) → ∀ t : ι → ℝ, Λ₁ ((∑ x, MvPolynomial.C (t x) * MvPolynomial.X x) ^ n) = Λ₂ ((∑ x, MvPolynomial.C (t x) * MvPolynomial.X x) ^ n) := by
  intro ι _ n Λ₁ Λ₂ h t
  let g : (ι → ℝ) → ℝ := fun t =>
    (Λ₁ - Λ₂) ((∑ x, MvPolynomial.C (t x) * MvPolynomial.X x) ^ n)
  have hg : ∀ t, g t = ∑ s : Fin n → ι, (∏ i, t (s i)) * (Λ₁ - Λ₂) (∏ i, MvPolynomial.X (s i)) :=
    fun t => linForm_pow_expand n (Λ₁ - Λ₂) t
  have hcont : Continuous g := by
    have : g = fun t => ∑ s : Fin n → ι, (∏ i, t (s i)) * (Λ₁ - Λ₂) (∏ i, MvPolynomial.X (s i)) :=
      funext hg
    rw [this]
    fun_prop
  have hhom : ∀ (c : ℝ) (t : ι → ℝ), g (fun x => c * t x) = c ^ n * g t := by
    intro c t
    rw [hg, hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hZ : ∀ a : ι → ℤ, g (fun x => (a x : ℝ)) = 0 := by
    intro a
    simp only [g, LinearMap.sub_apply, h a, sub_self]
  have hlim : Filter.Tendsto (fun N : ℕ => fun x => ((N : ℝ))⁻¹ * ((⌊(N : ℝ) * t x⌋ : ℤ) : ℝ))
      Filter.atTop (nhds t) := by
    rw [tendsto_pi_nhds]
    intro x
    simpa [div_eq_inv_mul] using tendsto_intFloor_mul_div (t x)
  have hzero : g t = 0 := by
    have h1 := (hcont.tendsto t).comp hlim
    have h2 : (g ∘ fun N : ℕ => fun x => ((N : ℝ))⁻¹ * ((⌊(N : ℝ) * t x⌋ : ℤ) : ℝ)) = fun _ => 0 := by
      funext N
      simp only [Function.comp_apply]
      rw [hhom, hZ (fun x => ⌊(N : ℝ) * t x⌋), mul_zero]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have := hzero
  simp only [g, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GlobalTheory
