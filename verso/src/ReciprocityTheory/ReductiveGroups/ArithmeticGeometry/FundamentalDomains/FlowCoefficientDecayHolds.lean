import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X la P ξ ν c1 w z0 x a hS χ z hz hf`. Take `⟨hH, hxL, hxξ, hxx, hne, hxp0, hua⟩` from `hS`. Take `⟨-, hSS, hξ, -, -, -, -, hw, hχ, hz0, -⟩` from `hH`. Use `set u : Fin 2 → Fin r → E := ![ξ, (X.NC : E) • x] with hu`. Use `set e := X.uvec u a with he`.

Use `set Q := X.fj la ξ ν P with hQ`. Use `set S1 := sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la Q y} with hS1`. Establish `hpair` using `FlowIsotropicPairs.isIsoPair_of X hξ hxξ hxx hne`. Establish `hmem` using `FlowIsotropicPairs.mem_pair X hξ hxL`. Take `⟨hiso, heξ, hHe, hce⟩` from `FlowIsotropicPairs.e_facts X.toData hξ.2.1 hξ.2.2 hxξ hxx hz0.1 e hxp0 hua`.

Take `⟨httv, hTD1⟩` from `FlowIsotropicPairs.flow_facts X.toData hz0 e hiso heξ hHe hce hz hf`. Establish `hTdom : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom` using `hTD1.1`. Take `⟨CP, hCP⟩` from `hSS.1.2`. Establish `hQb : ∀ y ∈ X.dom, X.pnorm la Q y ≤ CP` using `fun y hy => FlowCoefficientBounds.fj_bound X.toData la P CP hCP hξ ν hy`. Establish `hCP0 : 0 ≤ CP` using `le_trans (mul_nonneg (norm_nonneg _) (FlowCoefficientBounds.nfac_pos X.toData hz la).le) (hQb z hz)`.

Establish `hhat : ∀ y ∈ X.dom, X.hatN la Q y ≤ CP` using `fun y _ => Real.sSup_le (by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy') hCP0`. Establish `hle_hat : ∀ y ∈ X.dom, X.pnorm la Q y ≤ X.hatN la Q y` using `fun y hy => le_csSup ⟨CP, by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy'⟩ ⟨y, hy, fun τ => rfl, rfl⟩`. Establish `hle_S1 : ∀ y ∈ X.FramesOverBasis ξ, X.hatN la Q y ≤ S1` using `fun y hy => le_csSup ⟨CP, by rintro t ⟨y', hy', rfl⟩; exact hhat y' hy'.1⟩ ⟨y, hy, rfl⟩`. Establish `hS10 : 0 ≤ S1` using `le_trans (le_trans (mul_nonneg (norm_nonneg _) (FlowCoefficientBounds.nfac_pos X.toData hz0.1 la).le) (hle_hat z0 hz0.1)) (hle_S1 z0 hz0)`. Take `⟨-, hL1⟩` from `h1 r X.toData u hpair`.

Establish `hT1 : X.pnorm la (X.fz u X.g χ Q) (X.flowV e (fun _ => -(I / 2)) z) ≤ S1`. Use `FlowCoefficientBounds.fz_bound X.toData u X.g χ Q la hTdom S1 hS10 fun b hb => ?_` and prove the remaining obligations. Take `⟨-, -, -, -, -, hnfZ, -, hD1Z, -, -⟩` from `hL1 b hb`. Establish `hZ : X.Zb u b (X.flowV e (fun _ => -(I / 2)) z) ∈ X.FramesOverBasis ξ` using `hD1Z _ hTD1`. Rewrite using `[← hnfZ la _ hTdom]`.

Conclude with `(hle_hat _ hZ.1).trans (hle_S1 _ hZ)`. Establish `hRHS : 0 ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1` using `mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hS10`. Establish `hL3d : ∀ y ∈ X.dom, X.fz u X.g χ Q y = if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P y else 0` using `fun y hy => h3d r X u hpair hmem la P hSS.1.1 hχ ν χ y hy`. Distinguish the cases in `hc : ∀ τ, χ τ 0 0 = (ν τ : ℂ)`. Use `swap`.

Establish `h0 : X.fz u X.g χ Q z = 0` using `by rw [hL3d z hz, if_neg hc] show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _`. Rewrite using `[h0, norm_zero, zero_mul]`. Conclude with `hRHS`. Establish `hGP : ∀ y ∈ X.dom, X.fz u X.g χ Q y = X.fz u X.g χ P y` using `fun y hy => by`. Rewrite using `[hL3d y hy, if_pos hc]`.

Establish `hper` using `(h2 r X u hpair hmem).2.1 la P hSS.1.1 hχ`. Take `⟨⟨hdiff, -, hcov⟩, -, -⟩` from `h3 r X.toData u X.g hpair X.g_pos la P hSS.1.1.1 hSS.1.1.2.1 hper χ`. Take `⟨-, -, -, -, -, -, -, -, -, hRF⟩` from `hL1 0 (fun τ i k => by simp)`. Establish `hreal : ∀ s : X.Ψ → ℝ, X.fz u X.g χ P (X.flowV e (fun τ => (s τ : ℂ)) z) = cexp (4 * Real.pi * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ) * X.fz u X.g χ P z`. Introduce `s`.

Establish `hb : IsHermFam (fun τ (i k : Fin 2) => (s τ : ℂ) * a τ i * conj (a τ k))`. Introduce `τ i k`. Simplify using `only [map_mul, Complex.conj_ofReal, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRF' : X.flowV e (fun τ => (s τ : ℂ)) z = X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) z` using `hRF a s z`.

Establish `hpr : X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) = ∑ τ, (X.chiAt χ a τ).re * s τ`. Unfold `Data.pairR Data.chiAt`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `: ∑ i, ∑ k, χ τ i k * ((s τ : ℂ) * a τ i * conj (a τ k)) = (s τ : ℂ) * ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)`.

Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[this, Complex.re_ofReal_mul, mul_comm]`. Rewrite using `[hRF', hcov _ hb z hz, hpr, Complex.ofReal_sum]`. Simplify using `only [Complex.ofReal_mul]`.

Establish `hL4` using `h4 r X.toData e hiso (X.fz u X.g χ P) hdiff (fun τ => ((X.chiAt χ a τ).re : ℂ)) z hz hreal (fun _ => -(I / 2)) hTdom`. Establish `hexp : 4 * (Real.pi : ℂ) * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * -(I / 2) = ((2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re : ℝ) : ℂ)`. Rewrite using `[← Finset.sum_mul]`. Use `push_cast`. Take the linear combination `(-2 * (Real.pi : ℂ) * ∑ τ, ((X.chiAt χ a τ).re : ℂ)) * Complex.I_sq`.

Rewrite `hL4` using `[hexp]`. Establish `hnorm : ‖X.fz u X.g χ P z‖ = Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖`. Rewrite using `[hL4, norm_mul, Complex.norm_exp_ofReal, ← mul_assoc, ← Real.exp_add, show -Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re) + 2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re = 0 by ring, Real.exp_zero, one_mul]`. Establish `hq` using `m3bNorm_holds r X.toData e hiso la z hz (fun _ => -(I / 2)) hTdom`. Establish `hq2 : X.nfac la z / X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2)`.

Use `hq.2.trans (le_of_eq (Finset.prod_congr rfl fun τ _ => ?_))` and prove the remaining obligations. Simplify using `only [httv τ]`. Evaluate the numerical expressions using `[max_def]`. Establish `hprod : ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) ≤ 2 ^ (w / 2)`. Rewrite using `[← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]`.

Apply `Real.rpow_le_rpow_of_exponent_le (by norm_num)` to reduce the goal to its premises. Rewrite using `[← Finset.sum_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnT` using `FlowCoefficientBounds.nfac_pos X.toData hTdom la`. Establish `hnf : X.nfac la z ≤ 2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z)`.

Rewrite `hq2` using `[div_le_iff₀ hnT]`. Conclude with `hq2.trans (mul_le_mul_of_nonneg_right hprod hnT.le)`. Establish `hT1' : ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ * X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ S1`. Rewrite using `[← hGP _ hTdom]`. Conclude with `hT1`.

Use `show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _`. Rewrite using `[hGP z hz, hnorm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem flow_coefficient_decay_holds (h1 : UnipotentVectorGroup (E := E)) (h2 : UnipotentLatticeLift (E := E))
    (h3 : FourierCoefficientProperties (E := E)) (h3d : FourierCoefficientSupport (E := E)) (h4 : HolomorphicPeriodicityExtension (E := E)) :
    FlowCoefficientDecay (E := E) := by
  intro r X la P ξ ν c1 w z0 x a hS χ z hz hf
  obtain ⟨hH, hxL, hxξ, hxx, hne, hxp0, hua⟩ := hS
  obtain ⟨-, hSS, hξ, -, -, -, -, hw, hχ, hz0, -⟩ := hH
  set u : Fin 2 → Fin r → E := ![ξ, (X.NC : E) • x] with hu
  set e := X.uvec u a with he
  set Q := X.fj la ξ ν P with hQ
  set S1 := sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la Q y} with hS1
  have hpair := FlowIsotropicPairs.isIsoPair_of X hξ hxξ hxx hne
  have hmem := FlowIsotropicPairs.mem_pair X hξ hxL
  obtain ⟨hiso, heξ, hHe, hce⟩ :=
    FlowIsotropicPairs.e_facts X.toData hξ.2.1 hξ.2.2 hxξ hxx hz0.1 e hxp0 hua
  obtain ⟨httv, hTD1⟩ := FlowIsotropicPairs.flow_facts X.toData hz0 e hiso heξ hHe hce hz hf
  have hTdom : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := hTD1.1

  obtain ⟨CP, hCP⟩ := hSS.1.2
  have hQb : ∀ y ∈ X.dom, X.pnorm la Q y ≤ CP := fun y hy =>
    FlowCoefficientBounds.fj_bound X.toData la P CP hCP hξ ν hy
  have hCP0 : 0 ≤ CP :=
    le_trans (mul_nonneg (norm_nonneg _) (FlowCoefficientBounds.nfac_pos X.toData hz la).le) (hQb z hz)
  have hhat : ∀ y ∈ X.dom, X.hatN la Q y ≤ CP := fun y _ =>
    Real.sSup_le (by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy') hCP0
  have hle_hat : ∀ y ∈ X.dom, X.pnorm la Q y ≤ X.hatN la Q y := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy'⟩ ⟨y, hy, fun τ => rfl, rfl⟩
  have hle_S1 : ∀ y ∈ X.FramesOverBasis ξ, X.hatN la Q y ≤ S1 := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', rfl⟩; exact hhat y' hy'.1⟩ ⟨y, hy, rfl⟩
  have hS10 : 0 ≤ S1 := le_trans (le_trans (mul_nonneg (norm_nonneg _)
    (FlowCoefficientBounds.nfac_pos X.toData hz0.1 la).le) (hle_hat z0 hz0.1)) (hle_S1 z0 hz0)

  obtain ⟨-, hL1⟩ := h1 r X.toData u hpair
  have hT1 : X.pnorm la (X.fz u X.g χ Q) (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    refine FlowCoefficientBounds.fz_bound X.toData u X.g χ Q la hTdom S1 hS10 fun b hb => ?_
    obtain ⟨-, -, -, -, -, hnfZ, -, hD1Z, -, -⟩ := hL1 b hb
    have hZ : X.Zb u b (X.flowV e (fun _ => -(I / 2)) z) ∈ X.FramesOverBasis ξ := hD1Z _ hTD1
    rw [← hnfZ la _ hTdom]
    exact (hle_hat _ hZ.1).trans (hle_S1 _ hZ)
  have hRHS : 0 ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 :=
    mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hS10

  have hL3d : ∀ y ∈ X.dom, X.fz u X.g χ Q y =
      if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P y else 0 := fun y hy =>
    h3d r X u hpair hmem la P hSS.1.1 hχ ν χ y hy
  by_cases hc : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
  swap
  · have h0 : X.fz u X.g χ Q z = 0 := by rw [hL3d z hz, if_neg hc]
    show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
    rw [h0, norm_zero, zero_mul]
    exact hRHS
  have hGP : ∀ y ∈ X.dom, X.fz u X.g χ Q y = X.fz u X.g χ P y := fun y hy => by
    rw [hL3d y hy, if_pos hc]

  have hper := (h2 r X u hpair hmem).2.1 la P hSS.1.1 hχ
  obtain ⟨⟨hdiff, -, hcov⟩, -, -⟩ :=
    h3 r X.toData u X.g hpair X.g_pos la P hSS.1.1.1 hSS.1.1.2.1 hper χ

  obtain ⟨-, -, -, -, -, -, -, -, -, hRF⟩ := hL1 0 (fun τ i k => by simp)
  have hreal : ∀ s : X.Ψ → ℝ, X.fz u X.g χ P (X.flowV e (fun τ => (s τ : ℂ)) z) =
      cexp (4 * Real.pi * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ) * X.fz u X.g χ P z := by
    intro s
    have hb : IsHermFam (fun τ (i k : Fin 2) => (s τ : ℂ) * a τ i * conj (a τ k)) := by
      intro τ i k
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    have hRF' : X.flowV e (fun τ => (s τ : ℂ)) z =
        X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) z := hRF a s z
    have hpr : X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) =
        ∑ τ, (X.chiAt χ a τ).re * s τ := by
      unfold Data.pairR Data.chiAt
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have : ∑ i, ∑ k, χ τ i k * ((s τ : ℂ) * a τ i * conj (a τ k)) =
          (s τ : ℂ) * ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [this, Complex.re_ofReal_mul, mul_comm]
    rw [hRF', hcov _ hb z hz, hpr, Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
  have hL4 := h4 r X.toData e hiso (X.fz u X.g χ P) hdiff
    (fun τ => ((X.chiAt χ a τ).re : ℂ)) z hz hreal (fun _ => -(I / 2)) hTdom
  have hexp : 4 * (Real.pi : ℂ) * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * -(I / 2) =
      ((2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re : ℝ) : ℂ) := by
    rw [← Finset.sum_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ τ, ((X.chiAt χ a τ).re : ℂ)) * Complex.I_sq
  rw [hexp] at hL4
  have hnorm : ‖X.fz u X.g χ P z‖ = Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
      ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ := by
    rw [hL4, norm_mul, Complex.norm_exp_ofReal, ← mul_assoc, ← Real.exp_add,
      show -Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re) + 2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re = 0 by
        ring, Real.exp_zero, one_mul]

  have hq := m3bNorm_holds r X.toData e hiso la z hz (fun _ => -(I / 2)) hTdom
  have hq2 : X.nfac la z / X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤
      ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) := by
    refine hq.2.trans (le_of_eq (Finset.prod_congr rfl fun τ _ => ?_))
    simp only [httv τ]
    norm_num [max_def]
  have hprod : ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) ≤ 2 ^ (w / 2) := by
    rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [← Finset.sum_div]
    linarith
  have hnT := FlowCoefficientBounds.nfac_pos X.toData hTdom la
  have hnf : X.nfac la z ≤ 2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z) := by
    rw [div_le_iff₀ hnT] at hq2
    exact hq2.trans (mul_le_mul_of_nonneg_right hprod hnT.le)

  have hT1' : ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
      X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    rw [← hGP _ hTdom]
    exact hT1
  show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
  rw [hGP z hz, hnorm]
  calc Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ * X.nfac la z
      ≤ Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          (2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by gcongr
    _ = 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        (‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by ring
    _ ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 := by gcongr

end ReciprocityTheory.ChartRestriction.G.FD
