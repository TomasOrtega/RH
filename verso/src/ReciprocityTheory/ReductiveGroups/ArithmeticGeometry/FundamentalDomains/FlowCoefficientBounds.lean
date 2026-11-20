import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowIsotropicPairs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds

namespace ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Introduce `h`. Establish `h1` using `(hx τ).2 i`. Rewrite `h1` using `[h]`. Simplify using `at h1`.
-/
theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have h1 := (hx τ).2 i
  rw [h] at h1
  simp at h1

/- English proof (translation)
Unfold `Data.nfac`. Use `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_` and prove the remaining obligations. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Rewrite using `[norm_pos_iff]`. Conclude with `div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _)`.
-/
theorem nfac_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_
  apply Real.rpow_pos_of_pos
  rw [norm_pos_iff]
  exact div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _)

/- English proof (translation)
Rewrite using `[Complex.norm_exp, Real.exp_eq_one_iff]`. Simplify using `[Complex.mul_re, Complex.mul_im, hz]`.
-/
theorem norm_cexp_I (z : ℂ) (hz : z.im = 0) : ‖cexp (-(4 * (Real.pi : ℂ) * I) * z)‖ = 1 := by
  rw [Complex.norm_exp, Real.exp_eq_one_iff]
  simp [Complex.mul_re, Complex.mul_im, hz]

/- English proof (translation)
Use `set A := ∑ p, ∑ q, v p * g p q * conj (z q) with hA`. Use `set B := ∑ p, ∑ q, w p * g p q * conj (z q) with hB`. Establish `hB' : conj B = ∑ a, ∑ b, z a * g a b * conj (w b)`. Rewrite using `[hB, map_sum]`. Repeatedly rewrite using `[map_sum, map_mul, Complex.conj_conj, hg]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Establish `expand : ∀ a b, (v a - α * A * z a) * g a b * conj (w b - α * B * z b) = v a * g a b * conj (w b) + α * (conj B * (v a * g a b * conj (z b))) - α * A * (z a * g a b * conj (w b)) - α * α * A * conj B * (z a * g a b * conj (z b))`. Introduce `a b`. Simplify using `only [map_sub, map_mul, hα]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[expand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]`. Rewrite using `[← hA, ← hB', hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg {r : ℕ} (g : Fin r → Fin r → ℂ) (hg : ∀ a b, conj (g a b) = g b a)
    (z v w : Fin r → ℂ) (α : ℂ) (hα : conj α = -α)
    (hz : ∑ a, ∑ b, z a * g a b * conj (z b) = 0) :
    ∑ a, ∑ b, (v a - α * (∑ p, ∑ q, v p * g p q * conj (z q)) * z a) * g a b *
        conj (w b - α * (∑ p, ∑ q, w p * g p q * conj (z q)) * z b) =
      ∑ a, ∑ b, v a * g a b * conj (w b) := by
  set A := ∑ p, ∑ q, v p * g p q * conj (z q) with hA
  set B := ∑ p, ∑ q, w p * g p q * conj (z q) with hB
  have hB' : conj B = ∑ a, ∑ b, z a * g a b * conj (w b) := by
    rw [hB, map_sum]
    simp_rw [map_sum, map_mul, Complex.conj_conj, hg]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have expand : ∀ a b, (v a - α * A * z a) * g a b * conj (w b - α * B * z b) =
      v a * g a b * conj (w b) + α * (conj B * (v a * g a b * conj (z b))) -
        α * A * (z a * g a b * conj (w b)) - α * α * A * conj B * (z a * g a b * conj (z b)) := by
    intro a b
    simp only [map_sub, map_mul, hα]
    ring
  simp_rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← hA, ← hB', hz]
  ring

/- English proof (translation)
Establish `hflow : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) = gram τ.1 X.Gm (mat x τ) ∧ (X.flowMat ξ τ (s τ)).det = 1`. Introduce `τ`. Establish `hg : ∀ p q, conj (τ.1 (X.Gm p q)) = τ.1 (X.Gm q p)` using `fun p q => by`. Rewrite using `[← X.Gm_herm p q, cc, IsCMField.complexEmbedding_complexConj]`. Establish `hz : ∑ a, ∑ b, τ.1 (ξ a) * τ.1 (X.Gm a b) * conj (τ.1 (ξ b)) = 0`.

Establish `h0` using `congrArg τ.1 hξ.2.1`. Simplify using `only [herm, map_sum, map_mul, map_zero, cc, IsCMField.complexEmbedding_complexConj] at h0`. Conclude with `h0`. Establish `hα : conj (I * (X.c τ : ℂ) * (s τ : ℂ)) = -(I * (X.c τ : ℂ) * (s τ : ℂ))`. Rewrite using `[map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]`.

Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Use extensionality with `a b show hermC τ.1 X.Gm (col (X.flowMat ξ τ (s τ) * mat x τ) a) (col (X.flowMat ξ τ (s τ) * mat x τ) b) = hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b)`. Establish `hcol : ∀ c : Fin r, col (X.flowMat ξ τ (s τ) * mat x τ) c = fun p => col (mat x τ) c p - (I * (X.c τ : ℂ) * (s τ : ℂ)) * (∑ p', ∑ q, col (mat x τ) c p' * τ.1 (X.Gm p' q) * conj (τ.1 (ξ q))) * τ.1 (ξ p)`. Introduce `c`.

Use function extensionality and compare the values at `p`. Simplify using `only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]`. Use `congr 1`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring`.

Unfold `hermC`. Rewrite using `[hcol a, hcol b]`. Conclude with `sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (fun p q => τ.1 (X.Gm p q)) hg (fun q => τ.1 (ξ q)) (col (mat x τ) a) (col (mat x τ) b) (I * (X.c τ : ℂ) * (s τ : ℂ)) hα hz`. Establish `hT : X.flowMat ξ τ (s τ) = 1 + Matrix.replicateCol (Fin 1) (fun a => -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ a))) * Matrix.replicateRow (Fin 1) (fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k)))`. Use extensionality with `a b`.

Apply the tactic sequence `simp [Data.flowMat, Matrix.mul_apply, Matrix.one_apply] <;> ring`. Establish `h5 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) = 0`. Establish `h6 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) = -(I * (X.c τ : ℂ) * (s τ : ℂ)) * ∑ b, ∑ k, τ.1 (ξ b) * τ.1 (X.Gm b k) * conj (τ.1 (ξ k))`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[h6, hz, mul_zero]`. Rewrite using `[hT]`. Use `(Matrix.det_one_add_replicateCol_mul_replicateRow _ _).trans ?_` and prove the remaining obligations.

Simplify using `only [dotProduct]`. Rewrite using `[h5, add_zero]`. Establish `hdmin : ∀ τ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i`. Introduce `τ i`. Unfold `dmin`.

Rewrite using `[(hflow τ).1]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ∀ τ : X.Ψ, (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i).re`. Introduce `τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations.

Use `show (X.flowMat ξ τ (s τ) * mat x τ).det ≠ 0`. Rewrite using `[Matrix.det_mul, (hflow τ).2, one_mul]`. Conclude with `(hx τ).1`. Rewrite using `[hdmin]`. Conclude with `(hx τ).2 i`.

Unfold `Data.nfac`. Simplify using `only [hdmin]`.
-/
theorem flow_real {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℝ) (la : Wt X.Ψ r) :
    X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := by
  have hflow : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) =
      gram τ.1 X.Gm (mat x τ) ∧ (X.flowMat ξ τ (s τ)).det = 1 := by
    intro τ
    have hg : ∀ p q, conj (τ.1 (X.Gm p q)) = τ.1 (X.Gm q p) := fun p q => by
      rw [← X.Gm_herm p q, cc, IsCMField.complexEmbedding_complexConj]
    have hz : ∑ a, ∑ b, τ.1 (ξ a) * τ.1 (X.Gm a b) * conj (τ.1 (ξ b)) = 0 := by
      have h0 := congrArg τ.1 hξ.2.1
      simp only [herm, map_sum, map_mul, map_zero, cc, IsCMField.complexEmbedding_complexConj] at h0
      exact h0
    have hα : conj (I * (X.c τ : ℂ) * (s τ : ℂ)) = -(I * (X.c τ : ℂ) * (s τ : ℂ)) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    constructor
    · ext a b
      show hermC τ.1 X.Gm (col (X.flowMat ξ τ (s τ) * mat x τ) a) (col (X.flowMat ξ τ (s τ) * mat x τ) b) =
        hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b)
      have hcol : ∀ c : Fin r, col (X.flowMat ξ τ (s τ) * mat x τ) c = fun p => col (mat x τ) c p -
          (I * (X.c τ : ℂ) * (s τ : ℂ)) * (∑ p', ∑ q, col (mat x τ) c p' * τ.1 (X.Gm p' q) * conj (τ.1 (ξ q))) * τ.1 (ξ p) := by
        intro c
        funext p
        simp only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
          ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
      unfold hermC
      rw [hcol a, hcol b]
      exact sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (fun p q => τ.1 (X.Gm p q)) hg (fun q => τ.1 (ξ q)) (col (mat x τ) a)
        (col (mat x τ) b) (I * (X.c τ : ℂ) * (s τ : ℂ)) hα hz
    · have hT : X.flowMat ξ τ (s τ) = 1 + Matrix.replicateCol (Fin 1) (fun a => -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ a))) *
          Matrix.replicateRow (Fin 1) (fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) := by
        ext a b
        simp [Data.flowMat, Matrix.mul_apply, Matrix.one_apply] <;> ring
      have h5 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) = 0 := by
        have h6 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) =
            -(I * (X.c τ : ℂ) * (s τ : ℂ)) * ∑ b, ∑ k, τ.1 (ξ b) * τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h6, hz, mul_zero]
      rw [hT]
      refine (Matrix.det_one_add_replicateCol_mul_replicateRow _ _).trans ?_
      simp only [dotProduct]
      rw [h5, add_zero]
  have hdmin : ∀ τ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i := by
    intro τ i
    unfold dmin
    rw [(hflow τ).1]
  refine ⟨?_, ?_⟩
  · show ∀ τ : X.Ψ, (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i).re
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · show (X.flowMat ξ τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, (hflow τ).2, one_mul]
      exact (hx τ).1
    · rw [hdmin]
      exact (hx τ).2 i
  · unfold Data.nfac
    simp only [hdmin]

/- English proof (translation)
Establish `hpos` using `nfac_pos X hx la`. Express the relevant statement in the definitionally equal form `‖X.fj la ξ ν P x‖ * X.nfac la x ≤ C`. Establish `hC : 0 ≤ C` using `le_trans (by unfold Data.pnorm; positivity) (hP x hx)`. Unfold `Data.fj`. Use `split_ifs with h1 h2`.

Take `⟨-, -, hD0, hDt⟩` from `h2.choose_spec`. Rewrite using `[← le_div_iff₀ hpos, norm_mul]`. Establish `hpt : ∀ s : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤ C / X.nfac la x`. Introduce `s`. Take `⟨hd, hn⟩` from `flow_real X hξ hx s la`.

Rewrite using `[norm_mul, norm_cexp_I _ (by rw [Complex.im_sum]; simp), mul_one, le_div_iff₀ hpos, ← hn]`. Conclude with `hP _ hd`. Use `haveI : IsFiniteMeasure (volume.restrict h2.choose) := ⟨by rw [Measure.restrict_apply_univ]; exact hDt⟩`. Establish `hI` using `norm_integral_le_of_norm_le_const (μ := volume.restrict h2.choose) (ae_of_all _ hpt)`. Rewrite `hI` using `[measureReal_def, Measure.restrict_apply_univ]`.

Establish `hv : 0 < (volume h2.choose).toReal` using `ENNReal.toReal_pos hD0.ne' hDt.ne`. Simplify using `only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]`. Use `(mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hv.le)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_comm (C / X.nfac la x) _, ← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]`. Simplify using `[hC]`.

Simplify using `[hC]`.
-/
theorem fj_bound (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C : ℝ)
    (hP : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la (X.fj la ξ ν P) x ≤ C := by
  have hpos := nfac_pos X hx la
  change ‖X.fj la ξ ν P x‖ * X.nfac la x ≤ C
  have hC : 0 ≤ C := le_trans (by unfold Data.pnorm; positivity) (hP x hx)
  unfold Data.fj
  split_ifs with h1 h2
  · obtain ⟨-, -, hD0, hDt⟩ := h2.choose_spec
    rw [← le_div_iff₀ hpos, norm_mul]
    have hpt : ∀ s : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
        cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤ C / X.nfac la x := by
      intro s
      obtain ⟨hd, hn⟩ := flow_real X hξ hx s la
      rw [norm_mul, norm_cexp_I _ (by rw [Complex.im_sum]; simp), mul_one, le_div_iff₀ hpos, ← hn]
      exact hP _ hd
    haveI : IsFiniteMeasure (volume.restrict h2.choose) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hDt⟩
    have hI := norm_integral_le_of_norm_le_const (μ := volume.restrict h2.choose) (ae_of_all _ hpt)
    rw [measureReal_def, Measure.restrict_apply_univ] at hI
    have hv : 0 < (volume h2.choose).toReal := ENNReal.toReal_pos hD0.ne' hDt.ne
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
    refine (mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hv.le)).trans (le_of_eq ?_)
    rw [mul_comm (C / X.nfac la x) _, ← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]
  · simp [hC]
  · simp [hC]

/- English proof (translation)
Take `⟨β, hβ, -, he⟩` from `hb`. Introduce `τ i k`. Rewrite using `[he]`. Simplify using `only [Data.embH]`. Rewrite using `[← hβ i k, cc, IsCMField.complexEmbedding_complexConj]`.
-/
theorem herm_of_LZ {g : ℕ} {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, he⟩ := hb
  intro τ i k
  rw [he]
  simp only [Data.embH]
  rw [← hβ i k, cc, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Introduce `τ i k`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]`.
-/
theorem herm_sum {n : ℕ} (ω : Fin n → X.Ψ → Fin 2 → Fin 2 → ℂ) (hω : ∀ j, IsHermFam (ω j))
    (t : Fin n → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]

/- English proof (translation)
Establish `hpos` using `nfac_pos X hy la`. Express the relevant statement in the definitionally equal form `‖X.fz u g χ G y‖ * X.nfac la y ≤ M`. Unfold `Data.fz`. Use `split_ifs with h1 h2`. Rewrite using `[← le_div_iff₀ hpos]`.

Establish `hpt : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, ‖G (X.Zb u (∑ j, (t j : ℂ) • h2.choose j) y) * cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h2.choose j))‖ ≤ M / X.nfac la y`. Introduce `t`. Establish `hherm : IsHermFam (∑ j, (t j : ℂ) • h2.choose j)` using `herm_sum X _ (fun j => herm_of_LZ X (h2.choose_spec.1 j)) t`. Rewrite using `[norm_mul, norm_cexp_I _ (Complex.ofReal_im _), mul_one, le_div_iff₀ hpos]`. Conclude with `hb _ hherm`.

Establish `hvol : volume (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1) = 1`. Rewrite using `[volume_pi_pi]`. Simplify using `[Real.volume_Icc]`. Use `haveI : IsFiniteMeasure (volume.restrict (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1)) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩`. Use `(norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans ?_` and prove the remaining obligations.

Rewrite using `[measureReal_def, Measure.restrict_apply_univ, hvol]`. Simplify using the standard rewrite rules. Simplify using `[hM]`. Simplify using `[hM]`.
-/
theorem fz_bound (u : Fin 2 → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ)
    (G : Frame X.Ψ r → ℂ) (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ b, IsHermFam b → ‖G (X.Zb u b y)‖ * X.nfac la y ≤ M) :
    X.pnorm la (X.fz u g χ G) y ≤ M := by
  have hpos := nfac_pos X hy la
  change ‖X.fz u g χ G y‖ * X.nfac la y ≤ M
  unfold Data.fz
  split_ifs with h1 h2
  · rw [← le_div_iff₀ hpos]
    have hpt : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, ‖G (X.Zb u (∑ j, (t j : ℂ) • h2.choose j) y) *
        cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h2.choose j))‖ ≤ M / X.nfac la y := by
      intro t
      have hherm : IsHermFam (∑ j, (t j : ℂ) • h2.choose j) :=
        herm_sum X _ (fun j => herm_of_LZ X (h2.choose_spec.1 j)) t
      rw [norm_mul, norm_cexp_I _ (Complex.ofReal_im _), mul_one, le_div_iff₀ hpos]
      exact hb _ hherm
    have hvol : volume (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1) = 1 := by
      rw [volume_pi_pi]
      simp [Real.volume_Icc]
    haveI : IsFiniteMeasure (volume.restrict
        (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans ?_
    rw [measureReal_def, Measure.restrict_apply_univ, hvol]
    simp
  · simp [hM]
  · simp [hM]

end ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
