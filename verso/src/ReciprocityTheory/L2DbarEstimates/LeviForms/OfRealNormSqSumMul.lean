import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

open Complex ComplexConjugate Filter Topology

namespace ReciprocityTheory.L2DbarEstimates

def LeviChainStatement : Prop :=
  ∀ (n : ℕ) (k : ℝ → ℝ) (v : V n → ℝ) (x : V n) (ξ : Fin n → ℂ),
    ContDiffAt ℝ 2 v x → ContDiffAt ℝ 2 k (v x) →
    leviV n (fun y => ((k (v y) : ℝ) : ℂ)) x ξ =
      ((deriv k (v x) : ℝ) : ℂ) * leviV n (fun y => ((v y : ℝ) : ℂ)) x ξ +
      ((deriv (deriv k) (v x) : ℝ) : ℂ) *
        ((Complex.normSq (∑ j, wd n j (fun y => ((v y : ℝ) : ℂ)) x * ξ j) : ℝ) : ℂ)

def LSEVStatement : Prop :=
  ∀ (n m : ℕ) (U : Set (V n)) (u : Fin m → V n → ℝ), IsOpen U →
    (∀ i, (∃ φ : V n → ℝ, ContDiffOn ℝ 2 φ U ∧ LeviNonnegOn n φ U ∧
              ∀ y ∈ U, u i y = Real.exp (φ y)) ∨
          (∃ g : V n → ℂ, ContDiffOn ℂ 2 g U ∧ ∀ y ∈ U, u i y = Complex.normSq (g y))) →
    (∀ y ∈ U, 0 < ∑ i, u i y) →
    LeviNonnegOn n (fun y => Real.log (∑ i, u i y)) U

def LogPshAt (n : ℕ) (u : V n → ℝ) (x : V n) : Prop :=
  0 ≤ u x ∧ ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (u y : ℂ)) x ξ).re ∧
    Complex.normSq (∑ j, wd n j (fun y => (u y : ℂ)) x * ξ j) ≤
      u x * (leviV n (fun y => (u y : ℂ)) x ξ).re

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[← mul_conj, map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ofReal_normSq_sum_mul (a ξ : Fin n → ℂ) :
    ((Complex.normSq (∑ j, a j * ξ j) : ℝ) : ℂ) =
      ∑ j, ∑ kk, a j * conj (a kk) * ξ j * conj (ξ kk) := by
  rw [← mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_
  rw [map_mul]; ring

/- English proof (translation)
Introduce `n k v x ξ hv hk`. Establish `hv1 : DifferentiableAt ℝ v x` using `hv.differentiableAt (by simp)`. Establish `hk1 : DifferentiableAt ℝ (deriv k) (v x)` using `differentiableAt_deriv_of_contDiffAt hk`. Establish `hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x` using `ofRealCLM.contDiff.contDiffAt.comp x hv`. Establish `hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y` using `eventually_differentiableAt_of_contDiffAt hv`.

Establish `hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y)` using `hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)`. Establish `hE : ∀ kk : Fin n, wdb n kk (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x] fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n kk (fun y => ((v y : ℝ) : ℂ)) y`. Introduce `kk`. Use `filter_upwards [hvd, hkd] with y hy1 hy2`. Conclude with `wdb_ofReal_comp hy2 hy1`.

Establish `hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x` using `differentiableAt_ofReal (hk1.comp x hv1)`. Establish `hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => ((k (v y) : ℝ) : ℂ))) x = ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x * conj (wd n kk (fun y => ((v y : ℝ) : ℂ)) x) + ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n kk (fun y => ((v y : ℝ) : ℂ))) x`. Introduce `j kk`. Rewrite using `[wd_congr (hE kk), wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n kk (fun y => ((v y : ℝ) : ℂ))) hD1 (differentiableAt_wdb hv'), wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]`. Rewrite using `[ofReal_normSq_sum_mul]`.

Simplify using `only [leviV, hterm, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviChain : LeviChainStatement := by
  intro n k v x ξ hv hk
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  have hk1 : DifferentiableAt ℝ (deriv k) (v x) := differentiableAt_deriv_of_contDiffAt hk
  have hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x :=
    ofRealCLM.contDiff.contDiffAt.comp x hv
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y := eventually_differentiableAt_of_contDiffAt hv
  have hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y) :=
    hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)
  have hE : ∀ kk : Fin n, wdb n kk (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n kk (fun y => ((v y : ℝ) : ℂ)) y := by
    intro kk
    filter_upwards [hvd, hkd] with y hy1 hy2
    exact wdb_ofReal_comp hy2 hy1
  have hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x :=
    differentiableAt_ofReal (hk1.comp x hv1)
  have hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => ((k (v y) : ℝ) : ℂ))) x =
      ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x *
          conj (wd n kk (fun y => ((v y : ℝ) : ℂ)) x) +
        ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n kk (fun y => ((v y : ℝ) : ℂ))) x := by
    intro j kk
    rw [wd_congr (hE kk),
      wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n kk (fun y => ((v y : ℝ) : ℂ)))
        hD1 (differentiableAt_wdb hv'),
      wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]
  rw [ofReal_normSq_sum_mul]
  simp only [leviV, hterm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_
  ring

/- English proof (translation)
Establish `h1 : ‖∑ i, a i‖ ≤ ∑ i, √(u i) * √(L i)`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← Real.sqrt_mul (hu i), ← Real.sqrt_sq (norm_nonneg (a i))]`. Conclude with `Real.sqrt_le_sqrt (by rw [← normSq_eq_norm_sq]; exact h i)`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => √(u i)) (fun i => √(L i))`.

Establish `e1 : ∀ i, √(u i) ^ 2 = u i` using `fun i => Real.sq_sqrt (hu i)`. Establish `e2 : ∀ i, √(L i) ^ 2 = L i` using `fun i => Real.sq_sqrt (hL i)`. Simplify using `only [e1, e2] at h2`. Rewrite using `[normSq_eq_norm_sq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem normSq_sum_le_of_le {m : ℕ} (a : Fin m → ℂ) (u L : Fin m → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hL : ∀ i, 0 ≤ L i) (h : ∀ i, Complex.normSq (a i) ≤ u i * L i) :
    Complex.normSq (∑ i, a i) ≤ (∑ i, u i) * ∑ i, L i := by
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, √(u i) * √(L i) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← Real.sqrt_mul (hu i), ← Real.sqrt_sq (norm_nonneg (a i))]
    exact Real.sqrt_le_sqrt (by rw [← normSq_eq_norm_sq]; exact h i)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => √(u i)) (fun i => √(L i))
  have e1 : ∀ i, √(u i) ^ 2 = u i := fun i => Real.sq_sqrt (hu i)
  have e2 : ∀ i, √(L i) ^ 2 = L i := fun i => Real.sq_sqrt (hL i)
  simp only [e1, e2] at h2
  rw [normSq_eq_norm_sq]
  calc ‖∑ i, a i‖ ^ 2 ≤ (∑ i, √(u i) * √(L i)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/- English proof (translation)
Establish `hf : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, (u i y : ℂ)`. Use function extensionality and compare the values at `y`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hf, wd_sum Finset.univ (fun i _ => differentiableAt_ofReal (hu i))]`.
-/
theorem wd_ofReal_sum {m : ℕ} {j : Fin n} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x := by
  have hf : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, (u i y : ℂ) := by
    funext y; push_cast; rfl
  rw [hf, wd_sum Finset.univ (fun i _ => differentiableAt_ofReal (hu i))]

/- English proof (translation)
Establish `hf : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, (u i y : ℂ)`. Use function extensionality and compare the values at `y`. Use `push_cast`. Both sides reduce to the same expression. Establish `hc : ∀ i, ContDiffAt ℝ 2 (fun y => (u i y : ℂ)) x` using `fun i => ofRealCLM.contDiff.contDiffAt.comp x (hu i)`.

Establish `hev : ∀ kk : Fin n, wdb n kk (fun y => ∑ i, (u i y : ℂ)) =ᶠ[𝓝 x] fun y => ∑ i, wdb n kk (fun y => (u i y : ℂ)) y`. Introduce `kk`. Establish `: ∀ᶠ y in 𝓝 x, ∀ i, DifferentiableAt ℝ (fun y => (u i y : ℂ)) y`. Rewrite using `[Filter.eventually_all]`. Conclude with `fun i => eventually_differentiableAt_of_contDiffAt (hc i)`.

Use `filter_upwards [this] with y hy`. Conclude with `wdb_sum Finset.univ (fun i _ => hy i)`. Rewrite using `[hf]`. Simplify using `only [leviV, wd_congr (hev _), wd_sum Finset.univ (fun i _ => differentiableAt_wdb (hc i)), Finset.sum_mul]`. Conclude with `(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm`.
-/
theorem leviV_ofReal_sum {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((∑ i, u i y : ℝ) : ℂ)) x ξ = ∑ i, leviV n (fun y => (u i y : ℂ)) x ξ := by
  have hf : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, (u i y : ℂ) := by
    funext y; push_cast; rfl
  have hc : ∀ i, ContDiffAt ℝ 2 (fun y => (u i y : ℂ)) x := fun i =>
    ofRealCLM.contDiff.contDiffAt.comp x (hu i)
  have hev : ∀ kk : Fin n, wdb n kk (fun y => ∑ i, (u i y : ℂ)) =ᶠ[𝓝 x]
      fun y => ∑ i, wdb n kk (fun y => (u i y : ℂ)) y := by
    intro kk
    have : ∀ᶠ y in 𝓝 x, ∀ i, DifferentiableAt ℝ (fun y => (u i y : ℂ)) y := by
      rw [Filter.eventually_all]; exact fun i => eventually_differentiableAt_of_contDiffAt (hc i)
    filter_upwards [this] with y hy
    exact wdb_sum Finset.univ (fun i _ => hy i)
  rw [hf]
  simp only [leviV, wd_congr (hev _),
    wd_sum Finset.univ (fun i _ => differentiableAt_wdb (hc i)), Finset.sum_mul]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/- English proof (translation)
Establish `hc : (fun y => (u y : ℂ)) =ᶠ[𝓝 x] fun y => (w y : ℂ)` using `h.fun_comp (fun t : ℝ => (t : ℂ))`. Take `⟨h0, h1⟩` from `hu`. Use `⟨h.eq_of_nhds ▸ h0, fun ξ => ?_⟩` and prove the remaining obligations. Rewrite using `[← leviV_congr hc ξ, ← h.eq_of_nhds]`. Simplify using `only [← wd_congr hc]`.

Conclude with `h1 ξ`.
-/
theorem LogPshAt.congr {u w : V n → ℝ} {x : V n} (h : u =ᶠ[𝓝 x] w) (hu : LogPshAt n u x) :
    LogPshAt n w x := by
  have hc : (fun y => (u y : ℂ)) =ᶠ[𝓝 x] fun y => (w y : ℂ) := h.fun_comp (fun t : ℝ => (t : ℂ))
  obtain ⟨h0, h1⟩ := hu
  refine ⟨h.eq_of_nhds ▸ h0, fun ξ => ?_⟩
  rw [← leviV_congr hc ξ, ← h.eq_of_nhds]
  simp only [← wd_congr hc]
  exact h1 ξ

/- English proof (translation)
Establish `hφ1 : DifferentiableAt ℝ φ x` using `hφ.differentiableAt (by simp)`. Establish `hexp : ContDiffAt ℝ 2 Real.exp (φ x)` using `Real.contDiff_exp.contDiffAt`. Establish `hd1 : deriv Real.exp (φ x) = Real.exp (φ x)` using `by rw [Real.deriv_exp]`. Establish `hd2 : deriv (deriv Real.exp) (φ x) = Real.exp (φ x)` using `by rw [Real.deriv_exp, Real.deriv_exp]`. Use `⟨(Real.exp_pos _).le, fun ξ => ?_⟩` and prove the remaining obligations.

Establish `hc` using `leviChain n Real.exp φ x ξ hφ hexp`. Establish `hw : ∀ j, wd n j (fun y => ((Real.exp (φ y) : ℝ) : ℂ)) x = ((Real.exp (φ x) : ℝ) : ℂ) * wd n j (fun y => (φ y : ℂ)) x` using `fun j => by`. Rewrite using `[wd_ofReal_comp Real.differentiable_exp.differentiableAt hφ1, hd1]`. Rewrite `hc` using `[hd1, hd2]`. Simplify using `only [hc, hw, mul_assoc, ← Finset.mul_sum, add_re, re_ofReal_mul, normSq_mul, normSq_ofReal, ofReal_re]`.

Use `set e := Real.exp (φ x)`. Establish `he : 0 < e` using `Real.exp_pos _`. Establish `hl` using `hL ξ`. Use `set N := Complex.normSq (∑ j, wd n j (fun y => (φ y : ℂ)) x * ξ j)`. Use `set R := (leviV n (fun y => (φ y : ℂ)) x ξ).re`.

Establish `hN : 0 ≤ N` using `Complex.normSq_nonneg _`. Prove the components needed by the constructor for the conclusion. Check the signs of the components of the expression. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg he.le he.le) hl]`.
-/
theorem logPshAt_exp {φ : V n → ℝ} {x : V n} (hφ : ContDiffAt ℝ 2 φ x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re) :
    LogPshAt n (fun y => Real.exp (φ y)) x := by
  have hφ1 : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hexp : ContDiffAt ℝ 2 Real.exp (φ x) := Real.contDiff_exp.contDiffAt
  have hd1 : deriv Real.exp (φ x) = Real.exp (φ x) := by rw [Real.deriv_exp]
  have hd2 : deriv (deriv Real.exp) (φ x) = Real.exp (φ x) := by rw [Real.deriv_exp, Real.deriv_exp]
  refine ⟨(Real.exp_pos _).le, fun ξ => ?_⟩
  have hc := leviChain n Real.exp φ x ξ hφ hexp
  have hw : ∀ j, wd n j (fun y => ((Real.exp (φ y) : ℝ) : ℂ)) x =
      ((Real.exp (φ x) : ℝ) : ℂ) * wd n j (fun y => (φ y : ℂ)) x := fun j => by
    rw [wd_ofReal_comp Real.differentiable_exp.differentiableAt hφ1, hd1]
  rw [hd1, hd2] at hc
  simp only [hc, hw, mul_assoc, ← Finset.mul_sum, add_re, re_ofReal_mul, normSq_mul, normSq_ofReal,
    ofReal_re]
  set e := Real.exp (φ x)
  have he : 0 < e := Real.exp_pos _
  have hl := hL ξ
  set N := Complex.normSq (∑ j, wd n j (fun y => (φ y : ℂ)) x * ξ j)
  set R := (leviV n (fun y => (φ y : ℂ)) x ξ).re
  have hN : 0 ≤ N := Complex.normSq_nonneg _
  constructor
  · positivity
  · nlinarith [mul_nonneg (mul_nonneg he.le he.le) hl]

/- English proof (translation)
Establish `hgR : ContDiffAt ℝ 2 g x` using `hg.restrict_scalars ℝ`. Establish `hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y` using `(hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)`. Establish `hgx : DifferentiableAt ℂ g x` using `hg.differentiableAt (by simp)`. Establish `hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y)`. Use function extensionality and compare the values at `y`.

Rewrite using `[mul_conj]`. Establish `h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x` using `hg.fderiv_right (by norm_num)`. Establish `hh : ∀ kk : Fin n, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n kk)) x` using `fun kk => (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)`. Establish `hE : ∀ kk : Fin n, wdb n kk (fun y => g y * conj (g y)) =ᶠ[𝓝 x] fun y => g y * conj (fderiv ℂ g y (bas n kk))`. Introduce `kk`.

Use `filter_upwards [hgd] with y hy`. Rewrite using `[wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)), wdb_of_differentiableAt hy, wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => g y * conj (g y))) x = wd n j g x * conj (wd n kk g x)`. Introduce `j kk`.

Rewrite using `[wd_congr (hE kk), wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n kk))) (hgx.restrictScalars ℝ) (differentiableAt_conj ((hh kk).restrictScalars ℝ)), wd_conj ((hh kk).restrictScalars ℝ), wdb_of_differentiableAt (hh kk)]`. Simplify using `[wd_of_differentiableAt hgx]`. Establish `hwd : ∀ j : Fin n, wd n j (fun y => g y * conj (g y)) x = wd n j g x * conj (g x)`. Introduce `j`. Rewrite using `[wd_mul (hgx.restrictScalars ℝ) (differentiableAt_conj (hgx.restrictScalars ℝ)), wd_conj (hgx.restrictScalars ℝ), wdb_of_differentiableAt hgx]`.

Simplify using the standard rewrite rules. Use `⟨Complex.normSq_nonneg _, fun ξ => ?_⟩` and prove the remaining obligations. Establish `hlevi : leviV n (fun y => g y * conj (g y)) x ξ = ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ)`. Rewrite using `[ofReal_normSq_sum_mul]`. Simplify using `only [leviV, hterm]`.

Rewrite using `[hf, hlevi, ofReal_re]`. Simplify using `only [hwd]`. Establish `: ∑ j, wd n j g x * conj (g x) * ξ j = conj (g x) * ∑ j, wd n j g x * ξ j`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[this, normSq_mul, normSq_conj]`.

Conclude with `⟨Complex.normSq_nonneg _, le_rfl⟩`.
-/
theorem logPshAt_normSq {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    LogPshAt n (fun y => Complex.normSq (g y)) x := by
  have hgR : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (by simp)
  have hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [mul_conj]

  have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
  have hh : ∀ kk : Fin n, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n kk)) x := fun kk =>
    (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hE : ∀ kk : Fin n, wdb n kk (fun y => g y * conj (g y)) =ᶠ[𝓝 x]
      fun y => g y * conj (fderiv ℂ g y (bas n kk)) := by
    intro kk
    filter_upwards [hgd] with y hy
    rw [wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)),
      wdb_of_differentiableAt hy,
      wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]
    ring
  have hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => g y * conj (g y))) x =
      wd n j g x * conj (wd n kk g x) := by
    intro j kk
    rw [wd_congr (hE kk), wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n kk)))
      (hgx.restrictScalars ℝ) (differentiableAt_conj ((hh kk).restrictScalars ℝ)),
      wd_conj ((hh kk).restrictScalars ℝ), wdb_of_differentiableAt (hh kk)]
    simp [wd_of_differentiableAt hgx]
  have hwd : ∀ j : Fin n, wd n j (fun y => g y * conj (g y)) x = wd n j g x * conj (g x) := by
    intro j
    rw [wd_mul (hgx.restrictScalars ℝ) (differentiableAt_conj (hgx.restrictScalars ℝ)),
      wd_conj (hgx.restrictScalars ℝ),
      wdb_of_differentiableAt hgx]
    simp
  refine ⟨Complex.normSq_nonneg _, fun ξ => ?_⟩
  have hlevi : leviV n (fun y => g y * conj (g y)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
    rw [ofReal_normSq_sum_mul]
    simp only [leviV, hterm]
  rw [hf, hlevi, ofReal_re]
  simp only [hwd]
  have : ∑ j, wd n j g x * conj (g x) * ξ j = conj (g x) * ∑ j, wd n j g x * ξ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, normSq_mul, normSq_conj]
  exact ⟨Complex.normSq_nonneg _, le_rfl⟩

/- English proof (translation)
The claim follows from `logPshAt_normSq contDiffAt_const`.
-/
theorem logPshAt_one (x : V n) : LogPshAt n (fun y => Complex.normSq ((fun _ : V n => (1 : ℂ)) y)) x :=
  logPshAt_normSq contDiffAt_const

/- English proof (translation)
Establish `hS : ContDiffAt ℝ 2 (fun y => ∑ i, u i y) x` using `ContDiffAt.sum fun i _ => hu i`. Establish `hlog : ContDiffAt ℝ 2 Real.log (∑ i, u i x)` using `Real.contDiffAt_log.2 hpos.ne'`. Establish `hc` using `leviChain n Real.log (fun y => ∑ i, u i y) x ξ hS hlog`. Establish `hd1 : deriv Real.log (∑ i, u i x) = (∑ i, u i x)⁻¹` using `by rw [Real.deriv_log']`. Establish `hd2 : deriv (deriv Real.log) (∑ i, u i x) = -((∑ i, u i x) ^ 2)⁻¹`.

Rewrite using `[Real.deriv_log']`. Conclude with `deriv_inv`. Rewrite using `[hc, hd1, hd2, leviV_ofReal_sum hu]`. Establish `hw : ∀ j, wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x` using `fun j => wd_ofReal_sum fun i => (hu i).differentiableAt (by simp)`. Simplify using `only [hw, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [add_re, re_ofReal_mul, ofReal_re, re_sum]`. Use `set S := ∑ i, u i x`. Establish `key` using `normSq_sum_le_of_le (fun i => ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j) (fun i => u i x) (fun i => (leviV n (fun y => (u i y : ℂ)) x ξ).re) (fun i => (hl i).1) (fun i => ((hl i).2 ξ).1) (fun i => ((hl i).2 ξ).2)`. Use `set N := Complex.normSq (∑ i, ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j)`.

Use `set T := ∑ i, (leviV n (fun y => (u i y : ℂ)) x ξ).re`. Establish `hid : S⁻¹ * T + -(S ^ 2)⁻¹ * N = (S * T - N) / S ^ 2` using `by field_simp; ring`. Rewrite using `[hid]`. Conclude with `div_nonneg (by linarith) (by positivity)`.
-/
theorem leviV_log_sum_nonneg {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (hl : ∀ i, LogPshAt n (u i) x) (hpos : 0 < ∑ i, u i x)
    (ξ : Fin n → ℂ) : 0 ≤ (leviV n (fun y => ((Real.log (∑ i, u i y) : ℝ) : ℂ)) x ξ).re := by
  have hS : ContDiffAt ℝ 2 (fun y => ∑ i, u i y) x := ContDiffAt.sum fun i _ => hu i
  have hlog : ContDiffAt ℝ 2 Real.log (∑ i, u i x) := Real.contDiffAt_log.2 hpos.ne'
  have hc := leviChain n Real.log (fun y => ∑ i, u i y) x ξ hS hlog
  have hd1 : deriv Real.log (∑ i, u i x) = (∑ i, u i x)⁻¹ := by rw [Real.deriv_log']
  have hd2 : deriv (deriv Real.log) (∑ i, u i x) = -((∑ i, u i x) ^ 2)⁻¹ := by
    rw [Real.deriv_log']; exact deriv_inv
  rw [hc, hd1, hd2, leviV_ofReal_sum hu]
  have hw : ∀ j, wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x :=
    fun j => wd_ofReal_sum fun i => (hu i).differentiableAt (by simp)
  simp only [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [add_re, re_ofReal_mul, ofReal_re, re_sum]
  set S := ∑ i, u i x
  have key := normSq_sum_le_of_le (fun i => ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j) (fun i => u i x)
    (fun i => (leviV n (fun y => (u i y : ℂ)) x ξ).re) (fun i => (hl i).1)
    (fun i => ((hl i).2 ξ).1) (fun i => ((hl i).2 ξ).2)
  set N := Complex.normSq (∑ i, ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j)
  set T := ∑ i, (leviV n (fun y => (u i y : ℂ)) x ξ).re
  have hid : S⁻¹ * T + -(S ^ 2)⁻¹ * N = (S * T - N) / S ^ 2 := by field_simp; ring
  rw [hid]
  exact div_nonneg (by linarith) (by positivity)

/- English proof (translation)
Introduce `n m U u hU hu hpos x hx ξ`. Establish `hxU : U ∈ 𝓝 x` using `hU.mem_nhds hx`. Establish `hgood : ∀ i, ContDiffAt ℝ 2 (u i) x ∧ LogPshAt n (u i) x`. Introduce `i`. Break down `hu i with ⟨φ, hφ, hL, he⟩ | ⟨g, hg, he⟩` into its components or cases.

Establish `hev : (fun y => Real.exp (φ y)) =ᶠ[𝓝 x] u i` using `Filter.mem_of_superset hxU fun y hy => (he y hy).symm`. Establish `hφx : ContDiffAt ℝ 2 φ x` using `hφ.contDiffAt hxU`. Conclude with `⟨(Real.contDiff_exp.contDiffAt.comp x hφx).congr_of_eventuallyEq hev.symm, (logPshAt_exp hφx (hL x hx)).congr hev⟩`. Establish `hev : (fun y => Complex.normSq (g y)) =ᶠ[𝓝 x] u i` using `Filter.mem_of_superset hxU fun y hy => (he y hy).symm`. Establish `hgx : ContDiffAt ℂ 2 g x` using `hg.contDiffAt hxU`.

Establish `hgR : ContDiffAt ℝ 2 g x` using `hgx.restrict_scalars ℝ`. Establish `hns : ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x`. Establish `h2 : ContDiffAt ℝ 2 (fun y => (g y * conj (g y)).re) x` using `reCLM.contDiff.contDiffAt.comp x (hgR.mul (conjCLE.contDiff.contDiffAt.comp x hgR))`. Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `[mul_conj]`.

Conclude with `⟨hns.congr_of_eventuallyEq hev.symm, (logPshAt_normSq hgx).congr hev⟩`. Conclude with `leviV_log_sum_nonneg (fun i => (hgood i).1) (fun i => (hgood i).2) (hpos x hx) ξ`.
-/
theorem lseV : LSEVStatement := by
  intro n m U u hU hu hpos x hx ξ
  have hxU : U ∈ 𝓝 x := hU.mem_nhds hx
  have hgood : ∀ i, ContDiffAt ℝ 2 (u i) x ∧ LogPshAt n (u i) x := by
    intro i
    rcases hu i with ⟨φ, hφ, hL, he⟩ | ⟨g, hg, he⟩
    · have hev : (fun y => Real.exp (φ y)) =ᶠ[𝓝 x] u i :=
        Filter.mem_of_superset hxU fun y hy => (he y hy).symm
      have hφx : ContDiffAt ℝ 2 φ x := hφ.contDiffAt hxU
      exact ⟨(Real.contDiff_exp.contDiffAt.comp x hφx).congr_of_eventuallyEq hev.symm,
        (logPshAt_exp hφx (hL x hx)).congr hev⟩
    · have hev : (fun y => Complex.normSq (g y)) =ᶠ[𝓝 x] u i :=
        Filter.mem_of_superset hxU fun y hy => (he y hy).symm
      have hgx : ContDiffAt ℂ 2 g x := hg.contDiffAt hxU
      have hgR : ContDiffAt ℝ 2 g x := hgx.restrict_scalars ℝ
      have hns : ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
        have h2 : ContDiffAt ℝ 2 (fun y => (g y * conj (g y)).re) x :=
          reCLM.contDiff.contDiffAt.comp x (hgR.mul (conjCLE.contDiff.contDiffAt.comp x hgR))
        refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp [mul_conj]
      exact ⟨hns.congr_of_eventuallyEq hev.symm, (logPshAt_normSq hgx).congr hev⟩
  exact leviV_log_sum_nonneg (fun i => (hgood i).1) (fun i => (hgood i).2) (hpos x hx) ξ

/- English proof (translation)
Assemble the required witnesses or components as `⟨Set.univ, fun _ _ => 1, isOpen_univ, Set.univ_nonempty, fun _ => ⟨fun _ => 0, contDiffOn_const, leviNonnegOn_const 0 _, fun _ _ => by simp⟩, fun _ _ => by simp⟩`.
-/
theorem lseV_hyp_inhabited (n : ℕ) :
    ∃ (U : Set (V n)) (u : Fin 1 → V n → ℝ), IsOpen U ∧ U.Nonempty ∧
      (∀ i, ∃ φ : V n → ℝ, ContDiffOn ℝ 2 φ U ∧ LeviNonnegOn n φ U ∧
        ∀ y ∈ U, u i y = Real.exp (φ y)) ∧ (∀ y ∈ U, 0 < ∑ i, u i y) :=
  ⟨Set.univ, fun _ _ => 1, isOpen_univ, Set.univ_nonempty,
    fun _ => ⟨fun _ => 0, contDiffOn_const, leviNonnegOn_const 0 _, fun _ _ => by simp⟩,
    fun _ _ => by simp⟩

end ReciprocityTheory.L2DbarEstimates
