import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRapidFourierSeriesOfIntPeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ContDiffAndFderivTsumFourierOfRapid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FourierCoeffEqZeroOfTsumEqZeroFin
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory
namespace TorusElliptic

def Rapid {n : ℕ} (c : (Fin n → ℤ) → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C

noncomputable def ch {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ℂ :=
  cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))

/- English proof (translation)
Establish `: (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = ((2 * π * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * I` using `by push_cast; ring`. Rewrite using `[ch, this, Complex.norm_exp_ofReal_mul_I]`.
-/
lemma norm_ch {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ‖ch ν x‖ = 1 := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = ((2 * π * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [ch, this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Establish `: (2 * π * I * ∑ k, (ν k : ℂ) * (((x + fun k => (μ k : ℝ)) k : ℝ) : ℂ)) = (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) + ((∑ k, ν k * μ k : ℤ) : ℂ) * (2 * π * I)`. Simplify using `only [Pi.add_apply]`. Use `push_cast`. Simplify using `only [mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[ch, this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ch]`.
-/
lemma ch_periodic {n : ℕ} (ν μ : Fin n → ℤ) (x : Fin n → ℝ) :
    ch ν (x + fun k => (μ k : ℝ)) = ch ν x := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (((x + fun k => (μ k : ℝ)) k : ℝ) : ℂ))
      = (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) + ((∑ k, ν k * μ k : ℤ) : ℂ) * (2 * π * I) := by
    simp only [Pi.add_apply]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [ch, this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ch]

/- English proof (translation)
Establish `h : Summable (fun j : ℕ => 1 / (1 + (j : ℝ)) ^ 2)`. Use `(summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))` as an intermediate fact. Use `this.congr fun j => ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[add_comm]`.

Use `Summable.of_nat_of_neg ?_ ?_` and prove the remaining obligations. Simplify using `using h`. Simplify using `using h`.
-/
lemma summable_int_weight : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have h : Summable (fun j : ℕ => 1 / (1 + (j : ℝ)) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine this.congr fun j => ?_
    push_cast; rw [add_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

/- English proof (translation)
Use `summable_of_sum_le (c := ∏ _k : Fin n, ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2) (fun ν => by positivity) fun s => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) (fun _ _ _ => by positivity)` and prove the remaining obligations. Conclude with `Fintype.mem_piFinset.2 fun k => Finset.mem_image_of_mem _ hν`. Use `_ = ∏ k, ∑ j ∈ (s.image (fun ν => ν k) : Finset ℤ), 1 / (1 + |(j : ℝ)|) ^ 2 := by`.

Conclude with `(Finset.prod_univ_sum (fun k => (s.image (fun ν => ν k) : Finset ℤ)) (fun _ j => 1 / (1 + |(j : ℝ)|) ^ 2)).symm`. Use `_ ≤ _ := by`. Use `Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_` and prove the remaining obligations. Conclude with `summable_int_weight.sum_le_tsum _ (fun _ _ => by positivity)`.
-/
lemma summable_pi_weight (n : ℕ) :
    Summable (fun ν : Fin n → ℤ => ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2) := by
  classical
  refine summable_of_sum_le (c := ∏ _k : Fin n, ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2)
    (fun ν => by positivity) fun s => ?_
  calc ∑ ν ∈ s, ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2
      ≤ ∑ ν ∈ Fintype.piFinset (fun k => (s.image (fun ν => ν k) : Finset ℤ)),
          ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) (fun _ _ _ => by positivity)
        exact Fintype.mem_piFinset.2 fun k => Finset.mem_image_of_mem _ hν
    _ = ∏ k, ∑ j ∈ (s.image (fun ν => ν k) : Finset ℤ), 1 / (1 + |(j : ℝ)|) ^ 2 := by
        exact (Finset.prod_univ_sum (fun k => (s.image (fun ν => ν k) : Finset ℤ))
          (fun _ j => 1 / (1 + |(j : ℝ)|) ^ 2)).symm
    _ ≤ _ := by
        refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
        exact summable_int_weight.sum_le_tsum _ (fun _ _ => by positivity)

/- English proof (translation)
Take `⟨C, hC⟩` from `h (2 * n)`. Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ν => ?_) ((summable_pi_weight n).mul_left C)` and prove the remaining obligations. Establish `h1 : ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_` and prove the remaining obligations.

Use `gcongr`. Conclude with `Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)`. Use `_ = _ := by simp [pow_mul]`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div, le_div_iff₀ (by positivity)]`. Conclude with `le_trans (by gcongr) (hC ν)`.
-/
lemma Rapid.summable {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) :
    Summable (fun ν => ‖c ν‖) := by
  obtain ⟨C, hC⟩ := h (2 * n)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ν => ?_)
    ((summable_pi_weight n).mul_left C)
  have h1 : ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by
    calc ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ ∏ _k : Fin n, (1 + ∑ k, |(ν k : ℝ)|) ^ 2 := by
          refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
          gcongr
          exact Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ k)
      _ = _ := by simp [pow_mul]
  rw [Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div, le_div_iff₀ (by positivity)]
  exact le_trans (by gcongr) (hC ν)

/- English proof (translation)
Introduce `N`. Take `⟨C, hC⟩` from `h (N + 1)`. Use `⟨‖z‖ * C, fun ν => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖(ν j : ℂ)‖ ≤ 1 + ∑ k, |(ν k : ℝ)|`. Use `Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)` as an intermediate fact.

Rewrite using `[Complex.norm_intCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [norm_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * (1 + ∑ k, |(ν k : ℝ)|))) := by gcongr`. Use `_ ≤ ‖z‖ * C := by rw [← pow_succ]; gcongr; exact hC ν`.
-/
lemma Rapid.mul {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (z : ℂ) (j : Fin n) :
    Rapid (fun ν => z * (ν j : ℂ) * c ν) := by
  intro N
  obtain ⟨C, hC⟩ := h (N + 1)
  refine ⟨‖z‖ * C, fun ν => ?_⟩
  have h1 : ‖(ν j : ℂ)‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := by
    have := Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
    rw [Complex.norm_intCast]
    linarith
  calc ‖z * (ν j : ℂ) * c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N
      = ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * ‖(ν j : ℂ)‖)) := by
        simp only [norm_mul]; ring
    _ ≤ ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * (1 + ∑ k, |(ν k : ℝ)|))) := by gcongr
    _ ≤ ‖z‖ * C := by rw [← pow_succ]; gcongr; exact hC ν

/- English proof (translation)
Use `Summable.of_norm ?_` and prove the remaining obligations. Simplify `h` using `[norm_ch]`.
-/
lemma summable_ch {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Summable (fun ν => ‖c ν‖))
    (x : Fin n → ℝ) : Summable (fun ν => c ν * ch ν x) := by
  refine Summable.of_norm ?_
  simpa [norm_ch] using h

/- English proof (translation)
Establish `: Summable (fun ν : Fin n → ℤ => ∑ k, (q k * (2 * π * I)) * (ν k : ℂ) * c ν)` using `summable_sum fun k _ => (h.mul _ k).summable.of_norm`. Use `(summable_norm_iff.2 this).congr fun ν => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
lemma summable_symb {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) :
    Summable (fun ν : Fin n → ℤ => ‖2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν‖) := by
  have : Summable (fun ν : Fin n → ℤ => ∑ k, (q k * (2 * π * I)) * (ν k : ℂ) * c ν) :=
    summable_sum fun k _ => (h.mul _ k).summable.of_norm
  refine (summable_norm_iff.2 this).congr fun ν => ?_
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Establish `h1 : ∀ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1) = ∑' ν : Fin n → ℤ, (q k * (2 * π * I)) * (ν k : ℂ) * c ν * ch ν x`. Introduce `k`. Use `(GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n c h).2 x k` as an intermediate fact. Unfold `ch`. Rewrite using `[this, ← tsum_mul_left]`.

Conclude with `tsum_congr fun ν => by ring`. Repeatedly rewrite using `[h1]`. Rewrite using `[← Summable.tsum_finsetSum fun k _ => summable_ch (h.mul _ k).summable x]`. Use `tsum_congr fun ν => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
lemma sum_fderiv {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) (x : Fin n → ℝ) :
    ∑ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν, 2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν * ch ν x := by
  have h1 : ∀ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν : Fin n → ℤ, (q k * (2 * π * I)) * (ν k : ℂ) * c ν * ch ν x := by
    intro k
    have := (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n c h).2 x k
    unfold ch
    rw [this, ← tsum_mul_left]
    exact tsum_congr fun ν => by ring
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum fun k _ => summable_ch (h.mul _ k).summable x]
  refine tsum_congr fun ν => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Set `L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ)` to `{ toFun := fun ξ a => ∑ k, p a k * (ξ k : ℂ) map_add' := fun ξ η => by`. Use function extensionality and compare the values at `a`. Simplify using `[mul_add, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun r ξ => by`. Use function extensionality and compare the values at `a`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun k _ => by ring }`. Establish `hL : LinearMap.ker L = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `ξ hξ`. Conclude with `hp ξ fun a => congrFun hξ a`. Take `⟨K, hK, hA⟩` from `L.exists_antilipschitzWith hL`. Establish `hK' : (0 : ℝ) < K` using `hK`. Use `⟨1 / K, by positivity, fun ν hν => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h1 : ‖L (fun k => (ν k : ℝ))‖ < 1 / K`. Rewrite using `[pi_norm_lt_iff (by positivity)]`. Introduce `a`.

Simplify `hcon a` using `[L]`. Establish `h2` using `hA.le_mul_dist (fun k => (ν k : ℝ)) 0`. Rewrite `h2` using `[map_zero, dist_zero_right, dist_zero_right]`. Take `⟨k, hk⟩` from `Function.ne_iff.1 hν`. Establish `h3 : (1 : ℝ) ≤ ‖(fun k => (ν k : ℝ))‖`.

Use `le_trans ?_ (norm_le_pi_norm (fun k => (ν k : ℝ)) k)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `Int.one_le_abs hk` after adjusting the coercions. Rewrite `h1` using `[lt_div_iff₀ hK']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma symbol_lower {n m : ℕ} (p : Fin m → Fin n → ℂ)
    (hp : ∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Fin n → ℤ, ν ≠ 0 → ∃ a, ε ≤ ‖∑ k, p a k * (ν k : ℂ)‖ := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    { toFun := fun ξ a => ∑ k, p a k * (ξ k : ℂ)
      map_add' := fun ξ η => by
        funext a; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r ξ => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun k _ => by ring }
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ξ hξ
    exact hp ξ fun a => congrFun hξ a
  obtain ⟨K, hK, hA⟩ := L.exists_antilipschitzWith hL
  have hK' : (0 : ℝ) < K := hK
  refine ⟨1 / K, by positivity, fun ν hν => ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : ‖L (fun k => (ν k : ℝ))‖ < 1 / K := by
    rw [pi_norm_lt_iff (by positivity)]
    intro a
    simpa [L] using hcon a
  have h2 := hA.le_mul_dist (fun k => (ν k : ℝ)) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h2
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hν
  have h3 : (1 : ℝ) ≤ ‖(fun k => (ν k : ℝ))‖ := by
    refine le_trans ?_ (norm_le_pi_norm (fun k => (ν k : ℝ)) k)
    rw [Real.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hk
  rw [lt_div_iff₀ hK'] at h1
  linarith

end TorusElliptic

open TorusElliptic in

/- English proof (translation)
Introduce `n m p hp w hw hcomp`. Use `choose c hc hwc using fun a => GlobalTheory.exists_rapid_fourierSeries_of_int_periodic n (w a) (hw a).1 (hw a).2`. Establish `hc' : ∀ a, Rapid (c a)` using `hc`. Establish `hwf : ∀ a, w a = fun x => ∑' ν, c a ν * ch ν x` using `fun a => funext (hwc a)`. Establish `h2pi : (2 * π * I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`.

Establish `hsym : ∀ a b ν, (∑ k, p a k * (ν k : ℂ)) * c b ν = (∑ k, p b k * (ν k : ℂ)) * c a ν`. Introduce `a b ν`. Establish `hs1` using `summable_symb (hc' b) (p a)`. Establish `hs2` using `summable_symb (hc' a) (p b)`. Use `GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin n (fun ν => 2 * π * I * (∑ k, p a k * (ν k : ℂ)) * c b ν - 2 * π * I * (∑ k, p b k * (ν k : ℂ)) * c a ν) (summable_norm_iff.2 (hs1.of_norm.sub hs2.of_norm)) (fun x => by` as an intermediate fact.

Establish `h` using `hcomp a b x`. Rewrite `h` using `[hwf a, hwf b, sum_fderiv (hc' b), sum_fderiv (hc' a)]`. Establish `h'` using `(summable_ch hs1 x).tsum_sub (summable_ch hs2 x)`. Rewrite `h'` using `[h, sub_self]`. Rewrite using `[← h']`.

Conclude with `tsum_congr fun ν => by unfold ch; ring) ν`. Apply `mul_left_cancel₀ h2pi` to reduce the goal to its premises. Take the linear combination `this`. Take `⟨ε, hε, hlow⟩` from `symbol_lower p hp`. Use `choose α hα using hlow`.

Set `d : (Fin n → ℤ) → ℂ` to `fun ν => if h : ν = 0 then 0 else c (α ν h) ν / (2 * π * I * ∑ k, p (α ν h) k * (ν k : ℂ))`. Establish `hd : Rapid d`. Introduce `N`. Use `choose C hC using fun a => hc' a N`. Establish `hC0 : ∀ a, 0 ≤ C a` using `fun a => le_trans (by positivity) (hC a 0)`.

Use `⟨(∑ a, C a) / (‖(2 * π * I : ℂ)‖ * ε), fun ν => ?_⟩` and prove the remaining obligations. Establish `hn : 0 < ‖(2 * π * I : ℂ)‖` using `norm_pos_iff.2 h2pi`. Establish `hS : 0 ≤ ∑ a, C a` using `Finset.sum_nonneg fun a _ => hC0 a`. Distinguish the cases in `h : ν = 0`. Simplify using `only [d, dif_pos h, norm_zero, zero_mul]`.

Check the signs of the components of the expression. Simplify using `only [d, dif_neg h]`. Rewrite using `[norm_div, norm_mul (2 * π * I : ℂ), div_mul_eq_mul_div]`. Establish `h1` using `Finset.single_le_sum (f := C) (fun a _ => hC0 a) (Finset.mem_univ (α ν h))`. Establish `h2` using `hα ν h`.

Establish `h3` using `hC (α ν h) ν`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun a => c a 0, fun x => ∑' ν, d ν * ch ν x, (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n d hd).1, ?_, ?_⟩` and prove the remaining obligations. Introduce `μ x`.

Simplify using `only [ch_periodic]`. Introduce `a x`. Rewrite using `[sum_fderiv hd, hwf a]`. Establish `hs` using `summable_ch (hc' a).summable x`. Establish `h0` using `hs.tsum_eq_add_tsum_ite 0`.

Establish `hch : ch (0 : Fin n → ℤ) x = 1` using `by simp [ch]`. Rewrite `h0` using `[hch, mul_one]`. Simplify using `only []`. Rewrite using `[h0, add_sub_cancel_left]`. Use `tsum_congr fun ν => ?_` and prove the remaining obligations.

Distinguish the cases in `h : ν = 0`. Simplify using `only [d, dif_pos h, if_pos h, mul_zero, zero_mul]`. Simplify using `only [d, dif_neg h, if_neg h]`. Establish `h2 : (∑ k, p (α ν h) k * (ν k : ℂ)) ≠ 0`. Introduce `h0`.

Use `hα ν h` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `hsym a (α ν h) ν`. Use `congr 1`.

Rewrite using `[mul_div_assoc', div_eq_iff (mul_ne_zero h2pi h2)]`. Take the linear combination `(2 * π * I) * h3`.
-/
theorem torus_elliptic_system_solvable : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  classical
  intro n m p hp w hw hcomp
  choose c hc hwc using fun a => GlobalTheory.exists_rapid_fourierSeries_of_int_periodic n (w a) (hw a).1 (hw a).2
  have hc' : ∀ a, Rapid (c a) := hc
  have hwf : ∀ a, w a = fun x => ∑' ν, c a ν * ch ν x := fun a => funext (hwc a)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hsym : ∀ a b ν, (∑ k, p a k * (ν k : ℂ)) * c b ν = (∑ k, p b k * (ν k : ℂ)) * c a ν := by
    intro a b ν
    have hs1 := summable_symb (hc' b) (p a)
    have hs2 := summable_symb (hc' a) (p b)
    have := GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin n (fun ν => 2 * π * I * (∑ k, p a k * (ν k : ℂ)) * c b ν
      - 2 * π * I * (∑ k, p b k * (ν k : ℂ)) * c a ν)
      (summable_norm_iff.2 (hs1.of_norm.sub hs2.of_norm)) (fun x => by
        have h := hcomp a b x
        rw [hwf a, hwf b, sum_fderiv (hc' b), sum_fderiv (hc' a)] at h
        have h' := (summable_ch hs1 x).tsum_sub (summable_ch hs2 x)
        rw [h, sub_self] at h'
        rw [← h']
        exact tsum_congr fun ν => by unfold ch; ring) ν
    apply mul_left_cancel₀ h2pi
    linear_combination this
  obtain ⟨ε, hε, hlow⟩ := symbol_lower p hp
  choose α hα using hlow
  let d : (Fin n → ℤ) → ℂ := fun ν =>
    if h : ν = 0 then 0 else c (α ν h) ν / (2 * π * I * ∑ k, p (α ν h) k * (ν k : ℂ))
  have hd : Rapid d := by
    intro N
    choose C hC using fun a => hc' a N
    have hC0 : ∀ a, 0 ≤ C a := fun a => le_trans (by positivity) (hC a 0)
    refine ⟨(∑ a, C a) / (‖(2 * π * I : ℂ)‖ * ε), fun ν => ?_⟩
    have hn : 0 < ‖(2 * π * I : ℂ)‖ := norm_pos_iff.2 h2pi
    have hS : 0 ≤ ∑ a, C a := Finset.sum_nonneg fun a _ => hC0 a
    by_cases h : ν = 0
    · simp only [d, dif_pos h, norm_zero, zero_mul]
      positivity
    · simp only [d, dif_neg h]
      rw [norm_div, norm_mul (2 * π * I : ℂ), div_mul_eq_mul_div]
      have h1 := Finset.single_le_sum (f := C) (fun a _ => hC0 a) (Finset.mem_univ (α ν h))
      have h2 := hα ν h
      have h3 := hC (α ν h) ν
      gcongr
      linarith
  refine ⟨fun a => c a 0, fun x => ∑' ν, d ν * ch ν x, (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n d hd).1, ?_, ?_⟩
  · intro μ x
    simp only [ch_periodic]
  · intro a x
    rw [sum_fderiv hd, hwf a]
    have hs := summable_ch (hc' a).summable x
    have h0 := hs.tsum_eq_add_tsum_ite 0
    have hch : ch (0 : Fin n → ℤ) x = 1 := by simp [ch]
    rw [hch, mul_one] at h0
    simp only []
    rw [h0, add_sub_cancel_left]
    refine tsum_congr fun ν => ?_
    by_cases h : ν = 0
    · simp only [d, dif_pos h, if_pos h, mul_zero, zero_mul]
    · simp only [d, dif_neg h, if_neg h]
      have h2 : (∑ k, p (α ν h) k * (ν k : ℂ)) ≠ 0 := by
        intro h0
        have := hα ν h
        rw [h0, norm_zero] at this
        linarith
      have h3 := hsym a (α ν h) ν
      congr 1
      rw [mul_div_assoc', div_eq_iff (mul_ne_zero h2pi h2)]
      linear_combination (2 * π * I) * h3

end GlobalTheory
