import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
open ValuativeRel GlobalTheory.SplitWeil Matrix

noncomputable section
namespace GlobalTheory.CharDualMat

open ValuativeRel Matrix in
/- English proof (translation)
Establish `h1 : w.re ^ 2 + w.im ^ 2 = 1`. Use `Complex.sq_norm w` as an intermediate fact. Rewrite `this` using `[hw, Complex.normSq_apply]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (w.re - 1) ^ 2 + w.im ^ 2 < 1`.

Use `Complex.sq_norm (w - 1)` as an intermediate fact. Rewrite `this` using `[Complex.normSq_apply]`. Simplify using `only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this`. Establish `h0 : ‖w - 1‖ ^ 2 < 1`. Use `norm_nonneg (w - 1)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma half_lt_re_of_norm_eq_one_of_norm_sub_one_lt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1) :
    1 / 2 < w.re := by
  have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  have h2 : (w.re - 1) ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm (w - 1)
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this
    have h0 : ‖w - 1‖ ^ 2 < 1 := by
      have := norm_nonneg (w - 1)
      nlinarith
    nlinarith
  nlinarith

open ValuativeRel Matrix in

/- English proof (translation)
Establish `hnorm : ∀ m : ℕ, ‖(z : ℂ) ^ (2 ^ m)‖ = 1` using `fun m => by`. Rewrite using `[norm_pow, Circle.norm_coe, one_pow]`. Establish `hre : ∀ m : ℕ, 1 / 2 < ((z : ℂ) ^ (2 ^ m)).re` using `fun m => half_lt_re_of_norm_eq_one_of_norm_sub_one_lt (hnorm m) (h _)`. Establish `hsq : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ m)).re ^ 2 + ((z : ℂ) ^ (2 ^ m)).im ^ 2 = 1` using `fun m => by`. Use `Complex.sq_norm ((z : ℂ) ^ (2 ^ m))` as an intermediate fact.

Rewrite `this` using `[hnorm m, Complex.normSq_apply]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hstep : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ (m + 1))).re = ((z : ℂ) ^ (2 ^ m)).re ^ 2 - ((z : ℂ) ^ (2 ^ m)).im ^ 2` using `fun m => by`. Rewrite using `[pow_succ, pow_mul, sq, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hgrow : ∀ m : ℕ, 3 ^ m * (1 - (z : ℂ).re) ≤ 1 - ((z : ℂ) ^ (2 ^ m)).re`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`.

Rewrite using `[hstep m, pow_succ]`. Establish `hr` using `hre m`. Establish `hs` using `hsq m`. Establish `hle : ((z : ℂ) ^ (2 ^ m)).re ≤ 1` using `by nlinarith [sq_nonneg ((z : ℂ) ^ (2 ^ m)).im]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hd0 : (z : ℂ).re = 1`. Establish `hle : (z : ℂ).re ≤ 1`. Use `hsq 0` as an intermediate fact. Simplify using `only [pow_zero, pow_one] at this`. Use polynomial arithmetic with `[sq_nonneg (z : ℂ).im]`.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < 1 - (z : ℂ).re`. Break down `lt_or_eq_of_le hle with hlt | heq` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd heq hne`.

Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 3)`. Establish `h1` using `hgrow n`. Establish `h2` using `hre n`. Rewrite `hn` using `[div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `him : (z : ℂ).im = 0`. Use `hsq 0` as an intermediate fact. Simplify using `only [pow_zero, pow_one, hd0] at this`. Use polynomial arithmetic with `[sq_nonneg (z : ℂ).im]`. Apply `Circle.ext_iff.mpr` to reduce the goal to its premises.

Apply the tactic sequence `apply Complex.ext <;> simp [hd0, him]`.
-/
theorem _root_.GlobalTheory.CharDualMat.circle_eq_one_of_pow_near (z : Circle) (h : ∀ n : ℕ, ‖(z : ℂ) ^ n - 1‖ < 1) :
    z = 1 := by
  have hnorm : ∀ m : ℕ, ‖(z : ℂ) ^ (2 ^ m)‖ = 1 := fun m => by
    rw [norm_pow, Circle.norm_coe, one_pow]
  have hre : ∀ m : ℕ, 1 / 2 < ((z : ℂ) ^ (2 ^ m)).re := fun m =>
    half_lt_re_of_norm_eq_one_of_norm_sub_one_lt (hnorm m) (h _)
  have hsq : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ m)).re ^ 2 + ((z : ℂ) ^ (2 ^ m)).im ^ 2 = 1 := fun m => by
    have := Complex.sq_norm ((z : ℂ) ^ (2 ^ m))
    rw [hnorm m, Complex.normSq_apply] at this
    nlinarith
  have hstep : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ (m + 1))).re =
      ((z : ℂ) ^ (2 ^ m)).re ^ 2 - ((z : ℂ) ^ (2 ^ m)).im ^ 2 := fun m => by
    rw [pow_succ, pow_mul, sq, Complex.mul_re]
    ring
  have hgrow : ∀ m : ℕ, 3 ^ m * (1 - (z : ℂ).re) ≤ 1 - ((z : ℂ) ^ (2 ^ m)).re := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hstep m, pow_succ]
      have hr := hre m
      have hs := hsq m
      have hle : ((z : ℂ) ^ (2 ^ m)).re ≤ 1 := by nlinarith [sq_nonneg ((z : ℂ) ^ (2 ^ m)).im]
      nlinarith
  have hd0 : (z : ℂ).re = 1 := by
    have hle : (z : ℂ).re ≤ 1 := by
      have := hsq 0
      simp only [pow_zero, pow_one] at this
      nlinarith [sq_nonneg (z : ℂ).im]
    by_contra hne
    have hpos : 0 < 1 - (z : ℂ).re := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · linarith
      · exact absurd heq hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := hgrow n
    have h2 := hre n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have him : (z : ℂ).im = 0 := by
    have := hsq 0
    simp only [pow_zero, pow_one, hd0] at this
    nlinarith [sq_nonneg (z : ℂ).im]
  apply Circle.ext_iff.mpr
  apply Complex.ext <;> simp [hd0, him]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[succ_nsmul]`. Conclude with `((valuation k).map_add _ _).trans (max_le ih le_rfl)`.
-/
theorem _root_.GlobalTheory.CharDualMat.valuation_nsmul_le (t : k) (n : ℕ) : valuation k (n • t) ≤ valuation k t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact ((valuation k).map_add _ _).trans (max_le ih le_rfl)

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `hopen : IsOpen (ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1})` using `(isOpen_lt (by fun_prop) continuous_const).preimage hψ`. Establish `hzero : (0 : k) ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1}`. Simplify using `[AddChar.map_zero_eq_one]`. Take `⟨γ, hγ, hsub⟩` from `(IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 (hopen.mem_nhds hzero)`. Use `⟨γ, hγ, fun t ht => ?_⟩` and prove the remaining obligations.

Apply `_root_.GlobalTheory.CharDualMat.circle_eq_one_of_pow_near` to reduce the goal to its premises. Introduce `n`. Establish `hmem : n • t ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1}` using `hsub (lt_of_le_of_lt (_root_.GlobalTheory.CharDualMat.valuation_nsmul_le t n) ht)`. Rewrite `hmem` using `[Set.mem_preimage, AddChar.map_nsmul_eq_pow]`. Simplify using `using hmem`.
-/
theorem _root_.GlobalTheory.CharDualMat.exists_ball_trivial (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ t = 1 := by
  have hopen : IsOpen (ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1}) :=
    (isOpen_lt (by fun_prop) continuous_const).preimage hψ
  have hzero : (0 : k) ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1} := by
    simp [AddChar.map_zero_eq_one]
  obtain ⟨γ, hγ, hsub⟩ :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 (hopen.mem_nhds hzero)
  refine ⟨γ, hγ, fun t ht => ?_⟩
  apply _root_.GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
  intro n
  have hmem : n • t ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1} :=
    hsub (lt_of_le_of_lt (_root_.GlobalTheory.CharDualMat.valuation_nsmul_le t n) ht)
  rw [Set.mem_preimage, AddChar.map_nsmul_eq_pow] at hmem
  simpa using hmem

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Establish `hva : 1 < valuation k a`. Rewrite `ha` using `[Valuation.mem_integer_iff]`. Conclude with `not_le.1 ha`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hva`. Take `⟨γ, hγ, hball⟩` from `_root_.GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ`. Establish `hmul : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) → ∀ u : k, u ∈ 𝒪[k] → ψ (s * a * u) = 1`. Introduce `s hs u hu`.

Use `h (s * u) (fun u' hu' => by rw [mul_assoc]; exact hs _ (mul_mem hu hu'))` as an intermediate fact. Rewrite using `[mul_right_comm]`. Conclude with `this`. Establish `hpow : ∀ n : ℕ, ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) → ∀ u : k, u ∈ 𝒪[k] → ψ (s * a ^ n * u) = 1`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro s hs`. Simplify using `using hs`. Consider the case `succ n ih => intro s hs`. Rewrite using `[pow_succ, ← mul_assoc]`.

Conclude with `hmul _ (ih s hs)`. Apply `hne` to reduce the goal to its premises. Use extensionality with `t`. Take `⟨n, hn⟩` from `MulArchimedean.arch (valuation k t * γ⁻¹) hva`. Establish `hlt : valuation k t * γ⁻¹ < valuation k a ^ (n + 1)` using `lt_of_le_of_lt hn (pow_lt_pow_right₀ hva n.lt_succ_self)`.

Establish `hapos : valuation k a ^ (n + 1) ≠ 0` using `pow_ne_zero _ (by simpa using ha0)`. Establish `hlt' : valuation k t < γ * valuation k a ^ (n + 1)`. Combine the equalities or inequalities in the displayed calculation. Establish `hs : ∀ u : k, u ∈ 𝒪[k] → ψ (t * (a ^ (n + 1))⁻¹ * u) = 1`. Introduce `u hu`.

Apply `hball` to reduce the goal to its premises. Rewrite `hu` using `[Valuation.mem_integer_iff]`. Rewrite using `[map_mul, map_mul, map_inv₀, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `hpow (n + 1) _ hs 1 (one_mem _)` as an intermediate fact.

Rewrite `this` using `[mul_one, inv_mul_cancel_right₀ (pow_ne_zero _ ha0)]`. Rewrite using `[this, AddChar.one_apply]`.
-/
theorem _root_.GlobalTheory.CharDualMat.mem_integer_of_dual (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (a : k)
    (h : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) → ψ (s * a) = 1) : a ∈ 𝒪[k] := by
  by_contra ha
  have hva : 1 < valuation k a := by
    rw [Valuation.mem_integer_iff] at ha
    exact not_le.1 ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hva
  obtain ⟨γ, hγ, hball⟩ := _root_.GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hmul : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a * u) = 1 := by
    intro s hs u hu
    have := h (s * u) (fun u' hu' => by rw [mul_assoc]; exact hs _ (mul_mem hu hu'))
    rw [mul_right_comm]
    exact this
  have hpow : ∀ n : ℕ, ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a ^ n * u) = 1 := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih => intro s hs; rw [pow_succ, ← mul_assoc]; exact hmul _ (ih s hs)
  apply hne
  ext t
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k t * γ⁻¹) hva
  have hlt : valuation k t * γ⁻¹ < valuation k a ^ (n + 1) :=
    lt_of_le_of_lt hn (pow_lt_pow_right₀ hva n.lt_succ_self)
  have hapos : valuation k a ^ (n + 1) ≠ 0 := pow_ne_zero _ (by simpa using ha0)
  have hlt' : valuation k t < γ * valuation k a ^ (n + 1) := by
    calc valuation k t = valuation k t * γ⁻¹ * γ := (inv_mul_cancel_right₀ hγ _).symm
      _ < valuation k a ^ (n + 1) * γ := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hγ)
      _ = γ * valuation k a ^ (n + 1) := mul_comm _ _
  have hs : ∀ u : k, u ∈ 𝒪[k] → ψ (t * (a ^ (n + 1))⁻¹ * u) = 1 := by
    intro u hu
    apply hball
    rw [Valuation.mem_integer_iff] at hu
    rw [map_mul, map_mul, map_inv₀, map_pow]
    calc valuation k t * (valuation k a ^ (n + 1))⁻¹ * valuation k u
        ≤ valuation k t * (valuation k a ^ (n + 1))⁻¹ := mul_le_of_le_one_right' hu
      _ < γ := mul_inv_lt_of_lt_mul₀ hlt'
  have := hpow (n + 1) _ hs 1 (one_mem _)
  rw [mul_one, inv_mul_cancel_right₀ (pow_ne_zero _ ha0)] at this
  rw [this, AddChar.one_apply]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `_root_.GlobalTheory.CharDualMat.mem_integer_of_dual ψk hψ hne (x r₀ q₀) (fun s hs => ?_)` and prove the remaining obligations. Set `b : Matrix Y Y' k` to `fun r q => if r = r₀ ∧ q = q₀ then s else 0`. Establish `key : ∀ y : Matrix Y Y' k, ∑ r, ∑ q, b r q * y r q = s * y r₀ q₀`. Introduce `y`. Rewrite using `[Finset.sum_eq_single r₀ (fun r _ hr => Finset.sum_eq_zero fun q _ => by simp [b, hr]) (by simp), Finset.sum_eq_single q₀ (fun q _ hq => by simp [b, hq]) (by simp)]`.

Simplify using `[b]`. Use `hx b (fun u hu => by rw [key]; exact hs _ (hu r₀ q₀))` as an intermediate fact. Rewrite `this` using `[key]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.CharDualMat.integral_of_dual (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle)
    (hψ : Continuous ψk) (hne : ψk ≠ 1) (x : Matrix Y Y' k)
    (hx : ∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) →
      ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1)
    (r₀ : Y) (q₀ : Y') : x r₀ q₀ ∈ 𝒪[k] := by
  classical
  refine _root_.GlobalTheory.CharDualMat.mem_integer_of_dual ψk hψ hne (x r₀ q₀) (fun s hs => ?_)
  let b : Matrix Y Y' k := fun r q => if r = r₀ ∧ q = q₀ then s else 0
  have key : ∀ y : Matrix Y Y' k, ∑ r, ∑ q, b r q * y r q = s * y r₀ q₀ := by
    intro y
    rw [Finset.sum_eq_single r₀ (fun r _ hr => Finset.sum_eq_zero fun q _ => by simp [b, hr])
      (by simp), Finset.sum_eq_single q₀ (fun q _ hq => by simp [b, hq]) (by simp)]
    simp [b]
  have := hx b (fun u hu => by rw [key]; exact hs _ (hu r₀ q₀))
  rwa [key] at this

end GlobalTheory.CharDualMat
