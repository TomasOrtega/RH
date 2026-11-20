import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HeckeRatioPoleOrders
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane Filter Topology Complex
open scoped Real

noncomputable section

namespace HeckeRatioPoleOrders

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons, Multiset.sum_map_mul_left]`.
-/
theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_zero_left]`.
-/
theorem esymm_zero {R : Type*} [CommSemiring R] (s : Multiset R) : s.esymm 0 = 1 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_left]

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_self]`.
-/
theorem esymm_card {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm (Multiset.card s) = s.prod := by
  simp [Multiset.esymm, Multiset.powersetCard_self]

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_eq_empty n h]`.
-/
theorem esymm_of_card_lt {R : Type*} [CommSemiring R] (s : Multiset R) {n : ℕ}
    (h : Multiset.card s < n) : s.esymm n = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty n h]

/- English proof (translation)
Establish `h` using `Multiset.pow_smul_esymm d⁻¹ k s`. Simplify using `only [smul_eq_mul] at h`. Rewrite using `[div_eq_mul_inv, ← inv_pow, mul_comm, h]`. Simplify using `[div_eq_mul_inv, mul_comm]`.
-/
theorem esymm_map_div (s : Multiset ℂ) (d : ℂ) (k : ℕ) :
    (s.map (· / d)).esymm k = s.esymm k / d ^ k := by
  have h := Multiset.pow_smul_esymm d⁻¹ k s
  simp only [smul_eq_mul] at h
  rw [div_eq_mul_inv, ← inv_pow, mul_comm, h]
  simp [div_eq_mul_inv, mul_comm]

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero => simp only [esymm_zero]`. Conclude with `tendsto_const_nhds`. Consider the case `succ k`. Simplify using `only [esymm_cons_succ]`.

Conclude with `(hM (k + 1)).add (hf.mul (hM k))`.
-/
theorem tendsto_esymm_cons {α : Type*} {l : Filter α} {f : α → ℂ} {x : ℂ} {M : α → Multiset ℂ}
    {N : Multiset ℂ} (hf : Tendsto f l (𝓝 x))
    (hM : ∀ k, Tendsto (fun t ↦ (M t).esymm k) l (𝓝 (N.esymm k))) (k : ℕ) :
    Tendsto (fun t ↦ (f t ::ₘ M t).esymm k) l (𝓝 ((x ::ₘ N).esymm k)) := by
  cases k with
  | zero => simp only [esymm_zero]; exact tendsto_const_nhds
  | succ k =>
    simp only [esymm_cons_succ]
    exact (hM (k + 1)).add (hf.mul (hM k))

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on generalizing k with`. Consider the case `empty => simp only [Multiset.map_zero]`. Conclude with `tendsto_const_nhds`. Consider the case `cons i s ih`. Simplify using `only [Multiset.map_cons]`.

Conclude with `tendsto_esymm_cons (hF i) ih k`.
-/
theorem tendsto_esymm_map {ι α : Type*} {l : Filter α} (s : Multiset ι) {F : ι → α → ℂ}
    {y : ι → ℂ} (hF : ∀ i, Tendsto (F i) l (𝓝 (y i))) (k : ℕ) :
    Tendsto (fun t ↦ (s.map (F · t)).esymm k) l (𝓝 ((s.map y).esymm k)) := by
  induction s using Multiset.induction_on generalizing k with
  | empty => simp only [Multiset.map_zero]; exact tendsto_const_nhds
  | cons i s ih =>
    simp only [Multiset.map_cons]
    exact tendsto_esymm_cons (hF i) ih k

def unitPart (z : ℍ) : ℂ := ModularForm.discriminant z / Function.Periodic.qParam 1 z

/- English proof (translation)
Rewrite using `[unitPart, mul_div_cancel₀ _ (Function.Periodic.qParam_ne_zero _)]`.
-/
theorem discriminant_eq (z : ℍ) :
    ModularForm.discriminant z = Function.Periodic.qParam 1 z * unitPart z := by
  rw [unitPart, mul_div_cancel₀ _ (Function.Periodic.qParam_ne_zero _)]

/- English proof (translation)
The claim follows from `div_ne_zero (ModularForm.discriminant_ne_zero z) (Function.Periodic.qParam_ne_zero _)`.
-/
theorem unitPart_ne_zero (z : ℍ) : unitPart z ≠ 0 :=
  div_ne_zero (ModularForm.discriminant_ne_zero z) (Function.Periodic.qParam_ne_zero _)

/- English proof (translation)
Use `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z ↦ ?_` and prove the remaining obligations. Rewrite using `[unitPart, ModularForm.discriminant_eq_q_prod, mul_div_cancel_left₀ _ (Function.Periodic.qParam_ne_zero _)]`.
-/
theorem tendsto_unitPart : Tendsto unitPart atImInfty (𝓝 1) := by
  refine ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z ↦ ?_
  rw [unitPart, ModularForm.discriminant_eq_q_prod,
    mul_div_cancel_left₀ _ (Function.Periodic.qParam_ne_zero _)]

/- English proof (translation)
Rewrite using `[← UpperHalfPlane.coe_im, coe_mulPoint]`. Simplify using the standard rewrite rules.
-/
theorem im_mulPoint (n : ℕ+) (τ : ℍ) : (mulPoint n τ).im = (n : ℝ) * τ.im := by
  rw [← UpperHalfPlane.coe_im, coe_mulPoint]
  simp

/- English proof (translation)
Rewrite using `[← UpperHalfPlane.coe_im, coe_divPoint]`. Simplify using the standard rewrite rules.
-/
theorem im_divPoint (n : ℕ+) (a : ℕ) (τ : ℍ) : (divPoint n a τ).im = τ.im / (n : ℝ) := by
  rw [← UpperHalfPlane.coe_im, coe_divPoint]
  simp

/- English proof (translation)
Use `tendsto_comap_iff.mpr ?_` and prove the remaining obligations. Establish `h : Tendsto (fun τ : ℍ ↦ τ.im) atImInfty atTop` using `tendsto_comap`. Use `h.const_mul_atTop (show (0 : ℝ) < n by positivity)` as an intermediate fact. Simplify `this` using `[Function.comp_def, im_mulPoint]`.
-/
theorem tendsto_mulPoint (n : ℕ+) : Tendsto (mulPoint n) atImInfty atImInfty := by
  refine tendsto_comap_iff.mpr ?_
  have h : Tendsto (fun τ : ℍ ↦ τ.im) atImInfty atTop := tendsto_comap
  have := h.const_mul_atTop (show (0 : ℝ) < n by positivity)
  simpa [Function.comp_def, im_mulPoint] using this

/- English proof (translation)
Use `tendsto_comap_iff.mpr ?_` and prove the remaining obligations. Establish `h : Tendsto (fun τ : ℍ ↦ τ.im) atImInfty atTop` using `tendsto_comap`. Use `h.atTop_div_const (show (0 : ℝ) < n by positivity)` as an intermediate fact. Simplify `this` using `[Function.comp_def, im_divPoint]`.
-/
theorem tendsto_divPoint (n : ℕ+) (a : ℕ) : Tendsto (divPoint n a) atImInfty atImInfty := by
  refine tendsto_comap_iff.mpr ?_
  have h : Tendsto (fun τ : ℍ ↦ τ.im) atImInfty atTop := tendsto_comap
  have := h.atTop_div_const (show (0 : ℝ) < n by positivity)
  simpa [Function.comp_def, im_divPoint] using this

/- English proof (translation)
Introduce `p hp hodd`. Take `⟨m, rfl⟩ : ∃ m, p = m + 1` from `⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩`. Take `⟨r, hr⟩` from `hodd`. Establish `hm : m = 2 * r` using `by omega`. Establish `hm2 : 2 ≤ m` using `by have := hp.two_le; omega`.

Establish `hm1 : (m : ℂ) + 1 ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero m`. Use `set P : ℕ+ := ⟨m + 1, hp.pos⟩ with hPdef`. Establish `hPn : (P : ℕ) = m + 1` using `rfl`. Establish `hP : (P : ℂ) = (m : ℂ) + 1` using `by simp [hPdef]`. Use `set ζ : ℂ := cexp (2 * π * Complex.I / ((m : ℂ) + 1)) with hζ`.

Use `set s : ℍ → ℂ := fun τ ↦ Function.Periodic.qParam ((m + 1 : ℕ) : ℝ) τ with hs_def`. Establish `hs0 : ∀ τ, s τ ≠ 0` using `fun τ ↦ Function.Periodic.qParam_ne_zero _`. Establish `hq : ∀ τ : ℍ, Function.Periodic.qParam 1 τ = s τ ^ (m + 1)`. Introduce `τ`. Simplify using `only [hs_def, Function.Periodic.qParam, ← Complex.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hqm : ∀ τ : ℍ, Function.Periodic.qParam 1 (mulPoint P τ) = Function.Periodic.qParam 1 τ ^ (m + 1)`. Introduce `τ`.

Rewrite using `[coe_mulPoint, hP]`. Simplify using `only [Function.Periodic.qParam, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hqd : ∀ (a : ℕ) (τ : ℍ), Function.Periodic.qParam 1 (divPoint P a τ) = ζ ^ a * s τ`. Introduce `a τ`. Rewrite using `[coe_divPoint, hP]`. Simplify using `only [hs_def, hζ, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hζp : ζ ^ (m + 1) = 1`. Rewrite using `[hζ, ← Complex.exp_nat_mul]`. Use `Complex.exp_two_pi_mul_I using 2` and compare the differences between its conclusion and the goal.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hs : Tendsto s atImInfty (𝓝 0)` using `UpperHalfPlane.qParam_tendsto_atImInfty (by positivity)`. Establish `hc : Tendsto (fun τ ↦ s τ ^ m) atImInfty (𝓝 0)`. Simplify `hs.pow m` using `[zero_pow (show m ≠ 0 by omega)]`.

Use `set σi : ℍ → ℂ := fun τ ↦ ((m : ℂ) + 1) ^ 12 * unitPart (mulPoint P τ) / unitPart τ with hσi`. Use `set σ : ℕ → ℍ → ℂ := fun a τ ↦ ζ ^ a * unitPart (divPoint P a τ) / unitPart τ with hσ`. Establish `hσit : Tendsto σi atImInfty (𝓝 (((m : ℂ) + 1) ^ 12))`. Use `((tendsto_unitPart.comp (tendsto_mulPoint P)).const_mul (((m : ℂ) + 1) ^ 12)).div tendsto_unitPart one_ne_zero` as an intermediate fact. Rewrite `this` using `[mul_one, div_one]`.

Use `this.congr fun τ ↦ ?_` and prove the remaining obligations. Simplify using `only [hσi, Pi.div_apply, Function.comp_apply]`. Establish `hσt : ∀ a, Tendsto (σ a) atImInfty (𝓝 (ζ ^ a))`. Introduce `a`. Use `((tendsto_unitPart.comp (tendsto_divPoint P a)).const_mul (ζ ^ a)).div tendsto_unitPart one_ne_zero` as an intermediate fact.

Rewrite `this` using `[mul_one, div_one]`. Use `this.congr fun τ ↦ ?_` and prove the remaining obligations. Simplify using `only [hσ, Pi.div_apply, Function.comp_apply]`. Use `set L : ℍ → Multiset ℂ := fun τ ↦ (Multiset.range (m + 1)).map (σ · τ) with hL`. Use `set Li : Multiset ℂ := (Multiset.range (m + 1)).map (ζ ^ ·) with hLi`.

Use `set N : ℍ → Multiset ℂ := fun τ ↦ ((s τ ^ m) ^ (m + 1 + 1) * σi τ) ::ₘ L τ with hN`. Establish `hH : ∀ τ, heckeRatios P τ = (N τ).map (· / s τ ^ m)`. Introduce `τ`. Simplify using `only [heckeRatios, hN, hL, Multiset.map_cons, Multiset.map_map, hPn]`. Use `congr 1`.

Rewrite using `[discriminant_eq, discriminant_eq, hqm, hq]`. Use `push_cast`. Use `hs0 τ` as an intermediate fact. Use `unitPart_ne_zero τ` as an intermediate fact. Simplify using `only [hσi]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `Multiset.map_congr rfl fun a _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Function.comp_apply, discriminant_eq, discriminant_eq, hqd, hq]`. Use `hs0 τ` as an intermediate fact.

Use `unitPart_ne_zero τ` as an intermediate fact. Simplify using `only [hσ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hE : ∀ k τ, (heckeRatios P τ).esymm k = (N τ).esymm k / (s τ ^ m) ^ k`.

Introduce `k τ`. Rewrite using `[hH, esymm_map_div]`. Establish `hNt : ∀ k, Tendsto (fun τ ↦ (N τ).esymm k) atImInfty (𝓝 ((0 ::ₘ Li).esymm k))`. Establish `h0 : Tendsto (fun τ ↦ (s τ ^ m) ^ (m + 1 + 1) * σi τ) atImInfty (𝓝 0)`. Simplify using `using (hc.pow (m + 1 + 1)).mul hσit`.

Conclude with `tendsto_esymm_cons h0 (tendsto_esymm_map _ hσt)`. Establish `hLt : Tendsto (fun τ ↦ (L τ).esymm (m + 1)) atImInfty (𝓝 (Li.esymm (m + 1)))` using `tendsto_esymm_map _ hσt (m + 1)`. Establish `hLi : Li.esymm (m + 1) = 1`. Establish `hcard : Multiset.card Li = m + 1` using `by simp [hLi]`. Establish `hS : ∑ i ∈ Finset.range (m + 1), i = (m + 1) * r`.

Establish `h2` using `Finset.sum_range_id_mul_two (m + 1)`. Use `Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num) (h2.trans ?_)` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel, hm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hcard, esymm_card, hLi, ← Finset.range_val, Finset.prod_map_val, Finset.prod_pow_eq_pow_sum, hS, pow_mul, hζp, one_pow]`.

Establish `hLi0 : (0 ::ₘ Li).esymm (m + 1) = 1`. Rewrite using `[esymm_cons_succ, zero_mul, add_zero]`. Conclude with `hLi`. Establish `hQ : ∀ τ : ℍ, Function.Periodic.qParam 1 τ ^ (m + 1 - 1) = (s τ ^ m) ^ (m + 1)`. Introduce `τ`.

Rewrite using `[Nat.add_sub_cancel, hq]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun k hk ↦ ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩ : ∃ j, m + 1 = k + (j + 1)` from `⟨m - k, by omega⟩`. Establish `h` using `(hc.pow (j + 1)).mul (hNt k)`.

Rewrite `h` using `[zero_pow (Nat.succ_ne_zero j), zero_mul]`. Use `h.congr fun τ ↦ ?_` and prove the remaining obligations. Use `pow_ne_zero m (hs0 τ)` as an intermediate fact. Rewrite using `[hQ, hE, hj, pow_add]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hNt (m + 1)`. Rewrite `h` using `[hLi0]`. Use `h.congr fun τ ↦ ?_` and prove the remaining obligations. Use `pow_ne_zero m (hs0 τ)` as an intermediate fact.

Rewrite using `[hQ, hE]`. Clear the denominators using the available nonvanishing facts. Establish `h` using `hσit.mul hLt`. Rewrite `h` using `[hLi, mul_one]`. Establish `hc' : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1` using `by push_cast; ring`.

Rewrite using `[hc']`. Use `h.congr fun τ ↦ ?_` and prove the remaining obligations. Use `pow_ne_zero m (hs0 τ)` as an intermediate fact. Establish `hcardL : Multiset.card (L τ) < m + 1 + 1` using `by simp [hL]`. Rewrite using `[hE, hN]`.

Simplify using `only`. Rewrite using `[esymm_cons_succ, esymm_of_card_lt _ hcardL, zero_add]`. Clear the denominators using the available nonvanishing facts.
-/
theorem proof : HeckeRatioPoleOrders.Statement := by
  intro p hp hodd
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  obtain ⟨r, hr⟩ := hodd
  have hm : m = 2 * r := by omega
  have hm2 : 2 ≤ m := by have := hp.two_le; omega
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  set P : ℕ+ := ⟨m + 1, hp.pos⟩ with hPdef
  have hPn : (P : ℕ) = m + 1 := rfl
  have hP : (P : ℂ) = (m : ℂ) + 1 := by simp [hPdef]

  set ζ : ℂ := cexp (2 * π * Complex.I / ((m : ℂ) + 1)) with hζ
  set s : ℍ → ℂ := fun τ ↦ Function.Periodic.qParam ((m + 1 : ℕ) : ℝ) τ with hs_def
  have hs0 : ∀ τ, s τ ≠ 0 := fun τ ↦ Function.Periodic.qParam_ne_zero _
  have hq : ∀ τ : ℍ, Function.Periodic.qParam 1 τ = s τ ^ (m + 1) := by
    intro τ
    simp only [hs_def, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hqm : ∀ τ : ℍ, Function.Periodic.qParam 1 (mulPoint P τ) =
      Function.Periodic.qParam 1 τ ^ (m + 1) := by
    intro τ
    rw [coe_mulPoint, hP]
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hqd : ∀ (a : ℕ) (τ : ℍ), Function.Periodic.qParam 1 (divPoint P a τ) =
      ζ ^ a * s τ := by
    intro a τ
    rw [coe_divPoint, hP]
    simp only [hs_def, hζ, Function.Periodic.qParam, ← Complex.exp_nat_mul,
      ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have hζp : ζ ^ (m + 1) = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    convert Complex.exp_two_pi_mul_I using 2
    push_cast
    field_simp
  have hs : Tendsto s atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty (by positivity)
  have hc : Tendsto (fun τ ↦ s τ ^ m) atImInfty (𝓝 0) := by
    simpa [zero_pow (show m ≠ 0 by omega)] using hs.pow m

  set σi : ℍ → ℂ := fun τ ↦ ((m : ℂ) + 1) ^ 12 * unitPart (mulPoint P τ) / unitPart τ
    with hσi
  set σ : ℕ → ℍ → ℂ := fun a τ ↦ ζ ^ a * unitPart (divPoint P a τ) / unitPart τ
    with hσ
  have hσit : Tendsto σi atImInfty (𝓝 (((m : ℂ) + 1) ^ 12)) := by
    have := ((tendsto_unitPart.comp (tendsto_mulPoint P)).const_mul
      (((m : ℂ) + 1) ^ 12)).div tendsto_unitPart one_ne_zero
    rw [mul_one, div_one] at this
    refine this.congr fun τ ↦ ?_
    simp only [hσi, Pi.div_apply, Function.comp_apply]
  have hσt : ∀ a, Tendsto (σ a) atImInfty (𝓝 (ζ ^ a)) := by
    intro a
    have := ((tendsto_unitPart.comp (tendsto_divPoint P a)).const_mul
      (ζ ^ a)).div tendsto_unitPart one_ne_zero
    rw [mul_one, div_one] at this
    refine this.congr fun τ ↦ ?_
    simp only [hσ, Pi.div_apply, Function.comp_apply]
  set L : ℍ → Multiset ℂ := fun τ ↦ (Multiset.range (m + 1)).map (σ · τ) with hL
  set Li : Multiset ℂ := (Multiset.range (m + 1)).map (ζ ^ ·) with hLi
  set N : ℍ → Multiset ℂ := fun τ ↦ ((s τ ^ m) ^ (m + 1 + 1) * σi τ) ::ₘ L τ with hN
  have hH : ∀ τ, heckeRatios P τ = (N τ).map (· / s τ ^ m) := by
    intro τ
    simp only [heckeRatios, hN, hL, Multiset.map_cons, Multiset.map_map, hPn]
    congr 1
    · rw [discriminant_eq, discriminant_eq, hqm, hq]
      push_cast
      have := hs0 τ
      have := unitPart_ne_zero τ
      simp only [hσi]
      field_simp
      ring
    · refine Multiset.map_congr rfl fun a _ ↦ ?_
      rw [Function.comp_apply, discriminant_eq, discriminant_eq, hqd, hq]
      have := hs0 τ
      have := unitPart_ne_zero τ
      simp only [hσ]
      field_simp
      ring
  have hE : ∀ k τ, (heckeRatios P τ).esymm k = (N τ).esymm k / (s τ ^ m) ^ k := by
    intro k τ
    rw [hH, esymm_map_div]
  have hNt : ∀ k, Tendsto (fun τ ↦ (N τ).esymm k) atImInfty (𝓝 ((0 ::ₘ Li).esymm k)) := by
    have h0 : Tendsto (fun τ ↦ (s τ ^ m) ^ (m + 1 + 1) * σi τ) atImInfty (𝓝 0) := by
      simpa using (hc.pow (m + 1 + 1)).mul hσit
    exact tendsto_esymm_cons h0 (tendsto_esymm_map _ hσt)
  have hLt : Tendsto (fun τ ↦ (L τ).esymm (m + 1)) atImInfty (𝓝 (Li.esymm (m + 1))) :=
    tendsto_esymm_map _ hσt (m + 1)

  have hLi : Li.esymm (m + 1) = 1 := by
    have hcard : Multiset.card Li = m + 1 := by simp [hLi]
    have hS : ∑ i ∈ Finset.range (m + 1), i = (m + 1) * r := by
      have h2 := Finset.sum_range_id_mul_two (m + 1)
      refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num) (h2.trans ?_)
      rw [Nat.add_sub_cancel, hm]
      ring
    rw [← hcard, esymm_card, hLi, ← Finset.range_val, Finset.prod_map_val,
      Finset.prod_pow_eq_pow_sum, hS, pow_mul, hζp, one_pow]
  have hLi0 : (0 ::ₘ Li).esymm (m + 1) = 1 := by
    rw [esymm_cons_succ, zero_mul, add_zero]
    exact hLi
  have hQ : ∀ τ : ℍ, Function.Periodic.qParam 1 τ ^ (m + 1 - 1) = (s τ ^ m) ^ (m + 1) := by
    intro τ
    rw [Nat.add_sub_cancel, hq]
    ring
  refine ⟨fun k hk ↦ ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j, m + 1 = k + (j + 1) := ⟨m - k, by omega⟩
    have h := (hc.pow (j + 1)).mul (hNt k)
    rw [zero_pow (Nat.succ_ne_zero j), zero_mul] at h
    refine h.congr fun τ ↦ ?_
    have := pow_ne_zero m (hs0 τ)
    rw [hQ, hE, hj, pow_add]
    field_simp
    ring
  · have h := hNt (m + 1)
    rw [hLi0] at h
    refine h.congr fun τ ↦ ?_
    have := pow_ne_zero m (hs0 τ)
    rw [hQ, hE]
    field_simp
  · have h := hσit.mul hLt
    rw [hLi, mul_one] at h
    have hc' : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    rw [hc']
    refine h.congr fun τ ↦ ?_
    have := pow_ne_zero m (hs0 τ)
    have hcardL : Multiset.card (L τ) < m + 1 + 1 := by simp [hL]
    rw [hE, hN]
    simp only
    rw [esymm_cons_succ, esymm_of_card_lt _ hcardL, zero_add]
    field_simp

end HeckeRatioPoleOrders

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
