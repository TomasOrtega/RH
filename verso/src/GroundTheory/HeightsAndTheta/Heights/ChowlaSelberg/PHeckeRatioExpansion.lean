import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesRing
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesInv
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.DeltaIntSeries
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesNorm
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm PowerSeries Complex
open scoped Real Manifold

noncomputable section

namespace HeckeRatioExpansion

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons, Multiset.sum_map_mul_left]`.
-/
theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

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
Apply `summable_of_ne_finset_zero (s := {1})` to reduce the goal to its premises. Introduce `n hn`. Simplify using `only [Finset.mem_singleton] at hn`. Simplify using `[coeff_X, hn]`.
-/
theorem intSeriesConv_X (r : ℝ) : IntSeriesConv X r := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_X, hn]

/- English proof (translation)
Rewrite using `[intSeriesEval, tsum_eq_single 1 (fun n hn ↦ by simp [coeff_X, hn])]`. Simplify using the standard rewrite rules.
-/
theorem intSeriesEval_X (z : ℂ) : intSeriesEval X z = z := by
  rw [intSeriesEval, tsum_eq_single 1 (fun n hn ↦ by simp [coeff_X, hn])]
  simp

/- English proof (translation)
Take `⟨-, hmul, hsum, -, -⟩` from `hR r hr`. Use `⟨{ toFun := fun F ↦ intSeriesEval F z map_one' := ?_ map_mul' := fun F G ↦ hmul F G ((hS F).1 F.2) ((hS G).1 G.2) z hz map_zero' := by simp [intSeriesEval] map_add' := fun F G ↦ ?_ }, fun _ ↦ rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `intSeriesEval 1 z = 1`. Rewrite using `[intSeriesEval, tsum_eq_single 0 (fun n hn ↦ by simp [coeff_one, hn])]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `intSeriesEval ((F : PowerSeries ℤ) + G) z = intSeriesEval F z + intSeriesEval G z`. Use `(hsum _ ((hS _).1 (S.add_mem F.2 G.2)) z hz).unique ?_` and prove the remaining obligations. Simplify `(hsum F ((hS F).1 F.2) z hz).add (hsum G ((hS G).1 G.2) z hz)` using `[add_mul]`.
-/
theorem exists_evalHom (hR : IntSeriesRing.Statement) {r : ℝ} (hr : 0 ≤ r)
    (S : Subring (PowerSeries ℤ)) (hS : ∀ F, F ∈ S ↔ IntSeriesConv F r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ∃ φ : S →+* ℂ, ∀ F : S, φ F = intSeriesEval F z := by
  obtain ⟨-, hmul, hsum, -, -⟩ := hR r hr
  refine ⟨{ toFun := fun F ↦ intSeriesEval F z
            map_one' := ?_
            map_mul' := fun F G ↦ hmul F G ((hS F).1 F.2) ((hS G).1 G.2) z hz
            map_zero' := by simp [intSeriesEval]
            map_add' := fun F G ↦ ?_ }, fun _ ↦ rfl⟩
  · change intSeriesEval 1 z = 1
    rw [intSeriesEval, tsum_eq_single 0 (fun n hn ↦ by simp [coeff_one, hn])]
    simp
  · change intSeriesEval ((F : PowerSeries ℤ) + G) z = intSeriesEval F z + intSeriesEval G z
    refine (hsum _ ((hS _).1 (S.add_mem F.2 G.2)) z hz).unique ?_
    simpa [add_mul] using (hsum F ((hS F).1 F.2) z hz).add (hsum G ((hS G).1 G.2) z hz)

/- English proof (translation)
Introduce `p hp k`. Use `⟨hH _ k, ?_⟩` and prove the remaining obligations. Break down `k with _ | k` into its components or cases. Simplify `hasIntegralLaurentQExpansion_const 1` using `[Multiset.esymm]`. Take `⟨D, hD0, hDc, hΔ⟩` from `hD`.

Establish `hp0 : 0 < p` using `hp.pos`. Use `set n : ℕ+ := ⟨p, hp.pos⟩ with hn`. Establish `hnp : (n : ℕ) = p` using `rfl`. Establish `hpne : p ≠ 0` using `hp0.ne'`. Establish `hD2 : IntSeriesConv D (1 / 2)` using `hDc _ (by norm_num) (by norm_num)`.

Take `⟨⟨S₂, hS₂⟩, hmul₂, -, -, -⟩` from `hR (1 / 2) (by norm_num)`. Establish `hGc : IntSeriesConv (X * D) (1 / 2)` using `(hS₂ _).1 (S₂.mul_mem ((hS₂ _).2 (intSeriesConv_X _)) ((hS₂ _).2 hD2))`. Establish `evG : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → intSeriesEval (X * D) w = w * intSeriesEval D w`. Introduce `w hw`. Rewrite using `[hmul₂ _ _ (intSeriesConv_X _) hD2 w hw, intSeriesEval_X]`.

Take `⟨E₁, hE₁c, hE₁⟩` from `hN (X * D) (1 / 2) (by norm_num) hGc p hp0 (k + 1)`. Take `⟨E₀, hE₀c, hE₀⟩` from `hN (X * D) (1 / 2) (by norm_num) hGc p hp0 k`. Take `⟨V, r₁, hr₁, hVc, hDV⟩` from `hI D (1 / 2) (by norm_num) hD2 hD0`. Use `set R : ℝ := min ((1 / 2) ^ p) r₁ with hRdef`. Establish `hR0 : 0 < R` using `lt_min (by positivity) hr₁`.

Establish `hRh : R ≤ (1 / 2) ^ p` using `min_le_left _ _`. Establish `hRr : R ≤ r₁` using `min_le_right _ _`. Establish `hRl : R < 1` using `hRh.trans_lt (pow_lt_one₀ (by norm_num) (by norm_num) hpne)`. Take `⟨⟨S, hS⟩, hmul, hsum, -, hexp⟩` from `hR R hR0.le`. Establish `mem : ∀ F r', IntSeriesConv F r' → R ≤ r' → F ∈ S` using `fun F r' h h' ↦ (hS F).2 ((hR r' (hR0.le.trans h')).2.2.2.1 F R h hR0.le h')`.

Establish `hDp : IntSeriesConv D (R ^ p)` using `hDc _ (by positivity) (pow_lt_one₀ hR0.le hRl hpne)`. Set `Φ : S` to `(⟨E₁, mem _ _ hE₁c hRh⟩ + (p : S) ^ 12 * ⟨X, (hS _).2 (intSeriesConv_X R)⟩ ^ p * ⟨expand p hpne D, (hS _).2 (hexp p hpne D hDp).1⟩ * ⟨E₀, mem _ _ hE₀c hRh⟩) * ⟨V, mem _ _ hVc hRr⟩ ^ (k + 1)`. Use `⟨k + 1, fun n ↦ coeff n (Φ : PowerSeries ℤ), -Real.log R / (2 * π), fun τ hτ ↦ ?_⟩` and prove the remaining obligations. Use `set q := Function.Periodic.qParam 1 (τ : ℂ) with hq`. Use `set t := Function.Periodic.qParam p (τ : ℂ) with ht`.

Establish `hqR : ‖q‖ < R`. Establish `h` using `(Function.Periodic.norm_qParam_lt_iff one_pos (-Real.log R / (2 * π)) τ).2 hτ`. Rewrite `h` using `[show -2 * π * (-Real.log R / (2 * π)) / 1 = Real.log R by field_simp, Real.exp_log hR0]`. Then use the resulting hypothesis. Establish `htq : t ^ p = q`. Simplify using `only [ht, hq, Function.Periodic.qParam, ← Complex.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `ht0 : t ≠ 0` using `Function.Periodic.qParam_ne_zero _`. Establish `hq0 : q ≠ 0` using `Function.Periodic.qParam_ne_zero _`.

Establish `htle : ‖t‖ ≤ 1 / 2`. Use `(lt_of_pow_lt_pow_left₀ p (by norm_num) ?_).le` and prove the remaining obligations. Rewrite using `[← norm_pow, htq]`. Conclude with `hqR.trans_le hRh`. Establish `hpt : ∀ a : ℕ, ‖Complex.exp (2 * π * Complex.I * a / p) * t‖ ≤ 1 / 2`.

Introduce `a`. Rewrite using `[norm_mul, Complex.norm_exp]`. Simplify using `using htle`. Establish `hdiv : ∀ a : ℕ, Function.Periodic.qParam 1 (divPoint n a τ) = Complex.exp (2 * π * Complex.I * a / p) * t`. Introduce `a`.

Rewrite using `[coe_divPoint]`. Simplify using `only [ht, Function.Periodic.qParam, ← Complex.exp_add, hnp]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmulp : Function.Periodic.qParam 1 (mulPoint n τ) = q ^ p`. Rewrite using `[coe_mulPoint]`. Simplify using `only [hq, Function.Periodic.qParam, ← Complex.exp_nat_mul, hnp]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨φ, hφ⟩` from `exists_evalHom hR hR0.le S hS hqR.le`. Establish `hDV' : intSeriesEval D q * intSeriesEval V q = 1`. Use `congrArg φ (show (⟨D, mem _ _ hD2 ((hRh.trans (pow_le_of_le_one (by norm_num) (by norm_num) hpne)).trans (by norm_num))⟩ : S) * ⟨V, mem _ _ hVc hRr⟩ = 1 from Subtype.ext hDV)` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, hφ, hφ]`. Then use the resulting hypothesis.

Establish `hd0 : intSeriesEval D q ≠ 0` using `left_ne_zero_of_mul_eq_one hDV'`. Establish `hY : (Multiset.range p).map (fun a ↦ discriminant (divPoint n a τ) / discriminant τ) = ((Multiset.range p).map fun a : ℕ ↦ intSeriesEval (X * D) (Complex.exp (2 * π * Complex.I * a / p) * t)).map (· / discriminant τ)`. Rewrite using `[Multiset.map_map]`. Use `Multiset.map_congr rfl fun a _ ↦ ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[hΔ (divPoint _ a τ), hdiv a, evG _ (hpt a)]`. Establish `key : q ^ (k + 1) * (heckeRatios n τ).esymm (k + 1) = φ Φ`. Unfold `heckeRatios`. Rewrite using `[hnp, esymm_cons_succ, hY, esymm_map_div, esymm_map_div, hE₁ t ht0 htle, hE₀ t ht0 htle, htq, hΔ τ, hΔ (mulPoint _ τ), hmulp, ← (hexp p hpne D hDp).2 q hqR.le]`. Simplify using `only [Φ, map_add, map_mul, map_pow, map_natCast]`.

Simplify using `only [hφ, intSeriesEval_X]`. Rewrite using `[← hq]`. Rewrite using `[eq_inv_of_mul_eq_one_right hDV', inv_pow]`. Clear denominators, using `[hd0, hq0]` for the nonvanishing conditions. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key, hφ]`. Conclude with `hsum _ ((hS _).1 Φ.2) q hqR.le`.
-/
theorem proof (hR : IntSeriesRing.Statement) (hI : IntSeriesInv.Statement)
    (hD : DeltaIntSeries.Statement) (hN : IntSeriesNorm.Statement)
    (hH : HeckeRatioHolo.Statement) : HeckeRatioExpansion.Statement := by
  intro p hp k
  refine ⟨hH _ k, ?_⟩
  rcases k with _ | k
  · simpa [Multiset.esymm] using hasIntegralLaurentQExpansion_const 1
  obtain ⟨D, hD0, hDc, hΔ⟩ := hD
  have hp0 : 0 < p := hp.pos
  set n : ℕ+ := ⟨p, hp.pos⟩ with hn
  have hnp : (n : ℕ) = p := rfl
  have hpne : p ≠ 0 := hp0.ne'

  have hD2 : IntSeriesConv D (1 / 2) := hDc _ (by norm_num) (by norm_num)
  obtain ⟨⟨S₂, hS₂⟩, hmul₂, -, -, -⟩ := hR (1 / 2) (by norm_num)
  have hGc : IntSeriesConv (X * D) (1 / 2) :=
    (hS₂ _).1 (S₂.mul_mem ((hS₂ _).2 (intSeriesConv_X _)) ((hS₂ _).2 hD2))
  have evG : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → intSeriesEval (X * D) w = w * intSeriesEval D w := by
    intro w hw
    rw [hmul₂ _ _ (intSeriesConv_X _) hD2 w hw, intSeriesEval_X]
  obtain ⟨E₁, hE₁c, hE₁⟩ := hN (X * D) (1 / 2) (by norm_num) hGc p hp0 (k + 1)
  obtain ⟨E₀, hE₀c, hE₀⟩ := hN (X * D) (1 / 2) (by norm_num) hGc p hp0 k
  obtain ⟨V, r₁, hr₁, hVc, hDV⟩ := hI D (1 / 2) (by norm_num) hD2 hD0

  set R : ℝ := min ((1 / 2) ^ p) r₁ with hRdef
  have hR0 : 0 < R := lt_min (by positivity) hr₁
  have hRh : R ≤ (1 / 2) ^ p := min_le_left _ _
  have hRr : R ≤ r₁ := min_le_right _ _
  have hRl : R < 1 := hRh.trans_lt (pow_lt_one₀ (by norm_num) (by norm_num) hpne)
  obtain ⟨⟨S, hS⟩, hmul, hsum, -, hexp⟩ := hR R hR0.le
  have mem : ∀ F r', IntSeriesConv F r' → R ≤ r' → F ∈ S := fun F r' h h' ↦
    (hS F).2 ((hR r' (hR0.le.trans h')).2.2.2.1 F R h hR0.le h')
  have hDp : IntSeriesConv D (R ^ p) := hDc _ (by positivity) (pow_lt_one₀ hR0.le hRl hpne)
  let Φ : S := (⟨E₁, mem _ _ hE₁c hRh⟩ + (p : S) ^ 12 * ⟨X, (hS _).2 (intSeriesConv_X R)⟩ ^ p *
      ⟨expand p hpne D, (hS _).2 (hexp p hpne D hDp).1⟩ * ⟨E₀, mem _ _ hE₀c hRh⟩) *
    ⟨V, mem _ _ hVc hRr⟩ ^ (k + 1)
  refine ⟨k + 1, fun n ↦ coeff n (Φ : PowerSeries ℤ), -Real.log R / (2 * π), fun τ hτ ↦ ?_⟩
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hq
  set t := Function.Periodic.qParam p (τ : ℂ) with ht
  have hqR : ‖q‖ < R := by
    have h := (Function.Periodic.norm_qParam_lt_iff one_pos (-Real.log R / (2 * π)) τ).2 hτ
    rwa [show -2 * π * (-Real.log R / (2 * π)) / 1 = Real.log R by field_simp,
      Real.exp_log hR0] at h
  have htq : t ^ p = q := by
    simp only [ht, hq, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have ht0 : t ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hq0 : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have htle : ‖t‖ ≤ 1 / 2 := by
    refine (lt_of_pow_lt_pow_left₀ p (by norm_num) ?_).le
    rw [← norm_pow, htq]
    exact hqR.trans_le hRh
  have hpt : ∀ a : ℕ, ‖Complex.exp (2 * π * Complex.I * a / p) * t‖ ≤ 1 / 2 := by
    intro a
    rw [norm_mul, Complex.norm_exp]
    simpa using htle
  have hdiv : ∀ a : ℕ, Function.Periodic.qParam 1 (divPoint n a τ) =
      Complex.exp (2 * π * Complex.I * a / p) * t := by
    intro a
    rw [coe_divPoint]
    simp only [ht, Function.Periodic.qParam, ← Complex.exp_add, hnp]
    congr 1
    push_cast
    ring
  have hmulp : Function.Periodic.qParam 1 (mulPoint n τ) = q ^ p := by
    rw [coe_mulPoint]
    simp only [hq, Function.Periodic.qParam, ← Complex.exp_nat_mul, hnp]
    congr 1
    push_cast
    ring
  obtain ⟨φ, hφ⟩ := exists_evalHom hR hR0.le S hS hqR.le
  have hDV' : intSeriesEval D q * intSeriesEval V q = 1 := by
    have := congrArg φ (show (⟨D, mem _ _ hD2 ((hRh.trans (pow_le_of_le_one (by norm_num)
        (by norm_num) hpne)).trans (by norm_num))⟩ : S) * ⟨V, mem _ _ hVc hRr⟩ = 1 from
      Subtype.ext hDV)
    rwa [map_mul, map_one, hφ, hφ] at this
  have hd0 : intSeriesEval D q ≠ 0 := left_ne_zero_of_mul_eq_one hDV'
  have hY : (Multiset.range p).map (fun a ↦ discriminant (divPoint n a τ) /
      discriminant τ) = ((Multiset.range p).map fun a : ℕ ↦
        intSeriesEval (X * D) (Complex.exp (2 * π * Complex.I * a / p) * t)).map
          (· / discriminant τ) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun a _ ↦ ?_
    simp only [Function.comp_apply]
    rw [hΔ (divPoint _ a τ), hdiv a, evG _ (hpt a)]
  have key : q ^ (k + 1) * (heckeRatios n τ).esymm (k + 1) = φ Φ := by
    unfold heckeRatios
    rw [hnp, esymm_cons_succ, hY, esymm_map_div, esymm_map_div, hE₁ t ht0 htle,
      hE₀ t ht0 htle, htq, hΔ τ, hΔ (mulPoint _ τ), hmulp,
      ← (hexp p hpne D hDp).2 q hqR.le]
    simp only [Φ, map_add, map_mul, map_pow, map_natCast]
    simp only [hφ, intSeriesEval_X]
    rw [← hq]
    rw [eq_inv_of_mul_eq_one_right hDV', inv_pow]
    field_simp [hd0, hq0]
    ring
  rw [key, hφ]
  exact hsum _ ((hS _).1 Φ.2) q hqR.le

end HeckeRatioExpansion

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
