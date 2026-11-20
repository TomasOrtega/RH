import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul

noncomputable section

namespace SmallGenTwist

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def SmallGen (y : (Σ k, ι k) → Ω) (A : HermLine ι) : Prop :=
  ∃ (n : ℕ) (w : Fin n → Ω), (∀ j, w j ∈ chartLat y A.a 1) ∧ KH.GeneratesOn y A.a w ∧
    ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)

/- English proof (translation)
Use `choose c hc using hz.1`. Use `⟨c, hc, fun k h0 => ?_⟩` and prove the remaining obligations. Establish `hX : IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _` using `(by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1`. Rewrite using `[← X] at h)` and apply the resulting hypothesis. Establish `hmem` using `mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])`.

Establish `hz0` using `hz.2 _ hmem`. Simplify using `only [map_X, eval_X] at hz0`. Conclude with `hc k hz0`.
-/
theorem exists_chart (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hz.1
  refine ⟨c, hc, fun k h0 => ?_⟩
  have hX : IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _ :=
    (by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
        rwa [← X] at h)
  have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
  have hz0 := hz.2 _ hmem
  simp only [map_X, eval_X] at hz0
  exact hc k hz0

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `c hc`. Establish `h` using `mul_mem (hs c hc) (ht c hc)`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_mul_mul_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc k)]`. Use `congr 1`. Simplify using `only [Pi.add_apply, Nat.cast_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_chartLat (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {s t : Ω} (hs : s ∈ chartLat y a 1)
    (ht : t ∈ chartLat y b 1) : s * t ∈ chartLat y (a + b) 1 := by
  intro c hc
  have h := mul_mem (hs c hc) (ht c hc)
  convert h using 1
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Nat.cast_one, one_mul]
  ring

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `c hc`. Take `⟨u, hu, hsum⟩` from `hw c hc`. Take `⟨u', hu', hsum'⟩` from `hv c hc`. Use `⟨fun j => u (finProdFinEquiv.symm j).1 * u' (finProdFinEquiv.symm j).2, fun j => mul_mem (hu _) (hu' _), ?_⟩` and prove the remaining obligations. Use `set Pa := ∏ k, y ⟨k, c k⟩ ^ (-a k) with hPa`.

Use `set Pb := ∏ k, y ⟨k, c k⟩ ^ (-b k) with hPb`. Establish `hP : ∏ k, y ⟨k, c k⟩ ^ (-((a + b) k)) = Pa * Pb`. Rewrite using `[hPa, hPb, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc k)]`.

Use `congr 1`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hP, Fintype.sum_equiv finProdFinEquiv.symm _ (fun p : Fin n × Fin m => u p.1 * u' p.2 * (w p.1 * v p.2 * (Pa * Pb))) (fun _ => rfl), Fintype.sum_prod_type]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring`. Use `_ = 1 := by rw [hsum, hsum', one_mul]`.
-/
theorem generatesOn_mul (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {n m : ℕ} {w : Fin n → Ω} {v : Fin m → Ω}
    (hw : KH.GeneratesOn y a w) (hv : KH.GeneratesOn y b v) :
    KH.GeneratesOn y (a + b)
      (fun j : Fin (n * m) => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2) := by
  intro c hc
  obtain ⟨u, hu, hsum⟩ := hw c hc
  obtain ⟨u', hu', hsum'⟩ := hv c hc
  refine ⟨fun j => u (finProdFinEquiv.symm j).1 * u' (finProdFinEquiv.symm j).2,
    fun j => mul_mem (hu _) (hu' _), ?_⟩
  set Pa := ∏ k, y ⟨k, c k⟩ ^ (-a k) with hPa
  set Pb := ∏ k, y ⟨k, c k⟩ ^ (-b k) with hPb
  have hP : ∏ k, y ⟨k, c k⟩ ^ (-((a + b) k)) = Pa * Pb := by
    rw [hPa, hPb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [hP, Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin n × Fin m => u p.1 * u' p.2 * (w p.1 * v p.2 * (Pa * Pb))) (fun _ => rfl),
    Fintype.sum_prod_type]
  calc ∑ i, ∑ l, u i * u' l * (w i * v l * (Pa * Pb))
      = (∑ i, u i * (w i * Pa)) * ∑ l, u' l * (v l * Pb) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    _ = 1 := by rw [hsum, hsum', one_mul]

/- English proof (translation)
Introduce `dg dh g h z hg hh hdeg he hz`. Take `⟨c, hc, hy⟩` from `exists_chart y hz`. Take `⟨N, dgs, gs, hgs, hdgs, hvs⟩` from `exists_chartForm y A.a 1 hs c hy`. Take `⟨M, dgt, gt, hgt, hdgt, hvt⟩` from `exists_chartForm y B.a 1 ht c hy`. Establish `bs` using `hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz`.

Establish `bt` using `hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz`. Establish `hdeq : dgs + dgt + dh = dg + (N + M)`. Use function extensionality and compare the values at `k`. Establish `e1` using `hdgs k`. Establish `e2` using `hdgt k`.

Establish `e3` using `hdeg k`. Establish `e4` using `hCa k`. Simplify using `only [Pi.add_apply]`. Establish `: ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ)`. Move the coercions through the operations in `at e1 e2 e3 ⊢`.

Take the linear combination `e1 + e2 - e3 - e4`. Conclude with `this` after adjusting the coercions. Establish `hF : IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh)`. Use `isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs hgt) hh) ?_` and prove the remaining obligations. Rewrite using `[hdeq]`.

Conclude with `isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))`. Establish `hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) = aeval w (chartMono c N) * aeval w (chartMono c M)` using `fun w => by`. Rewrite using `[aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`. Establish `hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0`.

Rewrite using `[map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz0` using `hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)`. Simplify using `only [map_sub, map_mul] at hz0`. Rewrite `hz0` using `[sub_eq_zero]`.

Use `set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev`. Establish `hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M)`. Simplify using `only [hev, eval_chartMono, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`. Establish `hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖`.

Apply the tactic sequence `refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>`. Simplify using `only [hev, eval_chartMono]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Establish `key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) = ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖`. Rewrite using `[← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]`.

Conclude with `congrArg norm hz0.symm`. Establish `hprod : ‖ev gs‖ * ‖ev gt‖ ≤ (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1)` using `mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)`. Use `le_of_mul_le_mul_right ?_ hpos` and prove the remaining obligations. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hCh]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isSmallH_mul (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (hCa : ∀ k, C.a k = A.a k + B.a k)
    (hCh : ∀ z, C.h z = A.h z * B.h z) {s t : Ω} (hs : s ∈ chartLat y A.a 1) (ht : t ∈ chartLat y B.a 1)
    (hbs : IsSmallH (mCoordIdeal y) y A 1 s) (hbt : IsSmallH (mCoordIdeal y) y B 1 t) :
    IsSmallH (mCoordIdeal y) y C 1 (s * t) := by
  intro dg dh g h z hg hh hdeg he hz
  obtain ⟨c, hc, hy⟩ := exists_chart y hz
  obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a 1 hs c hy
  obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
  have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
  have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

  have hdeq : dgs + dgt + dh = dg + (N + M) := by
    funext k
    have e1 := hdgs k
    have e2 := hdgt k
    have e3 := hdeg k
    have e4 := hCa k
    simp only [Pi.add_apply]
    have : ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ) := by
      push_cast at e1 e2 e3 ⊢
      linear_combination e1 + e2 - e3 - e4
    exact_mod_cast this
  have hF : IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh) := by
    refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs hgt) hh) ?_
    rw [hdeq]
    exact isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))
  have hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) =
      aeval w (chartMono c N) * aeval w (chartMono c M) := fun w => by
    rw [aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  simp only [map_sub, map_mul] at hz0
  rw [sub_eq_zero] at hz0

  set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
  have hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M) := by
    simp only [hev, eval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ := by
    refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>
    · simp only [hev, eval_chartMono]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) =
      ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖ := by
    rw [← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]
    exact congrArg norm hz0.symm
  have hprod : ‖ev gs‖ * ‖ev gt‖ ≤
      (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) :=
    mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [key]
  calc ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖
      ≤ (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) * ‖ev h‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖ev h‖ * C.h z ^ 1 * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) := by
        rw [hCh]
        ring

/- English proof (translation)
Take `⟨n, w, hw, hgw, hsw⟩` from `hA`. Take `⟨m, v, hv, hgv, hsv⟩` from `hB`. Use `⟨n * m, fun j => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2, fun j => ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hCa]`. Conclude with `mul_mem_chartLat y (hw _) (hv _)`.

Rewrite using `[hCa]`. Conclude with `generatesOn_mul y hgw hgv`. Conclude with `isSmallH_mul y A B C (fun k => by rw [hCa]; rfl) hCh (hw _) (hv _) (hsw _) (hsv _)`.
-/
theorem smallGen_mul (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (hCa : C.a = A.a + B.a)
    (hCh : ∀ z, C.h z = A.h z * B.h z) (hA : SmallGen y A) (hB : SmallGen y B) : SmallGen y C := by
  obtain ⟨n, w, hw, hgw, hsw⟩ := hA
  obtain ⟨m, v, hv, hgv, hsv⟩ := hB
  refine ⟨n * m, fun j => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2,
    fun j => ?_, ?_, fun j => ?_⟩
  · rw [hCa]
    exact mul_mem_chartLat y (hw _) (hv _)
  · rw [hCa]
    exact generatesOn_mul y hgw hgv
  · exact isSmallH_mul y A B C (fun k => by rw [hCa]; rfl) hCh (hw _) (hv _) (hsw _) (hsv _)

/- English proof (translation)
Use `⟨1, fun _ => 1, fun _ => ?_, ?_, fun _ => ?_⟩` and prove the remaining obligations. Introduce `c hc`. Simplify using `[hEa]`. Introduce `c hc`. Use `⟨fun _ => 1, fun _ => one_mem _, ?_⟩` and prove the remaining obligations.

Simplify using `[hEa]`. Introduce `dg dh g h z hg hh hdeg he hz`. Establish `hd : dg = dh` using `funext fun k => by`. Use `hdeg k` as an intermediate fact. Rewrite `this` using `[hEa]`.

Simplify using `only [Pi.zero_apply, mul_zero, add_zero] at this`. Conclude with `this` after adjusting the coercions. Substitute `hd` using the available equality. Establish `h0 : aeval y (g - h) = 0` using `by rw [map_sub, he, one_mul, sub_self]`. Establish `hz0` using `hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_sub hg hh) h0)`.

Simplify using `only [map_sub, sub_eq_zero] at hz0`. Rewrite using `[hz0, hEh, pow_one, mul_one]`.
-/
theorem smallGen_of_trivial (y : (Σ k, ι k) → Ω) (E : HermLine ι) (hEa : E.a = 0) (hEh : ∀ z, E.h z = 1) :
    SmallGen y E := by
  refine ⟨1, fun _ => 1, fun _ => ?_, ?_, fun _ => ?_⟩
  · intro c hc
    simp [hEa]
  · intro c hc
    refine ⟨fun _ => 1, fun _ => one_mem _, ?_⟩
    simp [hEa]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = dh := funext fun k => by
      have := hdeg k
      rw [hEa] at this
      simp only [Pi.zero_apply, mul_zero, add_zero] at this
      exact_mod_cast this
    subst hd
    have h0 : aeval y (g - h) = 0 := by rw [map_sub, he, one_mul, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_sub hg hh) h0)
    simp only [map_sub, sub_eq_zero] at hz0
    rw [hz0, hEh, pow_one, mul_one]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[fsH, HermLine.ofMetrics]`.
-/
theorem fsH_a [∀ k, Fintype (ι k)] : (fsH ι).a = fun _ => 1 := by
  funext k
  simp [fsH, HermLine.ofMetrics]

/- English proof (translation)
Use `set e := Fintype.equivFin (∀ k, ι k) with he_def`. Use `⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) 1), fun j => ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Introduce `c hc beta_reduce`. Rewrite using `[aeval_chartMono, ← Finset.prod_mul_distrib]`. Use `prod_mem fun k _ => ?_` and prove the remaining obligations.

Establish `hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c` using `Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩`. Use `hmem using 1` and compare the differences between its conclusion and the goal. Simplify using `[fsH_a, div_eq_mul_inv]`. Introduce `c hc`. Apply the tactic sequence `refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩`.

Rewrite using `[Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) * (aeval y (chartMono i 1) * ∏ k, y ⟨k, c k⟩ ^ (-(fsH ι).a k))) (fun _ => rfl)]`. Simplify using `only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[aeval_chartMono, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => by simp [fsH_a, hc k]`. Introduce `dg dh g h z hg hh hdeg he hz`.

Establish `hd : dg = 1 + dh` using `funext fun k => by`. Use `hdeg k` as an intermediate fact. Simplify using `only [fsH_a, Nat.cast_one, one_mul] at this`. Simplify using `only [Pi.add_apply, Pi.one_apply]`. Use linear arithmetic over natural numbers and integers.

Establish `hF : IsMultiHomog (g - chartMono (e.symm j) 1 * h) dg` using `isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ 1) hh)`. Establish `h0 : aeval y (g - chartMono (e.symm j) 1 * h) = 0`. Rewrite using `[map_sub, map_mul, he, sub_self]`. Establish `hz0` using `hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)`. Simplify using `only [map_sub, map_mul, sub_eq_zero] at hz0`.

Rewrite using `[hz0, norm_mul, eval_chartMono, pow_one, mul_comm]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Simplify using `only [Pi.one_apply, pow_one, norm_prod]`. Establish `hH : (fsH ι).h z = ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖`. Simplify using `[fsH, HermLine.ofMetrics, fsMetric]`.

Rewrite using `[hH]`. Use `Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_` and prove the remaining obligations. Use `PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) ((e.symm j) k)` as an intermediate fact. Rewrite `this` using `[PiLp.toLp_apply]`. Then use the resulting hypothesis.
-/
theorem smallGen_fsH (y : (Σ k, ι k) → Ω) : SmallGen y (fsH ι) := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) 1), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert hmem using 1
    simp [fsH_a, div_eq_mul_inv]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i 1) * ∏ k, y ⟨k, c k⟩ ^ (-(fsH ι).a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by simp [fsH_a, hc k]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = 1 + dh := funext fun k => by
      have := hdeg k
      simp only [fsH_a, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hF : IsMultiHomog (g - chartMono (e.symm j) 1 * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ 1) hh)
    have h0 : aeval y (g - chartMono (e.symm j) 1 * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [Pi.one_apply, pow_one, norm_prod]
    have hH : (fsH ι).h z = ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ := by
      simp [fsH, HermLine.ofMetrics, fsMetric]
    rw [hH]
    refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
    have := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) ((e.symm j) k)
    rwa [PiLp.toLp_apply] at this

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero`. Proceed by induction on `p with`. Consider the case `zero`. Conclude with `smallGen_of_trivial y _ (by funext k; simp [HermLine.zcomb]) (fun z => by simp [HermLine.zcomb])`.

Consider the case `succ p ih`. Use `smallGen_mul y _ (fsH ι) _ ?_ (fun z => ?_) ih (smallGen_fsH y)` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [HermLine.zcomb, zpow_natCast, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ q ih`. Use `smallGen_mul y _ L _ ?_ (fun z => ?_) ih hL` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Simplify using `only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [HermLine.zcomb, zpow_natCast, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem smallGen_zcomb (y : (Σ k, ι k) → Ω) (L : HermLine ι) (hL : SmallGen y L) (q p : ℕ) :
    SmallGen y (HermLine.zcomb L (fsH ι) q p) := by
  induction q with
  | zero =>
    induction p with
    | zero =>
      exact smallGen_of_trivial y _ (by funext k; simp [HermLine.zcomb]) (fun z => by simp [HermLine.zcomb])
    | succ p ih =>
      refine smallGen_mul y _ (fsH ι) _ ?_ (fun z => ?_) ih (smallGen_fsH y)
      · funext k
        simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
        ring
  | succ q ih =>
    refine smallGen_mul y _ L _ ?_ (fun z => ?_) ih hL
    · funext k
      simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
      ring

/- English proof (translation)
Introduce `K _ ι _ Ω _ y L p q hL`. Conclude with `smallGen_zcomb y L hL q p`.
-/
theorem proof : SmallGenTwist.Statement := by
  intro K _ ι _ Ω _ y L p q hL
  exact smallGen_zcomb y L hL q p

end SmallGenTwist

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
