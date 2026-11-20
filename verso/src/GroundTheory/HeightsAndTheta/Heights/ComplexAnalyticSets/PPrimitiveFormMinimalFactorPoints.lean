import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormMinimalFactorPoints
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermMinimalPolynomialDivides
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreCentredEquation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormRemainder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace PrimitiveFormMinimalFactorPoints

open Topology Filter Polynomial

def anSub {d : ℕ} (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f y₀}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

/- English proof (translation)
Rewrite `h` using `[← lifts_iff_liftsRing, lifts_iff_coeff_lifts]`. Take `⟨f, hf⟩` from `h k`. Rewrite using `[← hf]`. Conclude with `f.2`.
-/
theorem coeff_analyticAt {d : ℕ} {y₀ : Fin d → ℂ} {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (h : E ∈ liftsRing (anSub y₀).subtype) (k : ℕ) : AnalyticAt ℂ (E.coeff k) y₀ := by
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at h
  obtain ⟨f, hf⟩ := h k
  rw [← hf]
  exact f.2

/- English proof (translation)
Rewrite using `[← lifts_iff_liftsRing]`. Conclude with `C_mem_lifts (anSub y₀).subtype ⟨f, hf⟩`.
-/
theorem C_mem {d : ℕ} {y₀ : Fin d → ℂ} {f : (Fin d → ℂ) → ℂ} (hf : AnalyticAt ℂ f y₀) :
    C f ∈ liftsRing (anSub y₀).subtype := by
  rw [← lifts_iff_liftsRing]
  exact C_mem_lifts (anSub y₀).subtype ⟨f, hf⟩

/- English proof (translation)
Rewrite using `[← lifts_iff_liftsRing]`. Conclude with `X_mem_lifts _`.
-/
theorem X_mem {d : ℕ} (y₀ : Fin d → ℂ) : (X : Polynomial ((Fin d → ℂ) → ℂ)) ∈ liftsRing (anSub y₀).subtype := by
  rw [← lifts_iff_liftsRing]
  exact X_mem_lifts _

/- English proof (translation)
Take `⟨G, hG⟩` from `hd`. Rewrite using `[← eval_map, hG, eval_mul]`. Simplify using `[eval_finsetSum, hτ]`.
-/
theorem eval₂_eq_zero_of_dvd {d n : ℕ} {b : Fin n → (Fin d → ℂ) → ℂ} {y : Fin d → ℂ}
    {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (hd : (X ^ n + ∑ j, C (b j y) * X ^ (j : ℕ) : Polynomial ℂ) ∣ E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y))
    {τ : ℂ} (hτ : τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0) :
    E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) τ = 0 := by
  obtain ⟨G, hG⟩ := hd
  rw [← eval_map, hG, eval_mul]
  simp [eval_finsetSum, hτ]

/- English proof (translation)
Rewrite using `[mul_add, Finset.mul_sum, mul_pow]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← pow_sub_mul_pow D j.2.le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cleared_eq {n : ℕ} (c : Fin n → ℂ) (D x : ℂ) :
    (D * x) ^ n + ∑ j : Fin n, c j * D ^ (n - j) * (D * x) ^ (j : ℕ) =
      D ^ n * (x ^ n + ∑ j : Fin n, c j * x ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, mul_pow]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_sub_mul_pow D j.2.le]
  ring

/- English proof (translation)
The claim follows from `LinearMap.pi_apply_eq_sum_univ (L : (σ → ℂ) →ₗ[ℂ] F) v`.
-/
theorem linear_apply_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ] {F : Type} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (L : (σ → ℂ) →L[ℂ] F) (v : σ → ℂ) :
    L v = ∑ i, v i • L (fun j => if i = j then 1 else 0) :=
  LinearMap.pi_apply_eq_sum_univ (L : (σ → ℂ) →ₗ[ℂ] F) v

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Conclude with `Eventually.of_forall fun y x hx => by simp at hx`. Use `set S : E → ℝ := fun y => ∑ j, ‖b j y‖ with hS`. Use `set B : ℝ := max 1 (S y₀ + 1) with hB`.

Establish `hB1 : 1 ≤ B` using `le_max_left _ _`. Establish `hSt : Tendsto S (𝓝 y₀) (𝓝 (S y₀))` using `tendsto_finsetSum _ fun j _ => (hb j).tendsto.norm`. Establish `hDt : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀) (𝓝 0)`. Establish `: Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀) (𝓝 (∑ j : Fin n, ‖b j y₀ - b j y₀‖ * B ^ (j : ℕ)))` using `tendsto_finsetSum _ fun j _ => ((tendsto_const_nhds.sub (hb j).tendsto).norm).mul_const _`. Simplify using `using this`.

Establish `hεn : (0 : ℝ) < ε ^ n` using `pow_pos hε n`. Use `filter_upwards [hSt.eventually (gt_mem_nhds (lt_add_one (S y₀))), hDt.eventually (gt_mem_nhds hεn)] with y hSy hDy x hx`. Establish `hxB : ‖x‖ ≤ B`. Distinguish the cases in `hx1 : ‖x‖ ≤ 1`. Conclude with `hx1.trans hB1`.

Use `replace hx1 := lt_of_not_ge hx1`. Establish `hxn : x ^ n = -∑ j, b j y * x ^ (j : ℕ)` using `eq_neg_of_add_eq_zero_left hx`. Establish `hle : ‖x‖ ^ n ≤ S y * ‖x‖ ^ (n - 1)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1.le (by omega)) (norm_nonneg _)`. Use `_ = S y * ‖x‖ ^ (n - 1) := by rw [hS, Finset.sum_mul]`. Establish `hpos : 0 < ‖x‖ ^ (n - 1)` using `pow_pos (zero_lt_one.trans hx1) _`. Establish `: ‖x‖ * ‖x‖ ^ (n - 1) ≤ S y * ‖x‖ ^ (n - 1)`.

Rewrite using `[← pow_succ', Nat.sub_add_cancel hn]`. Conclude with `hle`. Establish `hxS : ‖x‖ ≤ S y` using `le_of_mul_le_mul_right this hpos`. Conclude with `hxS.trans (hSy.le.trans (le_max_right _ _))`. Establish `hid : (x - u) ^ n = ∑ j, (b j y₀ - b j y) * x ^ (j : ℕ)`.

Rewrite using `[← h0 x]`. Establish `: x ^ n = -∑ j, b j y * x ^ (j : ℕ)` using `eq_neg_of_add_eq_zero_left hx`. Rewrite using `[this]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hle : ‖x - u‖ ^ n ≤ ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxB _) (norm_nonneg _)`.

Establish `: ‖x - u‖ ^ n < ε ^ n` using `hle.trans_lt hDy`. Conclude with `lt_of_pow_lt_pow_left₀ n hε.le this`.
-/
theorem roots_near_centred {E : Type*} [TopologicalSpace E] {n : ℕ} (b : Fin n → E → ℂ) (y₀ : E) (u : ℂ)
    (hb : ∀ j, ContinuousAt (b j) y₀) (h0 : ∀ T : ℂ, T ^ n + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u) ^ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x : ℂ, x ^ n + ∑ j, b j y * x ^ (j : ℕ) = 0 → ‖x - u‖ < ε := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Eventually.of_forall fun y x hx => by simp at hx
  set S : E → ℝ := fun y => ∑ j, ‖b j y‖ with hS
  set B : ℝ := max 1 (S y₀ + 1) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hSt : Tendsto S (𝓝 y₀) (𝓝 (S y₀)) :=
    tendsto_finsetSum _ fun j _ => (hb j).tendsto.norm
  have hDt : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀) (𝓝 0) := by
    have : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀)
        (𝓝 (∑ j : Fin n, ‖b j y₀ - b j y₀‖ * B ^ (j : ℕ))) :=
      tendsto_finsetSum _ fun j _ => ((tendsto_const_nhds.sub (hb j).tendsto).norm).mul_const _
    simpa using this
  have hεn : (0 : ℝ) < ε ^ n := pow_pos hε n
  filter_upwards [hSt.eventually (gt_mem_nhds (lt_add_one (S y₀))), hDt.eventually (gt_mem_nhds hεn)]
    with y hSy hDy x hx
  have hxB : ‖x‖ ≤ B := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans hB1
    replace hx1 := lt_of_not_ge hx1
    have hxn : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    have hle : ‖x‖ ^ n ≤ S y * ‖x‖ ^ (n - 1) := by
      calc ‖x‖ ^ n = ‖∑ j, b j y * x ^ (j : ℕ)‖ := by rw [← norm_pow, hxn, norm_neg]
        _ ≤ ∑ j, ‖b j y * x ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin n, ‖b j y‖ * ‖x‖ ^ (n - 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1.le (by omega)) (norm_nonneg _)
        _ = S y * ‖x‖ ^ (n - 1) := by rw [hS, Finset.sum_mul]
    have hpos : 0 < ‖x‖ ^ (n - 1) := pow_pos (zero_lt_one.trans hx1) _
    have : ‖x‖ * ‖x‖ ^ (n - 1) ≤ S y * ‖x‖ ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]; exact hle
    have hxS : ‖x‖ ≤ S y := le_of_mul_le_mul_right this hpos
    exact hxS.trans (hSy.le.trans (le_max_right _ _))
  have hid : (x - u) ^ n = ∑ j, (b j y₀ - b j y) * x ^ (j : ℕ) := by
    rw [← h0 x]
    have : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    rw [this]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hle : ‖x - u‖ ^ n ≤ ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
    calc ‖x - u‖ ^ n = ‖∑ j, (b j y₀ - b j y) * x ^ (j : ℕ)‖ := by rw [← norm_pow, hid]
      _ ≤ ∑ j, ‖(b j y₀ - b j y) * x ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxB _) (norm_nonneg _)
  have : ‖x - u‖ ^ n < ε ^ n := hle.trans_lt hDy
  exact lt_of_pow_lt_pow_left₀ n hε.le this

/- English proof (translation)
Introduce `σ _ Y w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδne hp hsep hrel`. Take `⟨n, b, hb, hmX, hdiv⟩` from `hMin σ Y w d A hX hirr hiso hinj ℓ (ℓ.analyticAt w)`. Use `choose nW cW hcW hcW0 hWX using fun i : σ => hCen σ Y w d A hX hiso (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)`. Take `⟨V, K, f, hVo, hwV, hf, hXV⟩` from `hX`. Use `choose M R hR hRz using fun k : Fin K => hRem σ w d A ℓ N δ q nW cW (f k) hδ hq hcW hcW0 (hf k w hwV)`.

Use `set ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun y => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y with hev`. Establish `hevC : ∀ y (g : (Fin d → ℂ) → ℂ), ev y g = g y` using `fun _ _ => rfl`. Use `set e : σ → σ → ℂ := fun i j => if i = j then 1 else 0 with he`. Use `set Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ) with hQdef`. Establish `hQ : ∀ i, Q i ∈ liftsRing (anSub (A w)).subtype` using `fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (hq i j)) (Subring.pow_mem _ (X_mem _) _)`.

Establish `hQe : ∀ i y t, (Q i).eval₂ (ev y) t = ∑ j, q i j y * t ^ (j : ℕ)`. Introduce `i y t`. Simplify using `[hQdef, eval₂_finsetSum, hevC]`. Establish `hproj : ∀ r : Fin d, AnalyticAt ℂ (fun y : Fin d → ℂ => y r) (A w)` using `fun r => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) r).analyticAt _`. Use `set Ep : Polynomial ((Fin d → ℂ) → ℂ) := X ^ N + ∑ j, C (a j) * X ^ (j : ℕ) with hEp`.

Use `set EA : Fin d → Polynomial ((Fin d → ℂ) → ℂ) := fun r => ∑ i, C (fun _ => A (e i) r) * Q i - C (fun y => δ y * y r) with hEA`. Use `set El : Polynomial ((Fin d → ℂ) → ℂ) := ∑ i, C (fun _ => ℓ (e i)) * Q i - C δ * X with hEl`. Use `set EW : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => Q i ^ nW i + ∑ j, C (fun y => cW i j y * δ y ^ (nW i - j)) * Q i ^ (j : ℕ) with hEW`. Establish `hEpc : Ep ∈ liftsRing (anSub (A w)).subtype` using `Subring.add_mem _ (Subring.pow_mem _ (X_mem _) _) (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (ha j)) (Subring.pow_mem _ (X_mem _) _))`. Establish `hEAc : ∀ r, EA r ∈ liftsRing (anSub (A w)).subtype` using `fun r => Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i)) (C_mem (hδ.mul (hproj r)))`.

Establish `hElc : El ∈ liftsRing (anSub (A w)).subtype` using `Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i)) (Subring.mul_mem _ (C_mem hδ) (X_mem _))`. Establish `hEWc : ∀ i, EW i ∈ liftsRing (anSub (A w)).subtype` using `fun i => Subring.add_mem _ (Subring.pow_mem _ (hQ i) _) (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem ((hcW i j).mul (hδ.pow _))) (Subring.pow_mem _ (hQ i) _))`. Establish `hEpe : ∀ y t, Ep.eval₂ (ev y) t = t ^ N + ∑ j, a j y * t ^ (j : ℕ)`. Introduce `y t`. Simplify using `[hEp, eval₂_finsetSum, hevC]`.

Establish `hEAe : ∀ r y t, (EA r).eval₂ (ev y) t = ∑ i, A (e i) r * ∑ j, q i j y * t ^ (j : ℕ) - δ y * y r`. Introduce `r y t`. Simplify using `[hEA, eval₂_finsetSum, hevC, hQe]`. Establish `hEle : ∀ y t, El.eval₂ (ev y) t = ∑ i, ℓ (e i) * ∑ j, q i j y * t ^ (j : ℕ) - δ y * t`. Introduce `y t`.

Simplify using `[hEl, eval₂_finsetSum, hevC, hQe]`. Establish `hEWe : ∀ i y t, (EW i).eval₂ (ev y) t = (∑ j, q i j y * t ^ (j : ℕ)) ^ nW i + ∑ j : Fin (nW i), cW i j y * δ y ^ (nW i - j) * (∑ j, q i j y * t ^ (j : ℕ)) ^ (j : ℕ)`. Introduce `i y t`. Simplify using `[hEW, eval₂_finsetSum, hevC, hQe, eval₂_pow]`. Establish `hAsum : ∀ (v : σ → ℂ) r, A v r = ∑ i, v i * A (e i) r`.

Introduce `v r`. Rewrite using `[linear_apply_eq_sum A v]`. Simplify using `[Finset.sum_apply, he]`. Establish `hlsum : ∀ v : σ → ℂ, ℓ v = ∑ i, v i * ℓ (e i)`. Introduce `v`.

Rewrite using `[linear_apply_eq_sum ℓ v]`. Simplify using `[he]`. Establish `hrelA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)` using `by filter_upwards [eventually_all.2 hrel] with z hz hzX i using hz i hzX`. Establish `hWA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0` using `by filter_upwards [eventually_all.2 hWX] with z hz hzX i using hz i hzX`. Establish `dEp` using `hdiv Ep (coeff_analyticAt hEpc) (by filter_upwards [hp] with z hz hzX; rw [hEpe]; exact hz hzX)`.

Establish `dEA` using `fun r => hdiv (EA r) (coeff_analyticAt (hEAc r)) (by filter_upwards [hrelA] with z hz hzX`. Rewrite using `[hEAe, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i], hAsum z r, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_eq_zero fun i _ => by ring)`. Establish `dEl` using `hdiv El (coeff_analyticAt hElc) (by filter_upwards [hrelA] with z hz hzX`. Rewrite using `[hEle, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i]]`.

Rewrite using `[hlsum z, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_eq_zero fun i _ => by ring)`. Establish `dEW` using `fun i => hdiv (EW i) (coeff_analyticAt (hEWc i)) (by filter_upwards [hrelA, hWA] with z hz hzW hzX`. Rewrite using `[hEWe, ← hz hzX i, cleared_eq, hzW hzX i, mul_zero])`. Establish `dR` using `fun k => hdiv (R k) (hR k) (by filter_upwards [hRz k, hrelA, hWA, hVo.mem_nhds hwV] with z h1 hz hzW hzV hzX`.

Establish `hz0 : z ∈ {z | z ∈ V ∧ ∀ i, f i z = 0}` using `by rw [← hXV]; exact ⟨hzX, hzV⟩`. Rewrite using `[← h1 (hzW hzX) (hz hzX), hz0.2 k, mul_zero])`. Use `⟨n, b, hb, hmX, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hsep, dEp] with y hs hd hδy`. Use `(hs hδy).of_dvd ?_` and prove the remaining obligations.

Simplify `hd` using `[hEp, Polynomial.map_add, Polynomial.map_sum, hevC]`. Introduce `U hU`. Establish `hO : ∀ᶠ z in 𝓝 w, z ∈ U ∧ z ∈ V ∧ ∀ k, (∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0) → (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) → δ (A z) ^ M k * f k z = (R k).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z)` using `by filter_upwards [hU, hVo.mem_nhds hwV, eventually_all.2 hRz] with z h1 h2 h3 using ⟨h1, h2, h3⟩`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff.1 hO`. Establish `hnear` using `fun i => roots_near_centred (cW i) (A w) (w i) (fun j => (hcW i j).continuousAt) (hcW0 i) hε`.

Use `filter_upwards [eventually_all.2 hnear, eventually_all.2 dEA, dEl, eventually_all.2 dEW, eventually_all.2 dR] with y hny hAy hly hWy hRy hδy τ hτ`. Use `set φ : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hφ`. Establish `hQφ : ∀ i, ∑ j, q i j y * τ ^ (j : ℕ) = δ y * φ i` using `fun i => by`. Rewrite using `[hφ]`. Clear the denominators using the available nonvanishing facts.

Establish `hAφ : A φ = y`. Use function extensionality and compare the values at `r`. Establish `h0` using `eval₂_eq_zero_of_dvd (hAy r) hτ`. Rewrite `h0` using `[hEAe, sub_eq_zero]`. Rewrite using `[hAsum φ r]`.

Apply `mul_left_cancel₀ hδy` to reduce the goal to its premises. Rewrite using `[← h0, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring`. Establish `hlφ : ℓ φ = τ`. Establish `h0` using `eval₂_eq_zero_of_dvd hly hτ`.

Rewrite `h0` using `[hEle, sub_eq_zero]`. Rewrite using `[hlsum φ]`. Apply `mul_left_cancel₀ hδy` to reduce the goal to its premises. Rewrite using `[← h0, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring`.

Establish `hWφ : ∀ i, φ i ^ nW i + ∑ j, cW i j y * φ i ^ (j : ℕ) = 0`. Introduce `i`. Establish `h0` using `eval₂_eq_zero_of_dvd (hWy i) hτ`. Rewrite `h0` using `[hEWe, hQφ i, cleared_eq]`. Conclude with `(mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδy)`.

Establish `hdist : dist φ w < ε`. Rewrite using `[dist_pi_lt_iff hε]`. Introduce `i`. Rewrite using `[dist_eq_norm]`. Conclude with `hny i (φ i) (hWφ i)`.

Take `⟨hφU, hφV, hφR⟩` from `hball hdist`. Establish `hfk : ∀ k, f k φ = 0`. Introduce `k`. Establish `h1` using `hφR k (by rw [hAφ]; exact hWφ) (by intro i; rw [hAφ, hlφ, hQφ i])`. Rewrite `h1` using `[hAφ, hlφ, eval₂_eq_zero_of_dvd (hRy k) hτ]`.

Conclude with `(mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hδy)`. Establish `hφX : φ ∈ Y ∩ V` using `by rw [hXV]; exact ⟨hφV, hfk⟩`. Conclude with `⟨⟨hφX.1, hφU⟩, hAφ, hlφ⟩`.
-/
theorem proof (hMin : GermMinimalPolynomialDivides.Statement) (hCen : FiniteFibreCentredEquation.Statement)
    (hRem : PrimitiveFormRemainder.Statement) : PrimitiveFormMinimalFactorPoints.Statement := by
  classical
  intro σ _ Y w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδne hp hsep hrel
  obtain ⟨n, b, hb, hmX, hdiv⟩ := hMin σ Y w d A hX hirr hiso hinj ℓ (ℓ.analyticAt w)
  choose nW cW hcW hcW0 hWX using fun i : σ =>
    hCen σ Y w d A hX hiso (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  obtain ⟨V, K, f, hVo, hwV, hf, hXV⟩ := hX
  choose M R hR hRz using fun k : Fin K => hRem σ w d A ℓ N δ q nW cW (f k) hδ hq hcW hcW0 (hf k w hwV)
  set ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun y => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y with hev
  have hevC : ∀ y (g : (Fin d → ℂ) → ℂ), ev y g = g y := fun _ _ => rfl
  set e : σ → σ → ℂ := fun i j => if i = j then 1 else 0 with he

  set Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ) with hQdef
  have hQ : ∀ i, Q i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (hq i j)) (Subring.pow_mem _ (X_mem _) _)
  have hQe : ∀ i y t, (Q i).eval₂ (ev y) t = ∑ j, q i j y * t ^ (j : ℕ) := by
    intro i y t; simp [hQdef, eval₂_finsetSum, hevC]
  have hproj : ∀ r : Fin d, AnalyticAt ℂ (fun y : Fin d → ℂ => y r) (A w) := fun r =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) r).analyticAt _
  set Ep : Polynomial ((Fin d → ℂ) → ℂ) := X ^ N + ∑ j, C (a j) * X ^ (j : ℕ) with hEp
  set EA : Fin d → Polynomial ((Fin d → ℂ) → ℂ) := fun r =>
    ∑ i, C (fun _ => A (e i) r) * Q i - C (fun y => δ y * y r) with hEA
  set El : Polynomial ((Fin d → ℂ) → ℂ) := ∑ i, C (fun _ => ℓ (e i)) * Q i - C δ * X with hEl
  set EW : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i =>
    Q i ^ nW i + ∑ j, C (fun y => cW i j y * δ y ^ (nW i - j)) * Q i ^ (j : ℕ) with hEW
  have hEpc : Ep ∈ liftsRing (anSub (A w)).subtype :=
    Subring.add_mem _ (Subring.pow_mem _ (X_mem _) _)
      (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (ha j)) (Subring.pow_mem _ (X_mem _) _))
  have hEAc : ∀ r, EA r ∈ liftsRing (anSub (A w)).subtype := fun r =>
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (C_mem (hδ.mul (hproj r)))
  have hElc : El ∈ liftsRing (anSub (A w)).subtype :=
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (Subring.mul_mem _ (C_mem hδ) (X_mem _))
  have hEWc : ∀ i, EW i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.add_mem _ (Subring.pow_mem _ (hQ i) _) (Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ (C_mem ((hcW i j).mul (hδ.pow _))) (Subring.pow_mem _ (hQ i) _))

  have hEpe : ∀ y t, Ep.eval₂ (ev y) t = t ^ N + ∑ j, a j y * t ^ (j : ℕ) := by
    intro y t; simp [hEp, eval₂_finsetSum, hevC]
  have hEAe : ∀ r y t, (EA r).eval₂ (ev y) t = ∑ i, A (e i) r * ∑ j, q i j y * t ^ (j : ℕ) - δ y * y r := by
    intro r y t; simp [hEA, eval₂_finsetSum, hevC, hQe]
  have hEle : ∀ y t, El.eval₂ (ev y) t = ∑ i, ℓ (e i) * ∑ j, q i j y * t ^ (j : ℕ) - δ y * t := by
    intro y t; simp [hEl, eval₂_finsetSum, hevC, hQe]
  have hEWe : ∀ i y t, (EW i).eval₂ (ev y) t = (∑ j, q i j y * t ^ (j : ℕ)) ^ nW i +
      ∑ j : Fin (nW i), cW i j y * δ y ^ (nW i - j) * (∑ j, q i j y * t ^ (j : ℕ)) ^ (j : ℕ) := by
    intro i y t; simp [hEW, eval₂_finsetSum, hevC, hQe, eval₂_pow]
  have hAsum : ∀ (v : σ → ℂ) r, A v r = ∑ i, v i * A (e i) r := by
    intro v r; rw [linear_apply_eq_sum A v]; simp [Finset.sum_apply, he]
  have hlsum : ∀ v : σ → ℂ, ℓ v = ∑ i, v i * ℓ (e i) := by
    intro v; rw [linear_apply_eq_sum ℓ v]; simp [he]

  have hrelA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ) := by
    filter_upwards [eventually_all.2 hrel] with z hz hzX i using hz i hzX
  have hWA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0 := by
    filter_upwards [eventually_all.2 hWX] with z hz hzX i using hz i hzX
  have dEp := hdiv Ep (coeff_analyticAt hEpc) (by
    filter_upwards [hp] with z hz hzX; rw [hEpe]; exact hz hzX)
  have dEA := fun r => hdiv (EA r) (coeff_analyticAt (hEAc r)) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEAe, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i], hAsum z r, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEl := hdiv El (coeff_analyticAt hElc) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEle, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i]]
    rw [hlsum z, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEW := fun i => hdiv (EW i) (coeff_analyticAt (hEWc i)) (by
    filter_upwards [hrelA, hWA] with z hz hzW hzX
    rw [hEWe, ← hz hzX i, cleared_eq, hzW hzX i, mul_zero])
  have dR := fun k => hdiv (R k) (hR k) (by
    filter_upwards [hRz k, hrelA, hWA, hVo.mem_nhds hwV] with z h1 hz hzW hzV hzX
    have hz0 : z ∈ {z | z ∈ V ∧ ∀ i, f i z = 0} := by rw [← hXV]; exact ⟨hzX, hzV⟩
    rw [← h1 (hzW hzX) (hz hzX), hz0.2 k, mul_zero])
  refine ⟨n, b, hb, hmX, ?_, ?_⟩
  · filter_upwards [hsep, dEp] with y hs hd hδy
    refine (hs hδy).of_dvd ?_
    simpa [hEp, Polynomial.map_add, Polynomial.map_sum, hevC] using hd
  intro U hU
  have hO : ∀ᶠ z in 𝓝 w, z ∈ U ∧ z ∈ V ∧ ∀ k, (∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0) →
      (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      δ (A z) ^ M k * f k z = (R k).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) :=
    by filter_upwards [hU, hVo.mem_nhds hwV, eventually_all.2 hRz] with z h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hO
  have hnear := fun i => roots_near_centred (cW i) (A w) (w i) (fun j => (hcW i j).continuousAt) (hcW0 i) hε
  filter_upwards [eventually_all.2 hnear, eventually_all.2 dEA, dEl, eventually_all.2 dEW,
    eventually_all.2 dR] with y hny hAy hly hWy hRy hδy τ hτ
  set φ : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hφ
  have hQφ : ∀ i, ∑ j, q i j y * τ ^ (j : ℕ) = δ y * φ i := fun i => by
    rw [hφ]; field_simp
  have hAφ : A φ = y := by
    funext r
    have h0 := eval₂_eq_zero_of_dvd (hAy r) hτ
    rw [hEAe, sub_eq_zero] at h0
    rw [hAsum φ r]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hlφ : ℓ φ = τ := by
    have h0 := eval₂_eq_zero_of_dvd hly hτ
    rw [hEle, sub_eq_zero] at h0
    rw [hlsum φ]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hWφ : ∀ i, φ i ^ nW i + ∑ j, cW i j y * φ i ^ (j : ℕ) = 0 := by
    intro i
    have h0 := eval₂_eq_zero_of_dvd (hWy i) hτ
    rw [hEWe, hQφ i, cleared_eq] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδy)
  have hdist : dist φ w < ε := by
    rw [dist_pi_lt_iff hε]
    intro i
    rw [dist_eq_norm]
    exact hny i (φ i) (hWφ i)
  obtain ⟨hφU, hφV, hφR⟩ := hball hdist
  have hfk : ∀ k, f k φ = 0 := by
    intro k
    have h1 := hφR k (by rw [hAφ]; exact hWφ) (by intro i; rw [hAφ, hlφ, hQφ i])
    rw [hAφ, hlφ, eval₂_eq_zero_of_dvd (hRy k) hτ] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hδy)
  have hφX : φ ∈ Y ∩ V := by rw [hXV]; exact ⟨hφV, hfk⟩
  exact ⟨⟨hφX.1, hφU⟩, hAφ, hlφ⟩

end PrimitiveFormMinimalFactorPoints

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
