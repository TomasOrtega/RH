import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds

noncomputable section

namespace GlobalTheory.LiftPole

open scoped Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_re`.
-/
theorem isOpen_re_gt (σ : ℝ) : IsOpen {s : ℂ | σ < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/- English proof (translation)
Establish `hM : MeromorphicAt (fun s => (s - s₀)⁻¹ * G s) s₀` using `((analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s - s₀) s₀).meromorphicAt.inv).mul hG.meromorphicAt`. Establish `hΛ : MeromorphicAt Λ s₀` using `hM.congr (h.mono fun s hs => hs.symm)`. Use `⟨hΛ, ?_, G s₀, h0, ?_⟩` and prove the remaining obligations. Rewrite using `[meromorphicOrderAt_eq_int_iff hΛ]`. Use `⟨G, hG, h0, h.mono fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[hs, zpow_neg_one, smul_eq_mul]`. Establish `hc : Tendsto G (𝓝[≠] s₀) (𝓝 (G s₀))` using `hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds`. Use `hc.congr' ?_` and prove the remaining obligations. Use `filter_upwards [h, self_mem_nhdsWithin] with s hs hne`. Rewrite using `[hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]`.
-/
theorem hasSimplePole_of {Λ G : ℂ → ℂ} {s₀ : ℂ} (hG : AnalyticAt ℂ G s₀) (h0 : G s₀ ≠ 0)
    (h : ∀ᶠ s in 𝓝[≠] s₀, Λ s = (s - s₀)⁻¹ * G s) : HasSimplePole Λ s₀ := by
  have hM : MeromorphicAt (fun s => (s - s₀)⁻¹ * G s) s₀ :=
    ((analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s - s₀) s₀).meromorphicAt.inv).mul
      hG.meromorphicAt
  have hΛ : MeromorphicAt Λ s₀ := hM.congr (h.mono fun s hs => hs.symm)
  refine ⟨hΛ, ?_, G s₀, h0, ?_⟩
  · rw [meromorphicOrderAt_eq_int_iff hΛ]
    refine ⟨G, hG, h0, h.mono fun s hs => ?_⟩
    rw [hs, zpow_neg_one, smul_eq_mul]
  · have hc : Tendsto G (𝓝[≠] s₀) (𝓝 (G s₀)) := hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [h, self_mem_nhdsWithin] with s hs hne
    rw [hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]

section ZetaNonvanishing₂

variable {K : Type} [Field K] [NumberField K] {T : Set (HeightOneSpectrum (𝓞 K))}

/- English proof (translation)
Use `⟨fun x _ => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Conclude with `((analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s - 1) x).meromorphicAt.inv).mul (hY.analyticAt x).meromorphicAt`. Establish `hne : s - 1 ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Complex.re h0`.

Simplify using `only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [h s hs, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]`.
-/
theorem isZetaCont_of_entire {Y : ℂ → ℂ} (hY : Differentiable ℂ Y)
    (h : ∀ s : ℂ, 1 < s.re → Y s = (s - 1) * zetaOff T s) : IsZetaCont T fun s => (s - 1)⁻¹ * Y s := by
  refine ⟨fun x _ => ?_, fun s hs => ?_⟩
  · exact ((analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s - 1) x).meromorphicAt.inv).mul
      (hY.analyticAt x).meromorphicAt
  · have hne : s - 1 ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h1
      linarith
    simp only [h s hs, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/- English proof (translation)
Establish `hM : MeromorphicOn (Z - Z') Set.univ` using `fun y _ => (h.1 y trivial).sub (h'.1 y trivial)`. Establish `h2 : meromorphicOrderAt (Z - Z') 2 = ⊤`. Rewrite using `[meromorphicOrderAt_eq_top_iff]`. Establish `hU : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ)` using `(isOpen_re_gt 1).mem_nhds (by norm_num [Set.mem_ofPred_eq])`. Use `filter_upwards [nhdsWithin_le_nhds hU] with s hs`.

Simplify using `[h.2 s hs, h'.2 s hs]`. Establish `hx : meromorphicOrderAt (Z - Z') x = ⊤`. Assume the negation of the conclusion as `hne`. Conclude with `hM.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hne h2`. Rewrite `hx` using `[meromorphicOrderAt_eq_top_iff]`.

Use `filter_upwards [hx] with s hs`. Simplify using `only [Pi.sub_apply, sub_eq_zero] at hs`. Conclude with `hs`.
-/
theorem eventuallyEq_of_isZetaCont {Z Z' : ℂ → ℂ} (h : IsZetaCont T Z) (h' : IsZetaCont T Z') (x : ℂ) :
    ∀ᶠ s in 𝓝[≠] x, Z s = Z' s := by
  have hM : MeromorphicOn (Z - Z') Set.univ := fun y _ => (h.1 y trivial).sub (h'.1 y trivial)
  have h2 : meromorphicOrderAt (Z - Z') 2 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hU : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := (isOpen_re_gt 1).mem_nhds (by norm_num [Set.mem_ofPred_eq])
    filter_upwards [nhdsWithin_le_nhds hU] with s hs
    simp [h.2 s hs, h'.2 s hs]
  have hx : meromorphicOrderAt (Z - Z') x = ⊤ := by
    by_contra hne
    exact hM.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hne h2
  rw [meromorphicOrderAt_eq_top_iff] at hx
  filter_upwards [hx] with s hs
  simp only [Pi.sub_apply, sub_eq_zero] at hs
  exact hs

/- English proof (translation)
Introduce `w _`. Use `⟨by simp, fun b hb => ?_⟩` and prove the remaining obligations. Simplify using `only [Multiset.mem_singleton] at hb`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules.
-/
theorem bounded_one : Bounded T (fun _ => {1}) 1 0 := by
  intro w _
  refine ⟨by simp, fun b hb => ?_⟩
  simp only [Multiset.mem_singleton] at hb
  subst hb
  simp

/- English proof (translation)
Establish `hd : DifferentiableOn ℂ (zetaOff T) {s : ℂ | (0 : ℝ) + 1 < s.re}` using `(bounded_one (T := T)).differentiableOn`. Establish `hU : {s : ℂ | (0 : ℝ) + 1 < s.re} ∈ 𝓝 s` using `(isOpen_re_gt _).mem_nhds (by simpa using hs)`. Conclude with `hd.analyticAt hU`.
-/
theorem analyticAt_zetaOff {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (zetaOff T) s := by
  have hd : DifferentiableOn ℂ (zetaOff T) {s : ℂ | (0 : ℝ) + 1 < s.re} := (bounded_one (T := T)).differentiableOn
  have hU : {s : ℂ | (0 : ℝ) + 1 < s.re} ∈ 𝓝 s := (isOpen_re_gt _).mem_nhds (by simpa using hs)
  exact hd.analyticAt hU

/- English proof (translation)
Introduce `w _`. Establish `hN : (1 : ℝ) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)` using `by exact_mod_cast (one_lt_absNorm w).le`. Use `⟨by simp [segFam], fun b hb => ?_⟩` and prove the remaining obligations. Simplify using `only [segFam, seg, Multiset.mem_map, Finset.mem_val, Finset.mem_range] at hb`. Take `⟨i, _, rfl⟩` from `hb`.

Establish `hre : (((t : ℂ) - 1) / 2 - (i : ℂ)).re = ((t : ℝ) - 1) / 2 - i`. Rewrite using `[show ((t : ℂ) - 1) / 2 - (i : ℂ) = ((((t : ℝ) - 1) / 2 - i : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]`. Simplify using `only [Pi.one_apply, one_mul, coe_npowU, norm_npow, hre]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hN (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])`.
-/
theorem bounded_segFam (t : ℕ) : Bounded T (segFam 1 t) t (((t : ℝ) - 1) / 2) := by
  intro w _
  have hN : (1 : ℝ) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast (one_lt_absNorm w).le
  refine ⟨by simp [segFam], fun b hb => ?_⟩
  simp only [segFam, seg, Multiset.mem_map, Finset.mem_val, Finset.mem_range] at hb
  obtain ⟨i, _, rfl⟩ := hb
  have hre : (((t : ℂ) - 1) / 2 - (i : ℂ)).re = ((t : ℝ) - 1) / 2 - i := by
    rw [show ((t : ℂ) - 1) / 2 - (i : ℂ) = ((((t : ℝ) - 1) / 2 - i : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  simp only [Pi.one_apply, one_mul, coe_npowU, norm_npow, hre]
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])

/- English proof (translation)
Introduce `w hw` and use `⟨(h w hw).1, fun b hb => ((h w hw).2 b hb).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (one_lt_absNorm w).le) hκ)⟩`.
-/
theorem Bounded.mono {c : Fam K} {r : ℕ} {κ κ' : ℝ} (h : Bounded T c r κ) (hκ : κ ≤ κ') : Bounded T c r κ' :=
  fun w hw => ⟨(h w hw).1, fun b hb => ((h w hw).2 b hb).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (one_lt_absNorm w).le) hκ)⟩

/- English proof (translation)
Establish `hre : (s + ((t : ℂ) - 1) / 2 - i).re = s.re + (((t : ℝ) - 1) / 2 - i)`. Rewrite using `[show s + ((t : ℂ) - 1) / 2 - i = s + ((((t : ℝ) - 1) / 2 - i : ℝ) : ℂ) by push_cast; ring, Complex.add_re, Complex.ofReal_re]`. Establish `hit : (i : ℝ) + 1 ≤ t` using `by exact_mod_cast hi`. Rewrite using `[hre]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_lt_re_shift {t i : ℕ} (hi : i < t) {s : ℂ} (hs : ((t : ℝ) + 1) / 2 < s.re) :
    1 < (s + ((t : ℂ) - 1) / 2 - i).re := by
  have hre : (s + ((t : ℂ) - 1) / 2 - i).re = s.re + (((t : ℝ) - 1) / 2 - i) := by
    rw [show s + ((t : ℂ) - 1) / 2 - i = s + ((((t : ℝ) - 1) / 2 - i : ℝ) : ℂ) by push_cast; ring,
      Complex.add_re, Complex.ofReal_re]
  have hit : (i : ℝ) + 1 ≤ t := by exact_mod_cast hi
  rw [hre]
  linarith

/- English proof (translation)
Establish `hp : HasProd (fun w : {w // w ∉ T} => ∏ i ∈ Finset.range t, locL (fun _ => {1}) w.1 (s + ((t : ℂ) - 1) / 2 - i)) (∏ i ∈ Finset.range t, zetaOff T (s + ((t : ℂ) - 1) / 2 - i))` using `hasProd_prod fun i hi => (converges_zeta T (one_lt_re_shift (Finset.mem_range.mp hi) hs)).hasProd`. Establish `he : (fun w : {w // w ∉ T} => locL (segFam 1 t) w.1 s) = fun w => ∏ i ∈ Finset.range t, locL (fun _ => {1}) w.1 (s + ((t : ℂ) - 1) / 2 - i)`. Use function extensionality and compare the values at `w`. Rewrite using `[locL_segFam']`. Both sides reduce to the same expression.

Rewrite using `[show eulerProd T (segFam 1 t) s = ∏' w : {w // w ∉ T}, locL (segFam 1 t) w.1 s from rfl, he]`. Conclude with `hp.tprod_eq`.
-/
theorem eulerProd_segFam {t : ℕ} {s : ℂ} (hs : ((t : ℝ) + 1) / 2 < s.re) :
    eulerProd T (segFam 1 t) s = ∏ i ∈ Finset.range t, zetaOff T (s + ((t : ℂ) - 1) / 2 - i) := by
  have hp : HasProd (fun w : {w // w ∉ T} =>
      ∏ i ∈ Finset.range t, locL (fun _ => {1}) w.1 (s + ((t : ℂ) - 1) / 2 - i))
      (∏ i ∈ Finset.range t, zetaOff T (s + ((t : ℂ) - 1) / 2 - i)) :=
    hasProd_prod fun i hi => (converges_zeta T (one_lt_re_shift (Finset.mem_range.mp hi) hs)).hasProd
  have he : (fun w : {w // w ∉ T} => locL (segFam 1 t) w.1 s) =
      fun w => ∏ i ∈ Finset.range t, locL (fun _ => {1}) w.1 (s + ((t : ℂ) - 1) / 2 - i) := by
    funext w
    rw [locL_segFam']
    rfl
  rw [show eulerProd T (segFam 1 t) s = ∏' w : {w // w ∉ T}, locL (segFam 1 t) w.1 s from rfl, he]
  exact hp.tprod_eq

end ZetaNonvanishing₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `he : above E S = ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v}`. Use extensionality with `w`. Simplify using `[above]`. Rewrite using `[he]`. Conclude with `hS.biUnion fun v _ => Formalism.L2.Host.finite_aboveF (L := E) F v`.
-/
theorem finite_above {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) : (above E S).Finite := by
  have he : above E S = ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
    ext w
    simp [above]
  rw [he]
  exact hS.biUnion fun v _ => Formalism.L2.Host.finite_aboveF (L := E) F v

/- English proof (translation)
Introduce `F E _ _ _ _ _ S r t c P m x hyp`. Take `⟨hS, hrt, hw⟩` from `hyp`. Establish `hm1 : ∀ w ∉ above E S, ‖((m⁻¹ w : ℂˣ) : ℂ)‖ = 1` using `fun w hw' => by`. Simplify using `[(hw w hw').2.2.1]`. Establish `hbc : Bounded (above E S) (twist c m⁻¹) r (((r : ℝ) - 1) / 2)` using `Bounded.twist (fun w hw' => ⟨(hw w hw').1.le, (hw w hw').2.1⟩) hm1`.

Establish `hrt' : (r : ℝ) + 5 ≤ t` using `by exact_mod_cast hrt`. Establish `hbs : Bounded (above E S) (segFam 1 t) t (((t : ℝ) - 1) / 2)` using `bounded_segFam t`. Establish `hbc' : Bounded (above E S) (twist c m⁻¹) r (((t : ℝ) - 1) / 2)` using `Bounded.mono hbc (by linarith)`. Establish `hbsum` using `hbc'.add hbs`. Establish `htw : ∀ w ∉ above E S, twist P x⁻¹ w = (twist c m⁻¹ + segFam 1 t : Fam E) w` using `fun w hw' => by`.

Rewrite using `[← congrFun (twist_liftFam c m x t) w]`. Simplify using `only [twist, (hw w hw').2.2.2.2]`. Establish `hA : ∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist P x⁻¹) s ∧ (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧ LSTw S P x s = rhs S c m t (zetaOff (above E S)) s`. Introduce `s hs`. Establish `hs' : ((t : ℝ) - 1) / 2 + 1 < s.re` using `by linarith`.

Establish `hcs : Converges (above E S) (twist c m⁻¹ + segFam 1 t) s` using `hbsum.converges hs'`. Use `⟨hcs.congr fun w hw' => (htw w hw').symm, fun i hi => converges_zeta _ (one_lt_re_shift hi hs), ?_⟩` and prove the remaining obligations. Establish `hc1 : Converges (above E S) (twist c m⁻¹) s` using `hbc'.converges hs'`. Establish `hc2 : Converges (above E S) (segFam 1 t) s` using `hbs.converges hs'`. Use `show eulerProd (above E S) (twist P x⁻¹) s = eulerProd (above E S) (twist c m⁻¹) s * ∏ i ∈ Finset.range t, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)`.

Rewrite using `[eulerProd_congr htw, eulerProd_add hc1 hc2, eulerProd_segFam hs]`. Establish `hr : ((r : ℝ) - 1) / 2 + 1 = ((r : ℝ) + 1) / 2` using `by ring`. Establish `hB : (∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧ DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}`. Use `⟨fun s hs => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Converges (above E S) (twist c m⁻¹) s` using `hbc.converges (by rw [hr]; exact hs)`.

Conclude with `⟨h1, h1.ne_zero⟩`. Establish `h1` using `hbc.differentiableOn`. Rewrite `h1` using `[hr]`. Conclude with `h1`. Take `⟨Z0, hZ0d, hZ0eq, hZ0ne⟩` from `(hH E (above E S) (finite_above hS)).2`.

Use `⟨hA, hB, ⟨_, isZetaCont_of_entire hZ0d hZ0eq⟩, fun Z hZ => ?_⟩` and prove the remaining obligations. Establish `hZeq : ∀ u : ℂ, 1 < u.re → Z u = zetaOff (above E S) u` using `hZ.2`. Establish `hs₀re : ((1 + (t : ℂ)) / 2).re = (1 + (t : ℝ)) / 2`. Rewrite using `[show (1 + (t : ℂ)) / 2 = (((1 + (t : ℝ)) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]`. Use `⟨fun s hs => ?_, by rw [hs₀re]; linarith, fun s hs => ?_, ?_⟩` and prove the remaining obligations.

Establish `hU : {s : ℂ | ((r : ℝ) + 1) / 2 < s.re} ∈ 𝓝 s` using `(isOpen_re_gt _).mem_nhds hs`. Establish `h1 : MeromorphicAt (LSTw S c m) s` using `(hB.2.analyticAt hU).meromorphicAt`. Establish `h2 : MeromorphicAt (fun s => ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)) s`. Use `MeromorphicAt.fun_prod fun i _ => ?_` and prove the remaining obligations. Establish `hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) s` using `by fun_prop`.

Conclude with `(hZ.1 _ trivial).comp_analyticAt hg`. Conclude with `h1.mul h2`. Rewrite using `[(hA s hs).2.2] show LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i) = LSTw S c m s * ∏ i ∈ Finset.range t, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun i hi => hZeq _ (one_lt_re_shift (Finset.mem_range.mp hi) hs)`.

Establish `hcast : ((t - 1 : ℕ) : ℂ) = (t : ℂ) - 1`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]`. Establish `hid : ∀ u : ℂ, u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ) - 1 = u - (1 + (t : ℂ)) / 2`. Introduce `u`. Rewrite using `[hcast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsh0 : (1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ) = 1`. Rewrite using `[hcast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre0 : ∀ i : ℕ, ((1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i).re = (t : ℝ) - i`.

Introduce `i`. Rewrite using `[show (1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i = (((t : ℝ) - i : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]`. Establish `hlt : ∀ i ∈ Finset.range t \ {t - 1}, 1 < ((1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i).re`. Introduce `i hi`. Rewrite using `[hre0]`.

Simplify using `only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi`. Take `⟨hi1, hi2⟩` from `hi`. Establish `h2 : (i : ℝ) + 2 ≤ t` using `by exact_mod_cast (by omega : i + 2 ≤ t)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem : t - 1 ∈ Finset.range t` using `Finset.mem_range.mpr (by omega)`.

Establish `hE1 : ∀ᶠ s in 𝓝 ((1 + (t : ℂ)) / 2), ∀ i ∈ Finset.range t \ {t - 1}, Z (s + ((t : ℂ) - 1) / 2 - i) = zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)`. Rewrite using `[Filter.eventually_all_finset]`. Introduce `i hi`. Establish `hc : Continuous (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i)` using `by fun_prop`. Use `filter_upwards [(hc.tendsto _).eventually ((isOpen_re_gt 1).mem_nhds (hlt i hi))] with u hu`.

Conclude with `hZeq _ hu`. Establish `hZZ0` using `eventuallyEq_of_isZetaCont hZ (isZetaCont_of_entire hZ0d hZ0eq) 1`. Establish `hc' : Continuous (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))` using `by fun_prop`. Establish `htend : Tendsto (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ)) (𝓝[≠] ((1 + (t : ℂ)) / 2)) (𝓝[≠] 1)`. Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_` and prove the remaining obligations.

Establish `h1` using `hc'.tendsto ((1 + (t : ℂ)) / 2)`. Rewrite `h1` using `[hsh0]`. Conclude with `h1.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with u hu`. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu ⊢`.

Introduce `heq`. Apply `hu` to reduce the goal to its premises. Establish `h1` using `hid u`. Rewrite `h1` using `[heq, sub_self]`. Conclude with `sub_eq_zero.mp h1.symm`.

Establish `hE2` using `htend.eventually hZZ0`. Establish `hU : {s : ℂ | ((r : ℝ) + 1) / 2 < s.re} ∈ 𝓝 ((1 + (t : ℂ)) / 2)` using `(isOpen_re_gt _).mem_nhds (by simp only [Set.mem_ofPred_eq]; rw [hs₀re]; linarith)`. Establish `hA0 : AnalyticAt ℂ (LSTw S c m) ((1 + (t : ℂ)) / 2)` using `hB.2.analyticAt hU`. Establish `hQ : AnalyticAt ℂ (fun s => ∏ i ∈ Finset.range t \ {t - 1}, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)) ((1 + (t : ℂ)) / 2)`. Use `Finset.analyticAt_fun_prod _ fun i hi => ?_` and prove the remaining obligations.

Establish `hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) ((1 + (t : ℂ)) / 2)` using `by fun_prop`. Conclude with `AnalyticAt.comp (f := fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) (analyticAt_zetaOff (K := E) (T := above E S) (hlt i hi)) hg`. Establish `hZt : AnalyticAt ℂ (fun s => Z0 (s + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))) ((1 + (t : ℂ)) / 2)`. Establish `hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ)) ((1 + (t : ℂ)) / 2)` using `by fun_prop`. Conclude with `(hZ0d.analyticAt _).comp hg`.

Establish `hGan : AnalyticAt ℂ (fun s => LSTw S c m s * (∏ i ∈ Finset.range t \ {t - 1}, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)) * Z0 (s + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))) ((1 + (t : ℂ)) / 2)` using `(hA0.fun_mul hQ).fun_mul hZt`. Use `hasSimplePole_of (Λ := rhs S c m t Z) (s₀ := (1 + (t : ℂ)) / 2) hGan ?_ ?_` and prove the remaining obligations. Use `mul_ne_zero (mul_ne_zero ?_ ?_) ?_` and prove the remaining obligations. Conclude with `(hB.1 _ (by rw [hs₀re]; linarith)).2`. Conclude with `Finset.prod_ne_zero_iff.mpr fun i hi => (converges_zeta _ (hlt i hi)).ne_zero`.

Rewrite using `[hsh0]`. Conclude with `hZ0ne 1 (by simp)`. Use `filter_upwards [nhdsWithin_le_nhds hE1, hE2] with s hs1 hs2`. Unfold `rhs`. Rewrite using `[Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem, hs2, Finset.prod_congr rfl hs1, hid s]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : SimplePole := by
  intro F E _ _ _ _ _ S r t c P m x hyp
  obtain ⟨hS, hrt, hw⟩ := hyp
  have hm1 : ∀ w ∉ above E S, ‖((m⁻¹ w : ℂˣ) : ℂ)‖ = 1 := fun w hw' => by
    simp [(hw w hw').2.2.1]
  have hbc : Bounded (above E S) (twist c m⁻¹) r (((r : ℝ) - 1) / 2) :=
    Bounded.twist (fun w hw' => ⟨(hw w hw').1.le, (hw w hw').2.1⟩) hm1
  have hrt' : (r : ℝ) + 5 ≤ t := by exact_mod_cast hrt
  have hbs : Bounded (above E S) (segFam 1 t) t (((t : ℝ) - 1) / 2) := bounded_segFam t
  have hbc' : Bounded (above E S) (twist c m⁻¹) r (((t : ℝ) - 1) / 2) := Bounded.mono hbc (by linarith)
  have hbsum := hbc'.add hbs
  have htw : ∀ w ∉ above E S, twist P x⁻¹ w = (twist c m⁻¹ + segFam 1 t : Fam E) w := fun w hw' => by
    rw [← congrFun (twist_liftFam c m x t) w]
    simp only [twist, (hw w hw').2.2.2.2]
  have hA : ∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
      Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s := by
    intro s hs
    have hs' : ((t : ℝ) - 1) / 2 + 1 < s.re := by linarith
    have hcs : Converges (above E S) (twist c m⁻¹ + segFam 1 t) s := hbsum.converges hs'
    refine ⟨hcs.congr fun w hw' => (htw w hw').symm, fun i hi => converges_zeta _ (one_lt_re_shift hi hs), ?_⟩
    have hc1 : Converges (above E S) (twist c m⁻¹) s := hbc'.converges hs'
    have hc2 : Converges (above E S) (segFam 1 t) s := hbs.converges hs'
    show eulerProd (above E S) (twist P x⁻¹) s = eulerProd (above E S) (twist c m⁻¹) s *
      ∏ i ∈ Finset.range t, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)
    rw [eulerProd_congr htw, eulerProd_add hc1 hc2, eulerProd_segFam hs]
  have hr : ((r : ℝ) - 1) / 2 + 1 = ((r : ℝ) + 1) / 2 := by ring
  have hB : (∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
      DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re} := by
    refine ⟨fun s hs => ?_, ?_⟩
    · have h1 : Converges (above E S) (twist c m⁻¹) s := hbc.converges (by rw [hr]; exact hs)
      exact ⟨h1, h1.ne_zero⟩
    · have h1 := hbc.differentiableOn
      rw [hr] at h1
      exact h1
  obtain ⟨Z0, hZ0d, hZ0eq, hZ0ne⟩ := (hH E (above E S) (finite_above hS)).2
  refine ⟨hA, hB, ⟨_, isZetaCont_of_entire hZ0d hZ0eq⟩, fun Z hZ => ?_⟩
  have hZeq : ∀ u : ℂ, 1 < u.re → Z u = zetaOff (above E S) u := hZ.2
  have hs₀re : ((1 + (t : ℂ)) / 2).re = (1 + (t : ℝ)) / 2 := by
    rw [show (1 + (t : ℂ)) / 2 = (((1 + (t : ℝ)) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  refine ⟨fun s hs => ?_, by rw [hs₀re]; linarith, fun s hs => ?_, ?_⟩
  · have hU : {s : ℂ | ((r : ℝ) + 1) / 2 < s.re} ∈ 𝓝 s := (isOpen_re_gt _).mem_nhds hs
    have h1 : MeromorphicAt (LSTw S c m) s := (hB.2.analyticAt hU).meromorphicAt
    have h2 : MeromorphicAt (fun s => ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)) s := by
      refine MeromorphicAt.fun_prod fun i _ => ?_
      have hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) s := by fun_prop
      exact (hZ.1 _ trivial).comp_analyticAt hg
    exact h1.mul h2
  · rw [(hA s hs).2.2]
    show LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i) =
      LSTw S c m s * ∏ i ∈ Finset.range t, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)
    congr 1
    exact Finset.prod_congr rfl fun i hi => hZeq _ (one_lt_re_shift (Finset.mem_range.mp hi) hs)
  · have hcast : ((t - 1 : ℕ) : ℂ) = (t : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
    have hid : ∀ u : ℂ, u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ) - 1 = u - (1 + (t : ℂ)) / 2 := by
      intro u
      rw [hcast]
      ring
    have hsh0 : (1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ) = 1 := by
      rw [hcast]
      ring
    have hre0 : ∀ i : ℕ, ((1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i).re = (t : ℝ) - i := by
      intro i
      rw [show (1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i = (((t : ℝ) - i : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    have hlt : ∀ i ∈ Finset.range t \ {t - 1}, 1 < ((1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i).re := by
      intro i hi
      rw [hre0]
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
      obtain ⟨hi1, hi2⟩ := hi
      have h2 : (i : ℝ) + 2 ≤ t := by exact_mod_cast (by omega : i + 2 ≤ t)
      linarith
    have hmem : t - 1 ∈ Finset.range t := Finset.mem_range.mpr (by omega)
    have hE1 : ∀ᶠ s in 𝓝 ((1 + (t : ℂ)) / 2), ∀ i ∈ Finset.range t \ {t - 1},
        Z (s + ((t : ℂ) - 1) / 2 - i) = zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i) := by
      rw [Filter.eventually_all_finset]
      intro i hi
      have hc : Continuous (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) := by fun_prop
      filter_upwards [(hc.tendsto _).eventually ((isOpen_re_gt 1).mem_nhds (hlt i hi))] with u hu
      exact hZeq _ hu
    have hZZ0 := eventuallyEq_of_isZetaCont hZ (isZetaCont_of_entire hZ0d hZ0eq) 1
    have hc' : Continuous (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ)) := by fun_prop
    have htend : Tendsto (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))
        (𝓝[≠] ((1 + (t : ℂ)) / 2)) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 := hc'.tendsto ((1 + (t : ℂ)) / 2)
        rw [hsh0] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu ⊢
        intro heq
        apply hu
        have h1 := hid u
        rw [heq, sub_self] at h1
        exact sub_eq_zero.mp h1.symm
    have hE2 := htend.eventually hZZ0
    have hU : {s : ℂ | ((r : ℝ) + 1) / 2 < s.re} ∈ 𝓝 ((1 + (t : ℂ)) / 2) :=
      (isOpen_re_gt _).mem_nhds (by simp only [Set.mem_ofPred_eq]; rw [hs₀re]; linarith)
    have hA0 : AnalyticAt ℂ (LSTw S c m) ((1 + (t : ℂ)) / 2) := hB.2.analyticAt hU
    have hQ : AnalyticAt ℂ (fun s => ∏ i ∈ Finset.range t \ {t - 1},
        zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)) ((1 + (t : ℂ)) / 2) := by
      refine Finset.analyticAt_fun_prod _ fun i hi => ?_
      have hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) ((1 + (t : ℂ)) / 2) := by fun_prop
      exact AnalyticAt.comp (f := fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i)
        (analyticAt_zetaOff (K := E) (T := above E S) (hlt i hi)) hg
    have hZt : AnalyticAt ℂ (fun s => Z0 (s + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))) ((1 + (t : ℂ)) / 2) := by
      have hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ)) ((1 + (t : ℂ)) / 2) := by
        fun_prop
      exact (hZ0d.analyticAt _).comp hg
    have hGan : AnalyticAt ℂ (fun s => LSTw S c m s *
        (∏ i ∈ Finset.range t \ {t - 1}, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)) *
        Z0 (s + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))) ((1 + (t : ℂ)) / 2) :=
      (hA0.fun_mul hQ).fun_mul hZt
    refine hasSimplePole_of (Λ := rhs S c m t Z) (s₀ := (1 + (t : ℂ)) / 2) hGan ?_ ?_
    · refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact (hB.1 _ (by rw [hs₀re]; linarith)).2
      · exact Finset.prod_ne_zero_iff.mpr fun i hi => (converges_zeta _ (hlt i hi)).ne_zero
      · rw [hsh0]
        exact hZ0ne 1 (by simp)
    · filter_upwards [nhdsWithin_le_nhds hE1, hE2] with s hs1 hs2
      unfold rhs
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem, hs2, Finset.prod_congr rfl hs1, hid s]
      ring

end GlobalTheory.LiftPole

end
