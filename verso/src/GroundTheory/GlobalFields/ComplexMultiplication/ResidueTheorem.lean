import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Residue
import GroundTheory.GlobalFields.ComplexMultiplication.RectangleIntegral

open Complex Filter Topology Set
open scoped Interval Real

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

/- English proof (translation)
Use function extensionality and compare the values at `w`. Use `show dslope (fun w ↦ G (w + a)) w₀ w = dslope G (w₀ + a) (w + a)`. Break down `eq_or_ne w w₀ with rfl | hw` into its components or cases. Rewrite using `[dslope_same, dslope_same]`. Conclude with `deriv_comp_add_const _ _ _`.

Establish `hw' : w + a ≠ w₀ + a` using `fun h ↦ hw (add_right_cancel h)`. Rewrite using `[dslope_of_ne _ hw, dslope_of_ne _ hw', slope_def_field, slope_def_field]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma swap_dslope_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) :
    Function.swap dslope w₀ (fun w ↦ G (w + a)) =
      fun w ↦ Function.swap dslope (w₀ + a) G (w + a) := by
  funext w
  show dslope (fun w ↦ G (w + a)) w₀ w = dslope G (w₀ + a) (w + a)
  rcases eq_or_ne w w₀ with rfl | hw
  · rw [dslope_same, dslope_same]
    exact deriv_comp_add_const _ _ _
  · have hw' : w + a ≠ w₀ + a := fun h ↦ hw (add_right_cancel h)
    rw [dslope_of_ne _ hw, dslope_of_ne _ hw', slope_def_field, slope_def_field]
    congr 1
    ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[dslopeIter_succ', ih, swap_dslope_comp_add]`. Use function extensionality and compare the values at `w`.

Rewrite using `[dslopeIter_succ']`.
-/
lemma dslopeIter_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (w + a)) = fun w ↦ dslopeIter (w₀ + a) k G (w + a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_comp_add]
    funext w
    rw [dslopeIter_succ']

/- English proof (translation)
Use `set n := meromorphicShift f (w₀ + a)`. Use `set G : ℂ → ℂ := fun z ↦ (z - (w₀ + a)) ^ (n + 1) * f z with hGdef`. Establish `hG : AnalyticAt ℂ G (w₀ + a)` using `analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)`. Establish `e : (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) = fun w ↦ G (w + a)`. Use function extensionality and compare the values at `w`.

Simplify using `only [hGdef]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) w₀`. Rewrite using `[e]`.

Establish `: AnalyticAt ℂ (fun w ↦ w + a) w₀` using `by fun_prop`. Conclude with `hG.comp_of_eq this rfl`. Rewrite using `[residue_eq_dslopeIter hana, e, dslopeIter_comp_add]`. Both sides reduce to the same expression.
-/
theorem residue_comp_add {f : ℂ → ℂ} {a w₀ : ℂ} (hf : MeromorphicAt f (w₀ + a)) :
    residue (fun w ↦ f (w + a)) w₀ = residue f (w₀ + a) := by
  set n := meromorphicShift f (w₀ + a)
  set G : ℂ → ℂ := fun z ↦ (z - (w₀ + a)) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (w₀ + a) :=
    analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) = fun w ↦ G (w + a) := by
    funext w
    simp only [hGdef]
    congr 2
    ring
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) w₀ := by
    rw [e]
    have : AnalyticAt ℂ (fun w ↦ w + a) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  rw [residue_eq_dslopeIter hana, e, dslopeIter_comp_add]
  rfl

/- English proof (translation)
Distinguish the cases in `htop : meromorphicOrderAt f p = ⊤`. Rewrite `htop` using `[meromorphicOrderAt_eq_top_iff]`. Rewrite using `[residue_congr hf htop]`. Conclude with `residue_eq_zero_of_analyticAt analyticAt_const`. Take `⟨n, hn⟩` from `WithTop.ne_top_iff_exists.1 htop`.

Establish `hn0 : 0 ≤ n` using `by rw [← hn] at h; exact_mod_cast h`. Take `⟨g, hg, -, hfg⟩` from `(meromorphicOrderAt_eq_int_iff hf).1 hn.symm`. Simplify using `only [smul_eq_mul] at hfg`. Use `lift n to ℕ using hn0`. Rewrite using `[residue_congr hf hfg]`.

Apply `residue_eq_zero_of_analyticAt` to reduce the goal to its premises. Simplify using `only [zpow_natCast]`. Use `fun_prop`.
-/
theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (h : 0 ≤ meromorphicOrderAt f p) : residue f p = 0 := by
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [meromorphicOrderAt_eq_top_iff] at htop
    rw [residue_congr hf htop]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    have hn0 : 0 ≤ n := by rw [← hn] at h; exact_mod_cast h
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
    simp only [smul_eq_mul] at hfg
    lift n to ℕ using hn0
    rw [residue_congr hf hfg]
    apply residue_eq_zero_of_analyticAt
    simp only [zpow_natCast]
    fun_prop

/- English proof (translation)
Establish `h : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ((z - p) ^ k)⁻¹) u` using `fun k ↦ ((analyticAt_id.sub analyticAt_const).pow k).inv (pow_ne_zero _ (sub_ne_zero.2 hu))`. Establish `: principalPart f p = fun z ↦ ∑ j ∈ Finset.range (meromorphicShift f p + 1), laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹` using `rfl`. Rewrite using `[this]`. Conclude with `Finset.analyticAt_fun_sum _ fun j _ ↦ analyticAt_const.mul (h _)`.
-/
lemma analyticAt_principalPart (f : ℂ → ℂ) {p u : ℂ} (hu : u ≠ p) :
    AnalyticAt ℂ (principalPart f p) u := by
  have h : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ((z - p) ^ k)⁻¹) u := fun k ↦
    ((analyticAt_id.sub analyticAt_const).pow k).inv (pow_ne_zero _ (sub_ne_zero.2 hu))
  have : principalPart f p = fun z ↦ ∑ j ∈ Finset.range (meromorphicShift f p + 1),
      laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹ := rfl
  rw [this]
  exact Finset.analyticAt_fun_sum _ fun j _ ↦ analyticAt_const.mul (h _)

/- English proof (translation)
Establish `hp : p ∉ rectBoundary z w` using `notMem_rectBoundary_of_mem_Ioo ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩ ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩`. Establish `hne : ∀ u ∈ rectBoundary z w, u ≠ p` using `fun u hu h ↦ hp (h ▸ hu)`. Establish `hc : ∀ k : ℕ, ContinuousOn (fun u ↦ ((u - p) ^ k)⁻¹) (rectBoundary z w)` using `fun k u hu ↦ ((((continuous_id.sub continuous_const).pow k).continuousAt).inv₀ (pow_ne_zero _ (sub_ne_zero.2 (hne u hu)))).continuousWithinAt`. Use `set n := meromorphicShift f p`. Establish `e : principalPart f p = fun u ↦ ∑ j ∈ Finset.range (n + 1), laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹` using `rfl`.

Rewrite using `[e, rectIntegral_finset_sum (Finset.range (n + 1)) (f := fun j u ↦ laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹) (fun j _ ↦ continuousOn_const.mul (hc _))]`. Repeatedly rewrite using `[rectIntegral_const_mul]`. Rewrite using `[Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]`. Rewrite using `[Nat.add_sub_cancel_left]`. Repeatedly rewrite using `[pow_one]`.

Rewrite using `[rectIntegral_sub_inv h1 h2 h3 h4]`. Conclude with `mul_comm _ _`. Introduce `j hj`. Establish `hj' : j < n` using `Finset.mem_range.1 hj`. Establish `e2 : (fun u ↦ ((u - p) ^ (n + 1 - j))⁻¹) = fun u ↦ (u - p) ^ (-((n + 1 - j : ℕ) : ℤ))`.

Use function extensionality and compare the values at `u`. Rewrite using `[zpow_neg, zpow_natCast]`. Rewrite using `[e2, rectIntegral_zpow_sub _ hp, mul_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rectIntegral_principalPart (f : ℂ → ℂ) {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectIntegral (principalPart f p) z w = 2 * π * I * residue f p := by
  have hp : p ∉ rectBoundary z w := notMem_rectBoundary_of_mem_Ioo
    ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
    ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hne : ∀ u ∈ rectBoundary z w, u ≠ p := fun u hu h ↦ hp (h ▸ hu)
  have hc : ∀ k : ℕ, ContinuousOn (fun u ↦ ((u - p) ^ k)⁻¹) (rectBoundary z w) := fun k u hu ↦
    ((((continuous_id.sub continuous_const).pow k).continuousAt).inv₀
      (pow_ne_zero _ (sub_ne_zero.2 (hne u hu)))).continuousWithinAt
  set n := meromorphicShift f p
  have e : principalPart f p = fun u ↦ ∑ j ∈ Finset.range (n + 1),
      laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹ := rfl
  rw [e, rectIntegral_finset_sum (Finset.range (n + 1))
    (f := fun j u ↦ laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹)
    (fun j _ ↦ continuousOn_const.mul (hc _))]
  simp_rw [rectIntegral_const_mul]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · rw [Nat.add_sub_cancel_left]
    simp_rw [pow_one]
    rw [rectIntegral_sub_inv h1 h2 h3 h4]
    exact mul_comm _ _
  · intro j hj
    have hj' : j < n := Finset.mem_range.1 hj
    have e2 : (fun u ↦ ((u - p) ^ (n + 1 - j))⁻¹) = fun u ↦ (u - p) ^ (-((n + 1 - j : ℕ) : ℤ)) := by
      funext u
      rw [zpow_neg, zpow_natCast]
    rw [e2, rectIntegral_zpow_sub _ hp, mul_zero]
    omega

/- English proof (translation)
Use `set F : ℂ → ℂ := fun u ↦ f u - ∑ q ∈ S, principalPart f q u with hF`. Use `set E : ℂ → ℂ → ℂ := fun p u ↦ regularPart f p u - ∑ q ∈ S.erase p, principalPart f q u with hE`. Use `set G : ℂ → ℂ := fun u ↦ if u ∈ S then E u u else F u with hG`. Establish `hFE : ∀ p ∈ S, ∀ u, u ≠ p → F u = E p u`. Introduce `p hp u hu`.

Simplify using `only [hF, hE]`. Rewrite using `[eq_principalPart_add_regularPart f p hu, ← Finset.add_sum_erase S _ hp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hEana : ∀ p ∈ S, AnalyticAt ℂ (E p) p`. Introduce `p hp`.

Conclude with `(analyticAt_regularPart (hmero p hp)).sub (Finset.analyticAt_fun_sum _ fun q hq ↦ analyticAt_principalPart f (Finset.ne_of_mem_erase hq).symm)`. Establish `hGana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], AnalyticAt ℂ G u`. Introduce `u hu`. Distinguish the cases in `huS : u ∈ S`. Establish `hnhds : ((S.erase u : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 u` using `(S.erase u).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)`.

Use `(hEana u huS).congr ?_` and prove the remaining obligations. Use `filter_upwards [hnhds] with v hv`. Simplify using `only [hG]`. Break down `eq_or_ne v u with rfl | hvu` into its components or cases. Simplify using `[huS]`.

Establish `hvS : v ∉ S` using `fun h ↦ hv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvu, h⟩))`. Rewrite using `[if_neg hvS, hFE u huS v hvu]`. Establish `hnhds : ((S : Set ℂ))ᶜ ∈ 𝓝 u` using `S.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using huS)`. Establish `hFana : AnalyticAt ℂ F u` using `(hana u hu huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦ analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))`. Use `hFana.congr ?_` and prove the remaining obligations.

Use `filter_upwards [hnhds] with v hv`. Establish `hvS : v ∉ S` using `by simpa using hv`. Simplify using `only [hG, if_neg hvS]`. Establish `hSb : ∀ p ∈ S, p ∉ rectBoundary z w` using `fun p hp ↦ by`. Take `⟨h1, h2, h3, h4⟩` from `hS p hp`.

Conclude with `notMem_rectBoundary_of_mem_Ioo ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩ ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩`. Establish `hbK : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]]` using `rectBoundary_subset`. Establish `hG0 : rectIntegral G z w = 0`. Apply `rectIntegral_eq_zero_of_differentiable_on_off_countable G z w ∅ countable_empty` to reduce the goal to its premises. Conclude with `fun u hu ↦ (hGana u hu).continuousAt.continuousWithinAt`.

Introduce `u hu`. Apply `(hGana u _).differentiableAt` to reduce the goal to its premises. Establish `h'` using `hu.1`. Rewrite `h'`, the goal using `[mem_reProdIm]`. Conclude with `⟨Ioo_subset_Icc_self h'.1, Ioo_subset_Icc_self h'.2⟩`.

Establish `hGF : rectIntegral G z w = rectIntegral F z w`. Apply `rectIntegral_congr` to reduce the goal to its premises. Introduce `u hu`. Establish `huS : u ∉ S` using `fun h ↦ hSb u h hu`. Simplify using `only [hG, if_neg huS]`.

Establish `hPc : ∀ q ∈ S, ContinuousOn (principalPart f q) (rectBoundary z w)` using `fun q hq u hu ↦ (analyticAt_principalPart f (fun (h : u = q) ↦ hSb q hq (h ▸ hu))).continuousAt.continuousWithinAt`. Establish `hFc : ContinuousOn F (rectBoundary z w)` using `fun u hu ↦ by`. Establish `huS : u ∉ S` using `fun h ↦ hSb u h hu`. Conclude with `((hana u (hbK hu) huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦ analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))).continuousAt.continuousWithinAt`. Establish `hsplit : rectIntegral f z w = rectIntegral F z w + ∑ q ∈ S, rectIntegral (principalPart f q) z w`.

Rewrite using `[← rectIntegral_finset_sum S hPc, ← rectIntegral_add hFc (continuousOn_finsetSum S hPc)]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Simplify using `only [hF]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit, ← hGF, hG0, zero_add, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `q hq`. Take `⟨h1, h2, h3, h4⟩` from `hS q hq`. Conclude with `rectIntegral_principalPart f h1 h2 h3 h4`.
-/
theorem rectIntegral_eq_sum_residue {f : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ)
    (hS : ∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)
    (hmero : ∀ p ∈ S, MeromorphicAt f p)
    (hana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], u ∉ S → AnalyticAt ℂ f u) :
    rectIntegral f z w = 2 * π * I * ∑ p ∈ S, residue f p := by
  classical
  set F : ℂ → ℂ := fun u ↦ f u - ∑ q ∈ S, principalPart f q u with hF
  set E : ℂ → ℂ → ℂ := fun p u ↦ regularPart f p u - ∑ q ∈ S.erase p, principalPart f q u
    with hE
  set G : ℂ → ℂ := fun u ↦ if u ∈ S then E u u else F u with hG
  have hFE : ∀ p ∈ S, ∀ u, u ≠ p → F u = E p u := by
    intro p hp u hu
    simp only [hF, hE]
    rw [eq_principalPart_add_regularPart f p hu, ← Finset.add_sum_erase S _ hp]
    ring
  have hEana : ∀ p ∈ S, AnalyticAt ℂ (E p) p := by
    intro p hp
    exact (analyticAt_regularPart (hmero p hp)).sub
      (Finset.analyticAt_fun_sum _ fun q hq ↦
        analyticAt_principalPart f (Finset.ne_of_mem_erase hq).symm)
  have hGana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], AnalyticAt ℂ G u := by
    intro u hu
    by_cases huS : u ∈ S
    · have hnhds : ((S.erase u : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 u :=
        (S.erase u).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine (hEana u huS).congr ?_
      filter_upwards [hnhds] with v hv
      simp only [hG]
      rcases eq_or_ne v u with rfl | hvu
      · simp [huS]
      · have hvS : v ∉ S := fun h ↦ hv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvu, h⟩))
        rw [if_neg hvS, hFE u huS v hvu]
    · have hnhds : ((S : Set ℂ))ᶜ ∈ 𝓝 u :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using huS)
      have hFana : AnalyticAt ℂ F u :=
        (hana u hu huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
          analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))
      refine hFana.congr ?_
      filter_upwards [hnhds] with v hv
      have hvS : v ∉ S := by simpa using hv
      simp only [hG, if_neg hvS]
  have hSb : ∀ p ∈ S, p ∉ rectBoundary z w := fun p hp ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hS p hp
    exact notMem_rectBoundary_of_mem_Ioo
      ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
      ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hbK : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := rectBoundary_subset
  have hG0 : rectIntegral G z w = 0 := by
    apply rectIntegral_eq_zero_of_differentiable_on_off_countable G z w ∅ countable_empty
    · exact fun u hu ↦ (hGana u hu).continuousAt.continuousWithinAt
    · intro u hu
      apply (hGana u _).differentiableAt
      have h' := hu.1
      rw [mem_reProdIm] at h' ⊢
      exact ⟨Ioo_subset_Icc_self h'.1, Ioo_subset_Icc_self h'.2⟩
  have hGF : rectIntegral G z w = rectIntegral F z w := by
    apply rectIntegral_congr
    intro u hu
    have huS : u ∉ S := fun h ↦ hSb u h hu
    simp only [hG, if_neg huS]
  have hPc : ∀ q ∈ S, ContinuousOn (principalPart f q) (rectBoundary z w) := fun q hq u hu ↦
    (analyticAt_principalPart f (fun (h : u = q) ↦ hSb q hq (h ▸ hu))).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (rectBoundary z w) := fun u hu ↦ by
    have huS : u ∉ S := fun h ↦ hSb u h hu
    exact ((hana u (hbK hu) huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
      analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))).continuousAt.continuousWithinAt
  have hsplit : rectIntegral f z w =
      rectIntegral F z w + ∑ q ∈ S, rectIntegral (principalPart f q) z w := by
    rw [← rectIntegral_finset_sum S hPc, ← rectIntegral_add hFc (continuousOn_finsetSum S hPc)]
    congr 1
    funext u
    simp only [hF]
    ring
  rw [hsplit, ← hGF, hG0, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hS q hq
  exact rectIntegral_principalPart f h1 h2 h3 h4

end Elliptic
end GroundTheory.Global
