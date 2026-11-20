import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousHerm

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

/- English proof (translation)
Simplify using `only [cls, neg_zero, Complex.cpow_zero, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cls_shift {n : ℕ} (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y = cls s z p q R y := by
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul]
  ring

/- English proof (translation)
Introduce `hG hB hGain hIBP hI hD m n ε c t hc ht P`. Take `⟨R, hR⟩` from `hG m n ε c t hc ht P`. Establish `ht0 : t ≠ 0`. Break down `ht with rfl | rfl` into its components or cases. Conclude with `hc.ne'`.

Conclude with `neg_ne_zero.2 hc.ne'`. Establish `hs' : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1`. Break down `ht with rfl | rfl` into its components or cases. Use `left`. Simplify using `[hc.ne']`.

Use `right`. Simplify using `[hc.ne']`. Generalize the expression as in `((t / c : ℝ) : ℂ) = s at hR hs'`. Establish `hs` using `hs'`. Generalize the expression as in `(Finset.univ.filter fun a => ε a = true).card = p at hR`.

Generalize the expression as in `(Finset.univ.filter fun a => ε a = false).card = q at hR`. Take `⟨-, hint⟩` from `hI n`. Take `⟨g, hgc, hgd, hgv⟩` from `hD m n ε c t hc ht P (n ^ 2 + 1) (by`. Use `push_cast`. Establish `: (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`.

Use the proof step `linarith)`. Use `⟨g, hgc, hgd, fun β hβ => ?_⟩` and prove the remaining obligations. Establish `hGN` using `fun N => hGain n s hs p q N R`. Use `choose J a G hGc hGb hGeq using hGN`. Use `choose CG hCG using hGb`.

Establish `hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2))` using `fun N j y => by`. Use `hCG N j y` as an intermediate fact. Rewrite `this` using `[neg_div]`. Then use the resulting hypothesis. Use `set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK`. Set `Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ` to `fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y`.

Set `WN : ℕ → ℂ → ℂ` to `fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z`. Set `U : ℕ → Set ℂ` to `fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2}`. Set `orig : ℂ → ℂ` to `fun z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y`. Establish `hUopen : ∀ N, IsOpen (U N)` using `fun N => isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)`. Establish `hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N)`.

Introduce `N`. Use `DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _` and prove the remaining obligations. Conclude with `(a N j).differentiable.differentiableOn.mul (holo hI t β (hGc N j) (((p + q + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))`. Establish `hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 → ∫ y, (Delta^[N] (cls s z p q R)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z`. Introduce `N z hz`.

Establish `e : (fun y => (Delta^[N] (cls s z p q R)) y * chr t β y) = fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y)`. Use function extensionality and compare the values at `y`. Rewrite using `[hGeq N z y, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Rewrite using `[e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul]`. Establish `hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z`. Introduce `N z hz`. Establish `e1 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) = fun y => cls s z p q R y * chr t β y`.

Use function extensionality and compare the values at `y`. Rewrite using `[hR y, ← cls_shift s z]`. Establish `hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2` using `by positivity`. Establish `good : Good (cls s z p q R)`. Use `⟨(hB n s hs p q R z).1, fun L => ?_⟩` and prove the remaining obligations.

Take `⟨C, hC⟩` from `(hB n s hs p q R z).2 L`. Conclude with `⟨fun y => C * dP y ^ (-(z.re + ((p : ℝ) + q) / 2)), (hint _ (by linarith)).const_mul C, hC⟩`. Establish `hz' : (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2`. Establish `: (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `show KK ^ N * _ = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y`. Rewrite using `[e1, ibp_iter hIBP good t β ht0 hβ N, hsum N z hz']`. Establish `agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N)`. Introduce `N N' hNN'`. Establish `hsub : U N ⊆ U N'` using `fun z hz => by`.

Simplify using `only [U, Set.mem_ofPred_eq] at hz ⊢`. Establish `: ((p + q + N : ℕ) : ℝ) ≤ ((p + q + N' : ℕ) : ℝ)` using `by exact_mod_cast (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : AnalyticOnNhd ℂ (WN N) (U N)` using `(hWdiff N).analyticOnNhd (hUopen N)`. Establish `hA' : AnalyticOnNhd ℂ (WN N') (U N)` using `((hWdiff N').mono hsub).analyticOnNhd (hUopen N)`.

Establish `hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((p + q + N : ℕ) : ℝ) / 2 < z.re}`. Use extensionality with `z`. Simplify using `only [U, Set.mem_ofPred_eq]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`. Establish `hpre : IsPreconnected (U N)`.

Rewrite using `[hU]`. Conclude with `(convex_halfSpace_re_gt _).isPreconnected`. Use `set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1`. Establish `hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1` using `by rw [hz1, Complex.ofReal_re]`. Establish `hz1U : z1 ∈ U N`.

Simplify using `only [U, Set.mem_ofPred_eq, hz1re]`. Establish `: (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re}`.

Simplify using `only [Set.mem_ofPred_eq, hz1re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hev : WN N =ᶠ[𝓝 z1] WN N'` using `Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm`. Conclude with `hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev`. Establish `agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z`.

Introduce `N N' z hz hz'`. Break down `le_total N N' with h | h` into its components or cases. Conclude with `agree N N' h hz`. Conclude with `(agree N' N h hz').symm`. Take `⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1` from `⟨_, fun _ => rfl⟩`.

Establish `hNf : ∀ z, z ∈ U (Nf z)`. Introduce `z`. Use `show (n : ℝ) ^ 2 / 2 < z.re + ((p + q + Nf z : ℕ) : ℝ) / 2`. Rewrite using `[hNfdef z]`. Establish `h1` using `Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)`.

Use `push_cast`. Establish `: (0 : ℝ) ≤ (p : ℝ) + q` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Introduce `z0`.

Establish `hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0)` using `Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz`. Conclude with `(((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev`. Establish `e2 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y * chr t β y`. Use function extensionality and compare the values at `y`. Rewrite using `[hR y]`.

Rewrite using `[e2]`. Take `⟨C, hC⟩` from `(hB n s hs p q R 0).2 []`. Establish `hC0 : ∀ y, ‖cls s 0 p q R y‖ ≤ C * dP y ^ (-(((p : ℝ) + q) / 2))`. Introduce `y`. Use `hC y` as an intermediate fact.

Simplify using `only [List.foldr_nil, Complex.zero_re, zero_add] at this`. Conclude with `this`. Establish `hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2` using `by positivity`. Conclude with `integ_term hI t β (hB n s hs p q R 0).1.continuous hC0 (by linarith)`. Conclude with `hbig (Nf z) z hz`.

Establish `hN0 : Nf 0 = n ^ 2 + 1`. Rewrite using `[hNfdef, Complex.zero_re, mul_zero, sub_zero, show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]`. Use `show WN (Nf 0) 0 = _`. Rewrite using `[hN0, hgv β hβ]`. Establish `hfun : (fun y => secN ε c t P (herm y)) = cls s 0 p q R` using `funext hR`.

Rewrite using `[hfun, hsum (n ^ 2 + 1) 0 (by`. Simplify using `only [Complex.zero_re, zero_add]`. Use `push_cast`. Establish `: (0 : ℝ) ≤ (p : ℝ) + q` using `by positivity`. Use the proof step `linarith)]`.

Use `show KK ^ (n ^ 2 + 1) * _ = _`. Rewrite using `[hKK]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wr_of : Gauss → ClsBound → ClsGain → IBP → Integr → Dens → WRSt := by
  intro hG hB hGain hIBP hI hD m n ε c t hc ht P
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.2 hc.ne'
  have hs' : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left; simp [hc.ne']
    · right; simp [hc.ne']
  generalize ((t / c : ℝ) : ℂ) = s at hR hs'
  have hs := hs'
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hR
  generalize (Finset.univ.filter fun a => ε a = false).card = q at hR
  obtain ⟨-, hint⟩ := hI n
  obtain ⟨g, hgc, hgd, hgv⟩ := hD m n ε c t hc ht P (n ^ 2 + 1) (by
    push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  refine ⟨g, hgc, hgd, fun β hβ => ?_⟩
  have hGN := fun N => hGain n s hs p q N R
  choose J a G hGc hGb hGeq using hGN
  choose CG hCG using hGb
  have hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := fun N j y => by
    have := hCG N j y
    rwa [neg_div] at this
  set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK
  let Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ := fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y
  let WN : ℕ → ℂ → ℂ := fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z
  let U : ℕ → Set ℂ := fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2}
  let orig : ℂ → ℂ := fun z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
  have hUopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N) := by
    intro N
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    exact (a N j).differentiable.differentiableOn.mul
      (holo hI t β (hGc N j) (((p + q + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))

  have hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 →
      ∫ y, (Delta^[N] (cls s z p q R)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z := by
    intro N z hz
    have e : (fun y => (Delta^[N] (cls s z p q R)) y * chr t β y) =
        fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y) := by
      funext y
      rw [hGeq N z y, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z := by
    intro N z hz
    have e1 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => cls s z p q R y * chr t β y := by
      funext y
      rw [hR y, ← cls_shift s z]
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    have good : Good (cls s z p q R) := by
      refine ⟨(hB n s hs p q R z).1, fun L => ?_⟩
      obtain ⟨C, hC⟩ := (hB n s hs p q R z).2 L
      exact ⟨fun y => C * dP y ^ (-(z.re + ((p : ℝ) + q) / 2)), (hint _ (by linarith)).const_mul C, hC⟩
    have hz' : (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    show KK ^ N * _ = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
    rw [e1, ibp_iter hIBP good t β ht0 hβ N, hsum N z hz']
  have agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N) := by
    intro N N' hNN'
    have hsub : U N ⊆ U N' := fun z hz => by
      simp only [U, Set.mem_ofPred_eq] at hz ⊢
      have : ((p + q + N : ℕ) : ℝ) ≤ ((p + q + N' : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have hA : AnalyticOnNhd ℂ (WN N) (U N) := (hWdiff N).analyticOnNhd (hUopen N)
    have hA' : AnalyticOnNhd ℂ (WN N') (U N) := ((hWdiff N').mono hsub).analyticOnNhd (hUopen N)
    have hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((p + q + N : ℕ) : ℝ) / 2 < z.re} := by
      ext z
      simp only [U, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hpre : IsPreconnected (U N) := by
      rw [hU]; exact (convex_halfSpace_re_gt _).isPreconnected
    set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1
    have hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1 := by rw [hz1, Complex.ofReal_re]
    have hz1U : z1 ∈ U N := by
      simp only [U, Set.mem_ofPred_eq, hz1re]
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := by
      simp only [Set.mem_ofPred_eq, hz1re]; linarith
    have hev : WN N =ᶠ[𝓝 z1] WN N' :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm
    exact hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev
  have agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z := by
    intro N N' z hz hz'
    rcases le_total N N' with h | h
    · exact agree N N' h hz
    · exact (agree N' N h hz').symm
  obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1 := ⟨_, fun _ => rfl⟩
  have hNf : ∀ z, z ∈ U (Nf z) := by
    intro z
    show (n : ℝ) ^ 2 / 2 < z.re + ((p + q + Nf z : ℕ) : ℝ) / 2
    rw [hNfdef z]
    have h1 := Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)
    push_cast
    have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
    linarith
  refine ⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · intro z0
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0) :=
      Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz
    exact (((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev
  · have e2 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y * chr t β y := by
      funext y; rw [hR y]
    rw [e2]
    obtain ⟨C, hC⟩ := (hB n s hs p q R 0).2 []
    have hC0 : ∀ y, ‖cls s 0 p q R y‖ ≤ C * dP y ^ (-(((p : ℝ) + q) / 2)) := by
      intro y
      have := hC y
      simp only [List.foldr_nil, Complex.zero_re, zero_add] at this
      exact this
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    exact integ_term hI t β (hB n s hs p q R 0).1.continuous hC0 (by linarith)
  · exact hbig (Nf z) z hz
  · have hN0 : Nf 0 = n ^ 2 + 1 := by
      rw [hNfdef, Complex.zero_re, mul_zero, sub_zero,
        show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
    show WN (Nf 0) 0 = _
    rw [hN0, hgv β hβ]
    have hfun : (fun y => secN ε c t P (herm y)) = cls s 0 p q R := funext hR
    rw [hfun, hsum (n ^ 2 + 1) 0 (by
      simp only [Complex.zero_re, zero_add]
      push_cast
      have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
      linarith)]
    show KK ^ (n ^ 2 + 1) * _ = _
    rw [hKK]
    ring

end PositivityTheory.Rg.Sw.WR.T
