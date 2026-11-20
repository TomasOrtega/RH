import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HkRowIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

noncomputable section
open scoped BigOperators ComplexConjugate
open Filter Topology

namespace Formalism.L2.Th1.F

namespace Hk4

/- English proof (translation)
Simplify using `[hk]`.
-/
lemma hk_zero (w : ℂ) : hk 0 w = 1 / w ^ 2 := by simp [hk]

def cellOff (τ : ℂ) (s : ℝ) (p : ℤ × ℤ) : ℂ := if p.2 = 0 then 0 else hkCell τ s p

/- English proof (translation)
Unfold `cellOff`. Use `split_ifs with hp`. Simplify using the standard rewrite rules. Conclude with `(hbd s p h0 h1 hp).trans (le_abs_self _)`.
-/
lemma cellOff_norm_le {τ : ℂ} {b : ℤ × ℤ → ℝ}
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (p : ℤ × ℤ) : ‖cellOff τ s p‖ ≤ |b p| := by
  unfold cellOff
  split_ifs with hp
  · simp
  · exact (hbd s p h0 h1 hp).trans (le_abs_self _)

/- English proof (translation)
Establish `hC : Summable (cellOff τ s)` using `Summable.of_norm_bounded hb.abs (cellOff_norm_le hbd h0 h1)`. Establish `hC' : Summable (fun q : ℤ × ℤ => cellOff τ s (q.2, q.1))` using `(Equiv.prodComm ℤ ℤ).summable_iff.mpr hC`. Establish `hCsum : ∑' p : ℤ × ℤ, cellOff τ s p = ∑' n : ℤ, ∑' m : ℤ, cellOff τ s (m, n)`. Rewrite using `[← (Equiv.prodComm ℤ ℤ).tsum_eq (cellOff τ s)]`. Conclude with `hC'.tsum_prod`.

Establish `hG : Summable (fun n : ℤ => ∑' m : ℤ, cellOff τ s (m, n))` using `hC'.prod`. Establish `hrow : ∀ n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ) = (if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0) + ∑' m : ℤ, cellOff τ s (m, n) + (if n = 0 then 0 else hkInt τ s n)`. Introduce `n`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality.

Simplify using `[cellOff]`. Establish `hs1 : Summable (fun m : ℤ => cellOff τ s (m, n))` using `hC'.prod_factor n`. Establish `hs2` using `(h2 τ s n hτ h0 hn).2`. Use `hs1.hasSum.add hs2` as an intermediate fact. Establish `he : (fun m : ℤ => cellOff τ s (m, n) + ∫ x in (0 : ℝ)..1, hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)) = fun m : ℤ => hk s ((m : ℂ) + (n : ℂ) * τ)`.

Use function extensionality and compare the values at `m`. Simplify using `[cellOff, hkCell, hn]`. Rewrite `this` using `[he]`. Rewrite using `[this.tsum_eq]`. Simplify using `[hn]`.

Establish `hR : Summable (fun n : ℤ => if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0)` using `(hasSum_ite_eq (0 : ℤ) _).summable`. Rewrite using `[tsum_congr hrow, (hR.add hG).tsum_add hI, hR.tsum_add hG, tsum_ite_eq, hCsum]`.
-/
lemma split (h2 : HkRowIntegral) {τ : ℂ} (hτ : τ.im ≠ 0) {b : ℤ × ℤ → ℝ} (hb : Summable b)
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hI : Summable (fun n : ℤ => if n = 0 then 0 else hkInt τ s n)) :
    ∑' n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ)
      = ∑' m : ℤ, hk s (m : ℂ) + ∑' p : ℤ × ℤ, cellOff τ s p
        + ∑' n : ℤ, (if n = 0 then 0 else hkInt τ s n) := by
  have hC : Summable (cellOff τ s) :=
    Summable.of_norm_bounded hb.abs (cellOff_norm_le hbd h0 h1)
  have hC' : Summable (fun q : ℤ × ℤ => cellOff τ s (q.2, q.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hC
  have hCsum : ∑' p : ℤ × ℤ, cellOff τ s p = ∑' n : ℤ, ∑' m : ℤ, cellOff τ s (m, n) := by
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (cellOff τ s)]
    exact hC'.tsum_prod
  have hG : Summable (fun n : ℤ => ∑' m : ℤ, cellOff τ s (m, n)) := hC'.prod
  have hrow : ∀ n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ)
      = (if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0) + ∑' m : ℤ, cellOff τ s (m, n)
        + (if n = 0 then 0 else hkInt τ s n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [cellOff]
    · have hs1 : Summable (fun m : ℤ => cellOff τ s (m, n)) := hC'.prod_factor n
      have hs2 := (h2 τ s n hτ h0 hn).2
      have := hs1.hasSum.add hs2
      have he : (fun m : ℤ => cellOff τ s (m, n)
          + ∫ x in (0 : ℝ)..1, hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ))
          = fun m : ℤ => hk s ((m : ℂ) + (n : ℂ) * τ) := by
        funext m
        simp [cellOff, hkCell, hn]
      rw [he] at this
      rw [this.tsum_eq]
      simp [hn]
  have hR : Summable (fun n : ℤ => if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) _).summable
  rw [tsum_congr hrow, (hR.add hG).tsum_add hI, hR.tsum_add hG, tsum_ite_eq, hCsum]

end Hk4

open Hk4 in
/- English proof (translation)
Introduce `τ hτ`. Take `⟨b, hb, hbd⟩` from `h3 τ hτ`. Establish `hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ)` using `Ioc_mem_nhdsGT one_pos`. Establish `hcell : Tendsto (fun s : ℝ => ∑' p : ℤ × ℤ, cellOff τ s p) (𝓝[>] 0) (𝓝 (∑' p : ℤ × ℤ, cellOff τ 0 p))`. Use `tendsto_tsum_of_dominated_convergence hb.abs ?_ ?_` and prove the remaining obligations.

Introduce `p`. Distinguish the cases in `hp : p.2 = 0`. Simplify using `[cellOff, hp]`. Simplify `h4 τ p hτ hp` using `[cellOff, hp]`. Use `filter_upwards [hmem] with s hs p`.

Conclude with `cellOff_norm_le hbd hs.1.le hs.2 p`. Establish `hI0 : (fun n : ℤ => if n = 0 then (0 : ℂ) else hkInt τ 0 n) = fun _ => 0`. Use function extensionality and compare the values at `n`. Distinguish the cases in `hn : n = 0`. Simplify using `[hn]`.

Simplify using `[hn, h5 τ n hτ hn]`. Establish `hzero` using `split h2 hτ hb hbd le_rfl zero_le_one (by rw [hI0]; exact summable_zero)`. Rewrite `hzero` using `[hI0, tsum_zero, add_zero]`. Simplify using `only [hk_zero] at hzero`. Rewrite using `[hzero]`.

Establish `hlim` using `(h6.add hcell).add (h7 τ hτ).2`. Rewrite `hlim` using `[← sub_eq_add_neg]`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hmem] with s hs`. Rewrite using `[← split h2 hτ hb hbd hs.1.le hs.2 ((h7 τ hτ).1 s hs.1)]`.

Establish `hS` using `h1 τ s hτ hs.1`. Establish `hS' : Summable (fun q : ℤ × ℤ => hk s ((q.2 : ℂ) + (q.1 : ℂ) * τ))` using `(Equiv.prodComm ℤ ℤ).summable_iff.mpr hS`. Rewrite using `[← (Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ))]`. Conclude with `hS'.tsum_prod.symm`.
-/
theorem hkLimit_of (h1 : HkSummable) (h2 : HkRowIntegral) (h3 : HkCellBound) (h4 : HkCellCont)
    (h5 : HkIntZero) (h6 : HkRowZero) (h7 : HkIntLimit) : HkLimit := by
  intro τ hτ
  obtain ⟨b, hb, hbd⟩ := h3 τ hτ
  have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT one_pos

  have hcell : Tendsto (fun s : ℝ => ∑' p : ℤ × ℤ, cellOff τ s p) (𝓝[>] 0)
      (𝓝 (∑' p : ℤ × ℤ, cellOff τ 0 p)) := by
    refine tendsto_tsum_of_dominated_convergence hb.abs ?_ ?_
    · intro p
      by_cases hp : p.2 = 0
      · simp [cellOff, hp]
      · simpa [cellOff, hp] using h4 τ p hτ hp
    · filter_upwards [hmem] with s hs p
      exact cellOff_norm_le hbd hs.1.le hs.2 p

  have hI0 : (fun n : ℤ => if n = 0 then (0 : ℂ) else hkInt τ 0 n) = fun _ => 0 := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, h5 τ n hτ hn]
  have hzero := split h2 hτ hb hbd le_rfl zero_le_one (by rw [hI0]; exact summable_zero)
  rw [hI0, tsum_zero, add_zero] at hzero
  simp only [hk_zero] at hzero
  rw [hzero]
  have hlim := (h6.add hcell).add (h7 τ hτ).2
  rw [← sub_eq_add_neg] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmem] with s hs
  rw [← split h2 hτ hb hbd hs.1.le hs.2 ((h7 τ hτ).1 s hs.1)]
  have hS := h1 τ s hτ hs.1
  have hS' : Summable (fun q : ℤ × ℤ => hk s ((q.2 : ℂ) + (q.1 : ℂ) * τ)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hS
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ))]
  exact hS'.tsum_prod.symm

namespace Hk4

/- English proof (translation)
Unfold `hk`. Rewrite using `[norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_pow, mul_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hk_mul (s : ℝ) (u w : ℂ) :
    hk s (u * w) = (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ) * hk s w := by
  unfold hk
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_pow, mul_inv]
  push_cast
  ring

end Hk4

open Hk4 PeriodAreaSignLemmas in
/- English proof (translation)
Introduce `L`. Use `set u := L.ω₁ with hu_def`. Establish `hu : u ≠ 0` using `ω₁_ne_zero L`. Use `set τ := L.ω₂ / u with hτ_def`. Establish `hN : 0 < Complex.normSq u` using `Complex.normSq_pos.mpr hu`.

Establish `him : τ.im = det L / Complex.normSq u` using `div_im L`. Establish `hτ : τ.im ≠ 0`. Rewrite using `[him]`. Conclude with `div_ne_zero (det_ne_zero L) hN.ne'`. Establish `hlin : ∀ m n : ℤ, (m : ℂ) * u + (n : ℂ) * L.ω₂ = u * ((m : ℂ) + (n : ℂ) * τ)`.

Introduce `m n`. Rewrite using `[hτ_def]`. Clear the denominators using the available nonvanishing facts. Establish `hsum : ∀ s : ℝ, ∑' ω : L.lattice, ((ω : ℂ) ^ 2)⁻¹ * ((‖(ω : ℂ)‖ ^ (-(2 * s)) : ℝ) : ℂ) = (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ)`. Introduce `s`.

Rewrite using `[← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations. Rewrite using `[← hk_mul, ← hlin]`. Simplify using `only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, hk]`. Both sides reduce to the same expression.

Simplify using `only [hsum]`. Establish `hc : Tendsto (fun s : ℝ => (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((u ^ 2)⁻¹ * 1))`. Use `Tendsto.const_mul _ ?_` and prove the remaining obligations. Establish `h1 : ContinuousAt (fun s : ℝ => ‖u‖ ^ (-(2 * s))) 0`. Establish `: ContinuousAt (fun x : ℝ => ‖u‖ ^ x) (-(2 * (0 : ℝ)))` using `Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hu)`.

Conclude with `ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) this (by fun_prop)`. Establish `h2 : Tendsto (fun s : ℝ => ‖u‖ ^ (-(2 * s))) (𝓝[>] 0) (𝓝 1)`. Use `h1.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))` as an intermediate fact. Simplify using `using this`. Use `(Complex.continuous_ofReal.tendsto 1).comp h2` as an intermediate fact.

Simplify `this` using `[Function.comp_def]`. Establish `hmain` using `hc.mul (h τ hτ)`. Use `hmain using 2` and compare the differences between its conclusion and the goal. Establish `hE` using `(etaEisenstein L).1`. Establish `hSp` using `etaSplit L u`.

Establish `hT : ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 = (u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2`. Repeatedly rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun n => tsum_congr fun m => ?_` and prove the remaining obligations. Rewrite using `[hlin, mul_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite `hE` using `[hT, ← hu_def]`. Establish `hA : (area L : ℂ) ≠ 0` using `by exact_mod_cast (area_pos L).ne'`. Establish `habs : |τ.im| = area L / Complex.normSq u`. Rewrite using `[him, abs_div, abs_of_pos hN, area_eq]`. Establish `hNc : ((Complex.normSq u : ℝ) : ℂ) = u * conj u` using `(Complex.mul_conj u).symm`.

Establish `hcu : conj u ≠ 0` using `by simpa using hu`. Rewrite using `[habs]`. Use `push_cast`. Rewrite using `[hNc]`. Rewrite `hSp` using `[hE]`.

Establish `hs : s2 L = (u * ((u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2) - ((Real.pi : ℂ) / (area L : ℂ)) * conj u) / u`. Rewrite using `[hSp]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs]`.

Generalize the expression as in `(∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2) = T`. Clear the denominators using the available nonvanishing facts.
-/
theorem eisensteinS2LimitFormula_of_hkLimit (h : HkLimit) : EisensteinS2LimitFormula := by
  intro L
  set u := L.ω₁ with hu_def
  have hu : u ≠ 0 := ω₁_ne_zero L
  set τ := L.ω₂ / u with hτ_def
  have hN : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have him : τ.im = det L / Complex.normSq u := div_im L
  have hτ : τ.im ≠ 0 := by
    rw [him]; exact div_ne_zero (det_ne_zero L) hN.ne'
  have hlin : ∀ m n : ℤ, (m : ℂ) * u + (n : ℂ) * L.ω₂ = u * ((m : ℂ) + (n : ℂ) * τ) := by
    intro m n
    rw [hτ_def]; field_simp
  have hsum : ∀ s : ℝ, ∑' ω : L.lattice, ((ω : ℂ) ^ 2)⁻¹ * ((‖(ω : ℂ)‖ ^ (-(2 * s)) : ℝ) : ℂ)
      = (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ) := by
    intro s
    rw [← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    rw [← hk_mul, ← hlin]
    simp only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, hk]
    rfl
  simp only [hsum]
  have hc : Tendsto (fun s : ℝ => (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((u ^ 2)⁻¹ * 1)) := by
    refine Tendsto.const_mul _ ?_
    have h1 : ContinuousAt (fun s : ℝ => ‖u‖ ^ (-(2 * s))) 0 := by
      have : ContinuousAt (fun x : ℝ => ‖u‖ ^ x) (-(2 * (0 : ℝ))) :=
        Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hu)
      exact ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) this (by fun_prop)
    have h2 : Tendsto (fun s : ℝ => ‖u‖ ^ (-(2 * s))) (𝓝[>] 0) (𝓝 1) := by
      have := h1.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have := (Complex.continuous_ofReal.tendsto 1).comp h2
    simpa [Function.comp_def] using this
  have hmain := hc.mul (h τ hτ)
  convert hmain using 2

  have hE := (etaEisenstein L).1
  have hSp := etaSplit L u
  have hT : ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2
      = (u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2 := by
    simp_rw [← tsum_mul_left]
    refine tsum_congr fun n => tsum_congr fun m => ?_
    rw [hlin, mul_pow]
    field_simp
  rw [hT, ← hu_def] at hE
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (area_pos L).ne'
  have habs : |τ.im| = area L / Complex.normSq u := by
    rw [him, abs_div, abs_of_pos hN, area_eq]
  have hNc : ((Complex.normSq u : ℝ) : ℂ) = u * conj u := (Complex.mul_conj u).symm
  have hcu : conj u ≠ 0 := by simpa using hu
  rw [habs]
  push_cast
  rw [hNc]
  rw [hE] at hSp
  have hs : s2 L = (u * ((u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2)
      - ((Real.pi : ℂ) / (area L : ℂ)) * conj u) / u := by
    rw [hSp]; field_simp; ring
  rw [hs]
  generalize (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2) = T
  field_simp

end Formalism.L2.Th1.F
