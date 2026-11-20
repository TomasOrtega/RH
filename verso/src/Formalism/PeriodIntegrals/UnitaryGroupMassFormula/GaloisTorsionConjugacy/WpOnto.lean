import Mathlib
import Formalism.PeriodIntegrals.GalTorsConj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpBridge
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole

noncomputable section

namespace PI.GalTorsConj.W

open PI.GalTorsConj Filter Topology

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Use `set f : ℂ → ℂ := fun z => (L.weierstrassP z - x)⁻¹ with hf`. Establish `hmer : ∀ z, MeromorphicAt f z`. Introduce `z`.

Establish `h` using `L.meromorphic_weierstrassP z`. Use `fun_prop`. Establish `hper : Formalism.L2.Th1.F.IsPeriodic L f`. Introduce `ω hω z`. Use `show (L.weierstrassP (z + ω) - x)⁻¹ = (L.weierstrassP z - x)⁻¹`.

Rewrite using `[show L.weierstrassP (z + ω) = L.weierstrassP z from L.weierstrassP_add_coe z ⟨ω, hω⟩]`. Establish `han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ f z`. Introduce `z hz`. Establish `h1 : AnalyticAt ℂ L.weierstrassP z` using `L.analyticOnNhd_weierstrassP z hz`. Establish `h2 : L.weierstrassP z - x ≠ 0` using `sub_ne_zero.mpr (hne z hz)`.

Conclude with `(h1.sub analyticAt_const).inv h2`. Establish `hord : ∀ z, 0 ≤ meromorphicOrderAt f z`. Introduce `z`. Distinguish the cases in `hz : z ∈ L.lattice`. Establish `h1 : meromorphicOrderAt (fun w => L.weierstrassP w - x) z = -2`.

Establish `e : (fun w => L.weierstrassP w - x) = L.weierstrassP + (fun _ => -x)`. Use extensionality with `w`. Simplify using `[sub_eq_add_neg]`. Rewrite using `[e, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-x) z)]`. Conclude with `L.order_weierstrassP z hz`.

Rewrite using `[L.order_weierstrassP z hz, meromorphicOrderAt_const] split_ifs`. Conclude with `WithTop.coe_lt_top _`. Evaluate the decidable proposition. Establish `e2 : f = (fun w => L.weierstrassP w - x)⁻¹` using `rfl`. Rewrite using `[e2, meromorphicOrderAt_inv, h1]`.

Evaluate the decidable proposition. Conclude with `(han z hz).meromorphicOrderAt_nonneg`. Take `⟨c, hc⟩` from `Formalism.L2.Th1.F.ellipticNoPole L f hmer hper hord`. Establish `hev : L.weierstrassP =ᶠ[𝓝[≠] 0] fun _ => x + c⁻¹` using `by filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz0 hz`. Establish `hzl : z ∉ L.lattice` using `fun h => hz ⟨h, hz0⟩`.

Establish `h1 : f z = c` using `hc z (han z hzl).continuousAt`. Establish `h1' : (L.weierstrassP z - x)⁻¹ = c` using `h1`. Rewrite using `[← h1', inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `meromorphicOrderAt_congr hev`.

Rewrite `h3` using `[L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const]`. Use `split_ifs at h3`. Conclude with `absurd h3 (WithTop.coe_ne_top)`. Conclude with `absurd h3 (by decide)`.
-/
theorem wp_onto (L : PeriodPair) (x : ℂ) : ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = x := by
  classical
  by_contra hne
  push Not at hne
  set f : ℂ → ℂ := fun z => (L.weierstrassP z - x)⁻¹ with hf
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    have h := L.meromorphic_weierstrassP z
    fun_prop
  have hper : Formalism.L2.Th1.F.IsPeriodic L f := by
    intro ω hω z
    show (L.weierstrassP (z + ω) - x)⁻¹ = (L.weierstrassP z - x)⁻¹
    rw [show L.weierstrassP (z + ω) = L.weierstrassP z from L.weierstrassP_add_coe z ⟨ω, hω⟩]
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ f z := by
    intro z hz
    have h1 : AnalyticAt ℂ L.weierstrassP z := L.analyticOnNhd_weierstrassP z hz
    have h2 : L.weierstrassP z - x ≠ 0 := sub_ne_zero.mpr (hne z hz)
    exact (h1.sub analyticAt_const).inv h2
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := by
    intro z
    by_cases hz : z ∈ L.lattice
    · have h1 : meromorphicOrderAt (fun w => L.weierstrassP w - x) z = -2 := by
        have e : (fun w => L.weierstrassP w - x) = L.weierstrassP + (fun _ => -x) := by
          ext w
          simp [sub_eq_add_neg]
        rw [e, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-x) z)]
        · exact L.order_weierstrassP z hz
        · rw [L.order_weierstrassP z hz, meromorphicOrderAt_const]
          split_ifs
          · exact WithTop.coe_lt_top _
          · decide
      have e2 : f = (fun w => L.weierstrassP w - x)⁻¹ := rfl
      rw [e2, meromorphicOrderAt_inv, h1]
      decide
    · exact (han z hz).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := Formalism.L2.Th1.F.ellipticNoPole L f hmer hper hord
  have hev : L.weierstrassP =ᶠ[𝓝[≠] 0] fun _ => x + c⁻¹ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz0 hz
    have hzl : z ∉ L.lattice := fun h => hz ⟨h, hz0⟩
    have h1 : f z = c := hc z (han z hzl).continuousAt
    have h1' : (L.weierstrassP z - x)⁻¹ = c := h1
    rw [← h1', inv_inv]
    ring
  have h3 := meromorphicOrderAt_congr hev
  rw [L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const] at h3
  split_ifs at h3
  · exact absurd h3 (WithTop.coe_ne_top)
  · exact absurd h3 (by decide)

/- English proof (translation)
Introduce `L x y hxy`. Take `⟨z, hz, hzx⟩` from `wp_onto L x`. Establish `hsq` using `L.derivWeierstrassP_sq z hz`. Rewrite `hsq` using `[hzx, ← hxy]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h` into its components or cases.

Conclude with `⟨z, hz, hzx, h⟩`. Use `⟨-z, ?_, by rw [L.weierstrassP_neg, hzx], by rw [L.derivWeierstrassP_neg, h, neg_neg]⟩` and prove the remaining obligations. Introduce `hm`. Conclude with `hz (by simpa using L.lattice.neg_mem hm)`.
-/
theorem pOnto : POnto := by
  intro L x y hxy
  obtain ⟨z, hz, hzx⟩ := wp_onto L x
  have hsq := L.derivWeierstrassP_sq z hz
  rw [hzx, ← hxy] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact ⟨z, hz, hzx, h⟩
  · refine ⟨-z, ?_, by rw [L.weierstrassP_neg, hzx], by rw [L.derivWeierstrassP_neg, h, neg_neg]⟩
    intro hm
    exact hz (by simpa using L.lattice.neg_mem hm)

end PI.GalTorsConj.W

end
