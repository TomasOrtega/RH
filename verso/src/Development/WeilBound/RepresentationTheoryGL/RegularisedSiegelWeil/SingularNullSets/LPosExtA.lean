import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Metrizable.Urysohn

noncomputable section

open scoped ComplexConjugate
open Set MeasureTheory

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def swAlg (A : Submodule ℂ (X → ℂ)) (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (K : Set X) : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {h | ∃ c : ℂ, ∃ a ∈ A, ∀ x : K, h x = c + a x}
  mul_mem' := by
    rintro h h' ⟨c, a, ha, hh⟩ ⟨c', a', ha', hh'⟩
    refine ⟨c * c', c • a' + c' • a + a * a', A.add_mem (A.add_mem (A.smul_mem _ ha') (A.smul_mem _ ha))
      (hmul _ ha _ ha'), fun x => ?_⟩
    simp only [ContinuousMap.mul_apply, hh, hh', Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  one_mem' := ⟨1, 0, A.zero_mem, fun x => by simp⟩
  add_mem' := by
    rintro h h' ⟨c, a, ha, hh⟩ ⟨c', a', ha', hh'⟩
    refine ⟨c + c', a + a', A.add_mem ha ha', fun x => ?_⟩
    simp only [ContinuousMap.add_apply, hh, hh', Pi.add_apply]
    ring
  zero_mem' := ⟨0, 0, A.zero_mem, fun x => by simp⟩
  algebraMap_mem' r := ⟨r, 0, A.zero_mem, fun x => by simp [Algebra.algebraMap_eq_smul_one]⟩
  star_mem' := by
    rintro h ⟨c, a, ha, hh⟩
    refine ⟨conj c, star a, hstar a ha, fun x => ?_⟩
    simp [ContinuousMap.star_apply, hh, Pi.star_apply]

/- English proof (translation)
Establish `: CompactSpace K` using `isCompact_iff_compactSpace.mp hK`. Use `set S := swAlg A hmul hstar K`. Establish `hS : S.SeparatesPoints`. Introduce `x y hxy`. Take `⟨f, hf, hfxy⟩` from `hsep x y (fun h => hxy (Subtype.ext h))`.

Set `F : C(K, ℂ)` to `⟨fun z => f z, (hc f hf).comp continuous_subtype_val⟩`. Conclude with `⟨F, ⟨F, ⟨0, f, hf, fun z => by simp [F]⟩, rfl⟩, hfxy⟩`. Establish `htop` using `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS`. Set `gK : C(K, ℂ)` to `⟨fun z => g z, hg.comp continuous_subtype_val⟩`. Establish `hgK : gK ∈ S.topologicalClosure` using `by rw [htop]; trivial`.

Rewrite `hgK` using `[← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, Metric.mem_closure_iff]`. Take `⟨p, hpS, hp⟩` from `hgK ε hε`. Take `⟨c, a, ha, hpa⟩` from `hpS`. Use `⟨c • b + b * a, A.add_mem (A.smul_mem _ hbA) (hmul _ hbA _ ha), fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ K`.

Establish `h1 : ‖p ⟨x, hx⟩ - gK ⟨x, hx⟩‖ ≤ ε`. Use `ContinuousMap.norm_coe_le_norm (p - gK) ⟨x, hx⟩` as an intermediate fact. Rewrite `hp` using `[dist_comm, dist_eq_norm]`. Conclude with `(this.trans hp.le)`. Establish `h2 : g x = b x * g x`.

Distinguish the cases in `h0 : g x = 0`. Simplify using `[h0]`. Simplify using `[hgb x h0]`. Establish `h3 : c • b x + b x * a x - g x = b x * (p ⟨x, hx⟩ - gK ⟨x, hx⟩)`. Rewrite using `[hpa ⟨x, hx⟩]`.

Simplify using `only [gK, ContinuousMap.coe_mk]`. Rewrite `*` using `[h2]`. Use `nth_rewrite 1 [h2]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply]`. Rewrite using `[h3, norm_mul, mul_comm ε]`. Conclude with `mul_le_mul_of_nonneg_left h1 (norm_nonneg _)`. Establish `hb` using `hbK x hx`. Establish `hg0 : g x = 0`.

Assume the negation of the conclusion as `h0`. Use `hgb x h0` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `zero_ne_one this`. Simplify using `[hb, hg0]`.
-/
theorem approx (A : Submodule ℂ (X → ℂ)) (hc : ∀ f ∈ A, Continuous f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y) {K : Set X} (hK : IsCompact K) {b : X → ℂ} (hbA : b ∈ A)
    (hbK : ∀ x ∉ K, b x = 0) {g : X → ℂ} (hg : Continuous g) (hgb : ∀ x, g x ≠ 0 → b x = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ h ∈ A, ∀ x, ‖h x - g x‖ ≤ ε * ‖b x‖ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set S := swAlg A hmul hstar K
  have hS : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfxy⟩ := hsep x y (fun h => hxy (Subtype.ext h))
    let F : C(K, ℂ) := ⟨fun z => f z, (hc f hf).comp continuous_subtype_val⟩
    exact ⟨F, ⟨F, ⟨0, f, hf, fun z => by simp [F]⟩, rfl⟩, hfxy⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  let gK : C(K, ℂ) := ⟨fun z => g z, hg.comp continuous_subtype_val⟩
  have hgK : gK ∈ S.topologicalClosure := by rw [htop]; trivial
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hgK
  obtain ⟨p, hpS, hp⟩ := hgK ε hε
  obtain ⟨c, a, ha, hpa⟩ := hpS
  refine ⟨c • b + b * a, A.add_mem (A.smul_mem _ hbA) (hmul _ hbA _ ha), fun x => ?_⟩
  by_cases hx : x ∈ K
  · have h1 : ‖p ⟨x, hx⟩ - gK ⟨x, hx⟩‖ ≤ ε := by
      have := ContinuousMap.norm_coe_le_norm (p - gK) ⟨x, hx⟩
      rw [dist_comm, dist_eq_norm] at hp
      exact (this.trans hp.le)
    have h2 : g x = b x * g x := by
      by_cases h0 : g x = 0
      · simp [h0]
      · simp [hgb x h0]
    have h3 : c • b x + b x * a x - g x = b x * (p ⟨x, hx⟩ - gK ⟨x, hx⟩) := by
      rw [hpa ⟨x, hx⟩]
      simp only [gK, ContinuousMap.coe_mk]
      rw [h2] at *
      nth_rewrite 1 [h2]
      simp only [smul_eq_mul]
      ring
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply]
    rw [h3, norm_mul, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  · have hb := hbK x hx
    have hg0 : g x = 0 := by
      by_contra h0
      have := hgb x h0
      rw [hb] at this
      exact zero_ne_one this
    simp [hb, hg0]

/- English proof (translation)
Establish `hC : 0 ≤ C` using `by have := h 1 one_pos; linarith [norm_nonneg d]`. Establish `: ∀ ε : ℝ, 0 < ε → dist d 0 ≤ ε`. Introduce `ε hε`. Rewrite using `[dist_zero_right]`. Use `(h (ε / (C + 1)) (by positivity)).trans ?_` and prove the remaining obligations.

Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `eq_of_forall_dist_le this`.
-/
theorem zero_of_le (d : ℂ) (C : ℝ) (h : ∀ ε : ℝ, 0 < ε → ‖d‖ ≤ ε * C) : d = 0 := by
  have hC : 0 ≤ C := by have := h 1 one_pos; linarith [norm_nonneg d]
  have : ∀ ε : ℝ, 0 < ε → dist d 0 ≤ ε := by
    intro ε hε
    rw [dist_zero_right]
    refine (h (ε / (C + 1)) (by positivity)).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  exact eq_of_forall_dist_le this

end PositivityTheory.Rg.Rsw.L.LPosExt
