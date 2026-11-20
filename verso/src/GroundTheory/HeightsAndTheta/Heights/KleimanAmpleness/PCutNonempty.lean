import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutOneGeneratorSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
Rewrite using `[← sum_homogeneousComponent p]`. Rewrite using `[map_sum, AddSubmonoidClass.coe_finsetSum]`. Use `Submodule.sum_mem _ fun d _ => Submodule.subset_span ?_` and prove the remaining obligations. Conclude with `⟨homogeneousComponent d p, X j ^ d, d, hh p hp d, pow_mem (X_mem_monos (Finset.mem_singleton_self j)) d, homogeneousComponent_isHomogeneous d p, isHomogeneous_X_pow j d, coe_aeval_ratio' hj (homogeneousComponent_isHomogeneous d p)⟩`.
-/
theorem coe_aeval_ratio_mem_idealMod {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) {j : Fin (N + 1)} (hj : x j ≠ 0)
    {p : Poly k N} (hp : p ∈ pp) :
    ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) ∈
      idealMod (x := x) pp (singleChart hj) := by
  rw [← sum_homogeneousComponent p]
  rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun d _ => Submodule.subset_span ?_
  exact ⟨homogeneousComponent d p, X j ^ d, d, hh p hp d,
    pow_mem (X_mem_monos (Finset.mem_singleton_self j)) d, homogeneousComponent_isHomogeneous d p,
    isHomogeneous_X_pow j d, coe_aeval_ratio' hj (homogeneousComponent_isHomogeneous d p)⟩

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨c, hfc, hf⟩` from `hf`. Take `⟨o, ho, he⟩` from `hf (singleChart hj) δ hδ`. Rewrite `ho` using `[twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]`.

Take `⟨b, rfl⟩` from `ho`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_aeval_ratio hj hfc, chartRing_smul_def, div_mul_eq_mul_div, he, chartRing_smul_def, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add, Subalgebra.coe_add, add_mul]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul g z _ hz`.

Rewrite using `[smul_eq_mul, map_mul, Subalgebra.coe_mul, mul_assoc]`. Conclude with `Submodule.smul_mem _ (aeval (ratio (S := k) hj) g) hz`.
-/
theorem coe_aeval_ratio_mul_mem_span {L : SubSystem k x Ω} {s : Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    {z : Poly k N} (hz : z ∈ zeroIdeal L s) {δ : Ω} (hδ : δ ∈ L.sub (singleChart hj)) :
    ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * δ ∈
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hfc, hf⟩ := hf
    obtain ⟨o, ho, he⟩ := hf (singleChart hj) δ hδ
    rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    rw [Submodule.mem_span_singleton]
    refine ⟨b, ?_⟩
    rw [coe_aeval_ratio hj hfc, chartRing_smul_def, div_mul_eq_mul_div, he, chartRing_smul_def,
      zpow_natCast]
    field_simp
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, Subalgebra.coe_add, add_mul]
    exact Submodule.add_mem _ ha hb
  | smul g z _ hz =>
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, mul_assoc]
    exact Submodule.smul_mem _ (aeval (ratio (S := k) hj) g) hz

/- English proof (translation)
Establish `hrad : (X j : Poly k N) ∈ (pp ⊔ zeroIdeal L.toSubSystem s).radical`. Rewrite using `[← Ideal.sInf_minimalPrimes]`. Conclude with `Submodule.mem_sInf.mpr fun qq hq => hmin qq hq j`. Take `⟨m, hm⟩` from `hrad`. Take `⟨p, hp, z, hz, hpz⟩` from `Submodule.mem_sup.mp hm`.

Introduce `ℓ hℓ`. Establish `h1 : ((aeval (ratio (S` using `k) hj) ((X j : Poly k N) ^ m) : chartRing k x (singleChart hj)) : Ω) = 1 := by`. Rewrite using `[map_pow, aeval_X, SubmonoidClass.coe_pow]`. Express the relevant statement in the definitionally equal form `(x j / x j) ^ m = 1`. Rewrite using `[div_self hj, one_pow]`.

Establish `hsplit : ℓ = ((aeval (ratio (S` using `k) hj) p : chartRing k x (singleChart hj)) : Ω) * ℓ + ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * ℓ := by`. Rewrite using `[← add_mul, ← Subalgebra.coe_add, ← map_add, hpz, h1, one_mul]`. Rewrite using `[hsplit]`. Use `Submodule.add_mem_sup (Submodule.subset_span ?_) (coe_aeval_ratio_mul_mem_span hj hz hℓ)` and prove the remaining obligations. Conclude with `⟨_, coe_aeval_ratio_mem_idealMod hh hj hp, ℓ, hℓ, rfl⟩`.
-/
theorem sub_le_twist_sup_span {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) (L : LineBundle k x) (s : Ω)
    (hmin : ∀ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∀ i, (X i : Poly k N) ∈ qq)
    (j : Fin (N + 1)) (hj : x j ≠ 0) :
    L.sub (singleChart hj) ≤ (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  have hrad : (X j : Poly k N) ∈ (pp ⊔ zeroIdeal L.toSubSystem s).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr fun qq hq => hmin qq hq j
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hm
  intro ℓ hℓ
  have h1 : ((aeval (ratio (S := k) hj) ((X j : Poly k N) ^ m) : chartRing k x (singleChart hj)) : Ω) = 1 := by
    rw [map_pow, aeval_X, SubmonoidClass.coe_pow]
    change (x j / x j) ^ m = 1
    rw [div_self hj, one_pow]
  have hsplit : ℓ = ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) * ℓ +
      ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * ℓ := by
    rw [← add_mul, ← Subalgebra.coe_add, ← map_add, hpz, h1, one_mul]
  rw [hsplit]
  refine Submodule.add_mem_sup (Submodule.subset_span ?_) (coe_aeval_ratio_mul_mem_span hj hz hℓ)
  exact ⟨_, coe_aeval_ratio_mem_idealMod hh hj hp, ℓ, hℓ, rfl⟩

end Chart

/- English proof (translation)
Introduce `k _ Ω _ _ N x n pp L s hW hL hs _`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Conclude with `hO k Ω N x n pp L s hW hL hs (sub_le_twist_sup_span hW.homog L s hne)`.
-/
theorem CutNonempty.proof (hO : CutOneGenerator.Statement.{u, w}) : CutNonempty.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs _
  by_contra hne
  push Not at hne
  exact hO k Ω N x n pp L s hW hL hs (sub_le_twist_sup_span hW.homog L s hne)

end

end GroundTheory.Heights₂.Heights.Kleiman
