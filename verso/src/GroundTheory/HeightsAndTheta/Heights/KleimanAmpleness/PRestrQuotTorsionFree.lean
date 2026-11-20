import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsRestrQuotTorsionFree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFibreSectionsFlat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Chart

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => exact hz`. Consider the case `zero`. Conclude with `⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨f, m, e, hf, hm, hfe, hme, rfl⟩` from `ha`. Take `⟨f', m', e', hf', hm', hfe', hme', rfl⟩` from `hb`. Use `⟨f * m' + m * f', m * m', e + e', J.add_mem (J.mul_mem_right _ hf) (J.mul_mem_left _ hf'), mul_mem hm hm', (hfe.mul hme').add (hme.mul hfe'), hme.mul hme', ?_⟩` and prove the remaining obligations. Rewrite using `[div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]`. Simplify using `only [map_add, map_mul]`.

Consider the case `smul a z _ hz`. Take `⟨f, m, e, hf, hm, hfe, hme, rfl⟩` from `hz`. Take `⟨g, n, d, hn, hg, hnd, ha⟩` from `a.2`. Use `⟨g * f, n * m, d + e, J.mul_mem_left _ hf, mul_mem hn hm, hg.mul hfe, hnd.mul hme, ?_⟩` and prove the remaining obligations. Rewrite using `[chartRing_smul_def, ha, map_mul, map_mul, div_mul_div_comm]`.
-/
theorem exists_eq_div_of_mem_idealMod {J : Ideal (Poly S N)} {I : Chart x} {z : Ω}
    (hz : z ∈ idealMod J I) :
    ∃ (f m : Poly S N) (e : ℕ), f ∈ J ∧ m ∈ monos I.1 ∧ f.IsHomogeneous e ∧
      m.IsHomogeneous e ∧ z = aeval x f / aeval x m := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨f, m, e, hf, hm, hfe, hme, rfl⟩ := ha
    obtain ⟨f', m', e', hf', hm', hfe', hme', rfl⟩ := hb
    refine ⟨f * m' + m * f', m * m', e + e', J.add_mem (J.mul_mem_right _ hf) (J.mul_mem_left _ hf'),
      mul_mem hm hm', (hfe.mul hme').add (hme.mul hfe'), hme.mul hme', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]
    simp only [map_add, map_mul]
  | smul a z _ hz =>
    obtain ⟨f, m, e, hf, hm, hfe, hme, rfl⟩ := hz
    obtain ⟨g, n, d, hn, hg, hnd, ha⟩ := a.2
    refine ⟨g * f, n * m, d + e, J.mul_mem_left _ hf, mul_mem hn hm, hg.mul hfe, hnd.mul hme, ?_⟩
    rw [chartRing_smul_def, ha, map_mul, map_mul, div_mul_div_comm]

/- English proof (translation)
Take `⟨g, n, d, hn, hg, hnd, rfl⟩` from `ha`. Take `⟨f, m, e, hf, hm, hfe, hme, hfm⟩` from `exists_eq_div_of_mem_idealMod hsa`. Establish `hn0` using `eval_ne_zero_of_mem_monos I hn`. Establish `hm0` using `eval_ne_zero_of_mem_monos I hm`. Establish `h1 : (C s * (g * m)).IsHomogeneous (d + e)`.

Simplify using `using (isHomogeneous_C (Fin (N + 1)) s).mul (hg.mul hme)`. Establish `h2 : (f * n).IsHomogeneous (d + e)`. Establish `h` using `hfe.mul hnd`. Rewrite `h` using `[add_comm e d]`. Then use the resulting hypothesis. Establish `hker : C s * (g * m) - f * n ∈ qq`.

Use `hle _ (d + e) (by rw [sub_eq_add_neg]; exact h1.add h2.neg) ?_` and prove the remaining obligations. Rewrite `hfm` using `[mul_div_assoc', div_eq_div_iff hn0 hm0]`. Simplify using `only [map_sub, map_mul, aeval_C]`. Take the linear combination `hfm`. Establish `h3 : C s * (g * m) ∈ qq`.

Establish `h4 : C s * (g * m) = (C s * (g * m) - f * n) + f * n` using `by ring`. Rewrite using `[h4]`. Conclude with `qq.add_mem hker (qq.mul_mem_right n hf)`. Establish `hgm : g * m ∈ qq` using `(hq.mem_or_mem h3).resolve_left hs`. Conclude with `Submodule.subset_span ⟨g * m, n * m, d + e, hgm, mul_mem hn hm, hg.mul hme, hnd.mul hme, by`.

Rewrite using `[map_mul, map_mul, mul_div_mul_right _ _ hm0]⟩`.
-/
theorem mem_idealMod_of_algebraMap_mul_mem {qq : Ideal (Poly S N)} (hq : qq.IsPrime)
    (hle : ∀ (p : Poly S N) (d : ℕ), p.IsHomogeneous d → aeval x p = 0 → p ∈ qq) (I : Chart x) {s : S}
    (hs : (C s : Poly S N) ∉ qq) {a : Ω} (ha : a ∈ chartRing S x I)
    (hsa : algebraMap S Ω s * a ∈ idealMod qq I) : a ∈ idealMod qq I := by
  obtain ⟨g, n, d, hn, hg, hnd, rfl⟩ := ha
  obtain ⟨f, m, e, hf, hm, hfe, hme, hfm⟩ := exists_eq_div_of_mem_idealMod hsa
  have hn0 := eval_ne_zero_of_mem_monos I hn
  have hm0 := eval_ne_zero_of_mem_monos I hm

  have h1 : (C s * (g * m)).IsHomogeneous (d + e) := by
    simpa using (isHomogeneous_C (Fin (N + 1)) s).mul (hg.mul hme)
  have h2 : (f * n).IsHomogeneous (d + e) := by
    have h := hfe.mul hnd
    rwa [add_comm e d] at h
  have hker : C s * (g * m) - f * n ∈ qq := by
    refine hle _ (d + e) (by rw [sub_eq_add_neg]; exact h1.add h2.neg) ?_
    rw [mul_div_assoc', div_eq_div_iff hn0 hm0] at hfm
    simp only [map_sub, map_mul, aeval_C]
    linear_combination hfm
  have h3 : C s * (g * m) ∈ qq := by
    have h4 : C s * (g * m) = (C s * (g * m) - f * n) + f * n := by ring
    rw [h4]
    exact qq.add_mem hker (qq.mul_mem_right n hf)
  have hgm : g * m ∈ qq := (hq.mem_or_mem h3).resolve_left hs
  exact Submodule.subset_span ⟨g * m, n * m, d + e, hgm, mul_mem hn hm, hg.mul hme, hnd.mul hme, by
    rw [map_mul, map_mul, mul_div_mul_right _ _ hm0]⟩

end Chart

/- English proof (translation)
Introduce `S _ _ F _ _ _ Ω _ _ _ _ N x L qq hq hconst e hsub`. Establish `hle : ∀ (p : Poly S N) (d : ℕ), p.IsHomogeneous d → aeval x p = 0 → p ∈ qq`. Introduce `p d hp hp0`. Use `mem_of_map_mem_map (F := F) hq hconst (hsub.le ?_)` and prove the remaining obligations. Rewrite using `[mem_primeOf_of_isHomogeneous x (hp.map _), MvPolynomial.aeval_map_algebraMap]`.

Conclude with `hp0`. Rewrite using `[Module.isTorsionFree_iff_smul_eq_zero]`. Introduce `s t hst`. Distinguish the cases in `hs : s = 0`. Conclude with `Or.inl hs`.

Use `right`. Establish `hsC : (C s : Poly S N) ∉ qq` using `fun h => hs (hconst s h)`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ t`. Rewrite `hst` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Establish `hmL : ∀ I, (m : Ω) ∈ L.sub I`. Use `m.2` as an intermediate fact. Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at this`. Conclude with `this`. Establish `hst' : ∀ I, algebraMap S Ω s * (m : Ω) ∈ idealMod qq I * L.sub I`.

Introduce `I`. Establish `h` using `(Submodule.mem_iInf _).mp (Submodule.mem_comap.mp hst) I`. Rewrite `h` using `[Submodule.restrictScalars_mem, SubSystem.twist_sub_eq_mul_of_line]`. Rewrite using `[← Algebra.smul_def]`. Conclude with `h`.

Use `Submodule.mem_comap.mpr ((Submodule.mem_iInf _).mpr fun I => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, SubSystem.twist_sub_eq_mul_of_line]`. Take `⟨L', hL'⟩` from `L.invertible I`. Establish `key : Submodule.span (chartRing S x I) {(m : Ω)} * L' ≤ idealMod qq I`. Introduce `z hz`.

Take `⟨b, hb, rfl⟩` from `Submodule.mem_span_singleton_mul.mp hz`. Establish `hmb : (m : Ω) * b ∈ (1 : Submodule (chartRing S x I) Ω)` using `hL' ▸ Submodule.mul_mem_mul (hmL I) hb`. Take `⟨a, ha⟩` from `Submodule.mem_one.mp hmb`. Use `mem_idealMod_of_algebraMap_mul_mem hq hle I hsC (by rw [← ha]; exact a.2) ?_` and prove the remaining obligations. Establish `h5 : algebraMap S Ω s * (m : Ω) * b ∈ idealMod qq I * L.sub I * L'`.

Conclude with `Submodule.mul_mem_mul (hst' I) hb`. Rewrite `h5` using `[mul_assoc (idealMod qq I), hL', mul_one, mul_assoc]`. Conclude with `h5`. Establish `hspan : Submodule.span (chartRing S x I) {(m : Ω)} ≤ idealMod qq I * L.sub I`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hspan (Submodule.mem_span_singleton_self _)`.
-/
theorem RestrQuotTorsionFree.proof : RestrQuotTorsionFree.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x L qq hq hconst e hsub

  have hle : ∀ (p : Poly S N) (d : ℕ), p.IsHomogeneous d → aeval x p = 0 → p ∈ qq := by
    intro p d hp hp0
    refine mem_of_map_mem_map (F := F) hq hconst (hsub.le ?_)
    rw [mem_primeOf_of_isHomogeneous x (hp.map _), MvPolynomial.aeval_map_algebraMap]
    exact hp0
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro s t hst
  by_cases hs : s = 0
  · exact Or.inl hs
  right
  have hsC : (C s : Poly S N) ∉ qq := fun h => hs (hconst s h)
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hst
  rw [Submodule.Quotient.mk_eq_zero]
  have hmL : ∀ I, (m : Ω) ∈ L.sub I := by
    have := m.2
    simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at this
    exact this
  have hst' : ∀ I, algebraMap S Ω s * (m : Ω) ∈ idealMod qq I * L.sub I := by
    intro I
    have h := (Submodule.mem_iInf _).mp (Submodule.mem_comap.mp hst) I
    rw [Submodule.restrictScalars_mem, SubSystem.twist_sub_eq_mul_of_line] at h
    rw [← Algebra.smul_def]
    exact h
  refine Submodule.mem_comap.mpr ((Submodule.mem_iInf _).mpr fun I => ?_)
  rw [Submodule.restrictScalars_mem, SubSystem.twist_sub_eq_mul_of_line]
  obtain ⟨L', hL'⟩ := L.invertible I
  have key : Submodule.span (chartRing S x I) {(m : Ω)} * L' ≤ idealMod qq I := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    have hmb : (m : Ω) * b ∈ (1 : Submodule (chartRing S x I) Ω) := hL' ▸ Submodule.mul_mem_mul (hmL I) hb
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hmb
    refine mem_idealMod_of_algebraMap_mul_mem hq hle I hsC (by rw [← ha]; exact a.2) ?_
    have h5 : algebraMap S Ω s * (m : Ω) * b ∈ idealMod qq I * L.sub I * L' := by
      exact Submodule.mul_mem_mul (hst' I) hb
    rw [mul_assoc (idealMod qq I), hL', mul_one, mul_assoc] at h5
    exact h5
  have hspan : Submodule.span (chartRing S x I) {(m : Ω)} ≤ idealMod qq I * L.sub I := by
    calc Submodule.span (chartRing S x I) {(m : Ω)}
        = Submodule.span (chartRing S x I) {(m : Ω)} * (L' * L.sub I) := by rw [mul_comm L', hL', mul_one]
      _ = Submodule.span (chartRing S x I) {(m : Ω)} * L' * L.sub I := (mul_assoc _ _ _).symm
      _ ≤ idealMod qq I * L.sub I := mul_le_mul' key le_rfl
  exact hspan (Submodule.mem_span_singleton_self _)

end

end GroundTheory.Heights₂.Heights.Kleiman
