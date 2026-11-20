import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

open scoped Pointwise

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]

omit [IsScalarTower S F Ω] in

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Rewrite using `[map_X]`. Conclude with `Submonoid.subset_closure ⟨i, hi, rfl⟩`.

Consider the case `one => rw [map_one]`. Conclude with `one_mem _`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
theorem map_mem_monos {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S F) s ∈ monos (S := F) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/- English proof (translation)
Take `⟨f, s, e, hs, hf, hse, rfl⟩` from `ha`. Conclude with `⟨map (algebraMap S F) f, map (algebraMap S F) s, e, map_mem_monos hs, hf.map _, hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩`.
-/
theorem mem_chartRing_extend {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing F x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S F) f, map (algebraMap S F) s, e, map_mem_monos hs, hf.map _, hse.map _,
    by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

/- English proof (translation)
Establish `: a • y = (⟨(a : Ω), mem_chartRing_extend a.2⟩ : chartRing F x I) • y`. Rewrite using `[chartRing_smul_def, chartRing_smul_def]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem smul_mem_span_extend {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing F x I) P) : a • y ∈ Submodule.span (chartRing F x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_extend a.2⟩ : chartRing F x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations. Use `Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (chartRing F x I) P) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce `z hz`. Conclude with `Submodule.subset_span hz`.

Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `a z _ hz`. Conclude with `smul_mem_span_extend P a hz`.

Conclude with `Submodule.span_mono Submodule.subset_span`.
-/
theorem span_extend_span (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing F x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing F x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing F x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_extend P a hz
  · exact Submodule.span_mono Submodule.subset_span

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1`. Express the relevant statement in the definitionally equal form `Submodule.span (chartRing F x I) (twistMod S x c I : Set Ω) = twistMod F x c I`. Rewrite using `[twistMod_eq_span c I hi, twistMod_eq_span c I hi, span_extend_span]`.
-/
theorem SubSystem.extend_twistSys (c : ℤ) : (twistSys S x c).extend F = twistSys F x c := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  change Submodule.span (chartRing F x I) (twistMod S x c I : Set Ω) = twistMod F x c I
  rw [twistMod_eq_span c I hi, twistMod_eq_span c I hi, span_extend_span]

omit [Algebra S F] [IsScalarTower S F Ω] in

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line]`. Express the relevant statement in the definitionally equal form `Submodule.span (chartRing F x I) ((Q.twist R).sub I : Set Ω) = Submodule.span (chartRing F x I) (R.sub I : Set Ω) * Submodule.span (chartRing F x I) (Q.sub I : Set Ω)`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, Submodule.span_mul_span]`. Apply `le_antisymm` to reduce the goal to its premises.

Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations. Use `Submodule.mul_induction_on (C := fun y => y ∈ Submodule.span (chartRing F x I) ((R.sub I : Set Ω) * (Q.sub I : Set Ω))) hy ?_ ?_` and prove the remaining obligations. Introduce `r hr q hq`. Conclude with `Submodule.subset_span (Set.mul_mem_mul hr hq)`. Introduce `a b ha hb`.

Conclude with `Submodule.add_mem _ ha hb`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, q, hq, rfl⟩`. Conclude with `Submodule.subset_span (Submodule.mul_mem_mul hr hq)`.
-/
theorem SubSystem.extend_twist (Q R : SubSystem S x Ω) :
    (Q.twist R).extend F = (Q.extend F).twist (R.extend F) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change Submodule.span (chartRing F x I) ((Q.twist R).sub I : Set Ω) =
    Submodule.span (chartRing F x I) (R.sub I : Set Ω) * Submodule.span (chartRing F x I) (Q.sub I : Set Ω)
  rw [SubSystem.twist_sub_eq_mul_of_line, Submodule.span_mul_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.mul_induction_on (C := fun y =>
      y ∈ Submodule.span (chartRing F x I) ((R.sub I : Set Ω) * (Q.sub I : Set Ω))) hy ?_ ?_
    · intro r hr q hq
      exact Submodule.subset_span (Set.mul_mem_mul hr hq)
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, hr, q, hq, rfl⟩
    exact Submodule.subset_span (Submodule.mul_mem_mul hr hq)

end

end GroundTheory.Heights₂.Heights.Kleiman
